//! The decision export: a lowered bundle's whole policy set, each of its traces, and the verdict
//! the crate's `Authorizer` gives at every event of each trace.
//!
//! A rule is written from its Cedar form (the policy JSON, Cedar's EST) as a policy of the
//! specification, with each hoisted temporal field `context.<id>` put back as the leaf
//! `temporal φ`, and each hoisted provider field `context.providers.<id>` as the leaf
//! `provider c`. The temporal leaf is the authored one after pin injection, before the
//! relativization rewrite; the specification injects pins itself, and injecting twice is
//! injecting once (`Dogwood.Thm.sat_injectPins_idem`). A trace event is written as a timepoint of
//! the specification, its values as Cedar values.
//!
//! For a bundle with information providers, the export also records, at each decision event,
//! the provider outputs the crate computed: the `context.providers` record its policy engine
//! received. The replay reads each decision's provider leaves off that record. At a decision event
//! where the crate failed closed before its policy engine ran (a provider that failed, among
//! other causes), there is no record.
//!
//! A trace's timestamps are exported as recorded, in seconds; the crate takes them as given. The
//! conformance run reads each as the clock reading of its event, in nanoseconds, and stamps the
//! trace as the specification's authorizer does (`Dogwood.Spec.Trace.stamp`), so a trace whose
//! times do not strictly increase is decided over different times by the two.
//!
//! The export also records whether the crate ingested each event into its history: it rejects
//! an event that does not conform to the event schema, as the specification's ingestion does.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::Path;
use std::sync::{Arc, Mutex};

use dogwood_language::temporal_ast::Condition;
use dogwood_language::{
    Arg, AuthorizationDecision, AuthorizationRequest, Authorizer, CedarPolicyEngine, Decision,
    Event, EventSignature, LoweredPolicySet, PartitionKey, PolicyEngine, ProviderField, Rejection,
    TemporalBindings, TemporalEngine, TemporalField, Value, parse_trace,
};
use serde_json::{Value as Json, json};

use crate::{EngineFactory, ctor, formula};

type Result<T> = std::result::Result<T, String>;

/// The traces of a bundle directory: `trace.log`, or `trace_*.log` in name order.
pub fn trace_files(dir: &Path) -> Vec<(String, String)> {
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .map(|rd| rd.filter_map(|e| e.ok().map(|e| e.path())).collect())
        .unwrap_or_default();
    paths.retain(|p| {
        p.extension().is_some_and(|e| e == "log")
            && p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n == "trace.log" || n.starts_with("trace_"))
    });
    paths.sort();
    paths
        .into_iter()
        .filter_map(|p| {
            let name = p.file_name()?.to_string_lossy().to_string();
            Some((name, std::fs::read_to_string(&p).ok()?))
        })
        .collect()
}

/// The rules of a lowered bundle, as `Dogwood.Spec.Policy`s, and its hoisted provider fields, as
/// `[id, Dogwood.Spec.Provider.Call]` pairs.
pub fn policies(lowered: &LoweredPolicySet) -> Result<(Vec<Json>, Vec<Json>)> {
    let temporal: HashMap<String, &Condition> = lowered
        .nonrelativized_temporal_fields()
        .map(|f| (f.id.as_str().to_string(), &f.condition.condition))
        .collect();
    let mut providers: HashMap<String, Json> = HashMap::new();
    let mut provider_fields = Vec::new();
    for f in lowered.provider_fields() {
        let c = call(f)?;
        providers.insert(f.id.to_string(), c.clone());
        provider_fields.push(json!([f.id.to_string(), c]));
    }
    let mut policies = Vec::new();
    for rule in lowered.rules() {
        let id = cedar_policy::PolicyId::new(&rule.cedar_policy_id);
        let policy = lowered
            .as_cedar()
            .policy(&id)
            .ok_or_else(|| format!("rule {} is not in the lowered set", rule.rule_index))?;
        let json = policy.to_json().map_err(|e| format!("rule {}: {e}", rule.rule_index))?;
        policies.push(
            Gen { temporal: &temporal, providers: &providers }
                .policy(&rule.cedar_policy_id, &json)
                .map_err(|e| format!("rule {}: {e}", rule.rule_index))?,
        );
    }
    Ok((policies, provider_fields))
}

/// A lowered rule, from its Cedar policy JSON, as a `Dogwood.Spec.Policy` that keeps the crate's
/// names: each hoisted field stays the attribute access `context.<id>` or
/// `context.providers.<id>`.
pub fn crate_named_policy(id: &str, est: &Json) -> Result<Json> {
    Gen { temporal: &HashMap::new(), providers: &HashMap::new() }.policy(id, est)
}

/// Export the decisions of a bundle, as a `Dogwood.Conformance.Decisions`: each trace and the
/// crate's verdicts over it. `fresh` lowers the bundle again (an `Authorizer` consumes its policy
/// set, and each trace starts from an empty history). With `engine`, each trace's `Authorizer`
/// evaluates the temporal leaves with a fresh engine from it, partitioned.
pub fn export(
    lowered: &LoweredPolicySet,
    fresh: &dyn Fn() -> LoweredPolicySet,
    traces: &[(String, String)],
    bundle: &str,
    engine: Option<&EngineFactory>,
) -> Result<Json> {
    let record = lowered.provider_fields().next().is_some();
    let mut out = Vec::new();
    for (name, log) in traces {
        let events = parse_trace(log).map_err(|e| format!("{name}: {e}"))?;
        let points = events
            .iter()
            .map(timepoint)
            .collect::<Result<Vec<_>>>()
            .map_err(|e| format!("{name}: {e}"))?;
        let all: Vec<&Event> = events.iter().collect();
        let label = format!("{bundle}/{name}");
        let whole =
            run(fresh(), &all, record, engine, &label).map_err(|e| format!("{name}: {e}"))?;
        out.push(json!({
            "name": name, "trace": points, "verdicts": whole.verdicts,
            "crateErrors": whole.errors, "providerOutputs": whole.outputs,
            "ingested": whole.ingested,
        }));
    }
    Ok(json!({"traces": out}))
}

/// The crate's verdicts over `events`, from a fresh `Authorizer`, and, when `record` holds, the
/// provider outputs its policy engine received at each event.
struct Run {
    verdicts: Vec<Option<bool>>,
    /// The errors the crate's diagnostics report at each event: a decision with errors failed,
    /// in part or whole.
    errors: Vec<Vec<String>>,
    outputs: Option<Vec<Json>>,
    /// Whether the crate ingested each event into its history. The crate rejects a history event
    /// that does not conform to the event schema (`Authorizer::submit`), and does not ingest a
    /// decision event that does not conform either: it fails that decision closed, with a
    /// `nonconforming decision event` error.
    ingested: Vec<bool>,
}

fn run(
    lowered: LoweredPolicySet,
    events: &[&Event],
    record: bool,
    temporal: Option<&EngineFactory>,
    label: &str,
) -> Result<Run> {
    let seen: Arc<Mutex<Option<Result<Json>>>> = Arc::new(Mutex::new(None));
    let engine = Recorder { inner: CedarPolicyEngine::new(), seen: seen.clone() };
    let builder = match temporal {
        Some(make) => {
            let supplied = Supplied(make(&lowered, label));
            Authorizer::builder(lowered)
                .temporal_engine(supplied)
                .partition_temporal()
        }
        None => Authorizer::builder(lowered),
    };
    let mut authorizer = builder
        .policy_engine(engine)
        .build()
        .map_err(|e| format!("authorizer: {e}"))?;
    let mut verdicts = Vec::new();
    let mut errors = Vec::new();
    let mut outputs = Vec::new();
    let mut ingested = Vec::new();
    for event in events {
        *seen.lock().expect("the recorder's lock") = None;
        let (response, rejected) = match authorizer.submit(event) {
            Ok(response) => (response, false),
            Err(_) => (None, true),
        };
        let event_errors: Vec<String> = response
            .as_ref()
            .map(|r| r.diagnostics().errors().map(str::to_string).collect())
            .unwrap_or_default();
        ingested.push(
            !rejected
                && !event_errors.iter().any(|e| e.starts_with("nonconforming decision event:")),
        );
        verdicts.push(response.as_ref().map(|r| r.decision() == Decision::Allow));
        errors.push(event_errors);
        outputs.push(match seen.lock().expect("the recorder's lock").take() {
            Some(record) => record?,
            None => Json::Null,
        });
    }
    Ok(Run { verdicts, errors, outputs: record.then_some(outputs), ingested })
}

/// A temporal engine an [`EngineFactory`] made, as `AuthorizerBuilder::temporal_engine` takes
/// one: every method is the engine's own.
struct Supplied(Box<dyn TemporalEngine>);

impl TemporalEngine for Supplied {
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        schema: &cedar_policy::Schema,
        events: &[EventSignature],
    ) -> std::result::Result<(), dogwood_language::Error> {
        self.0.prepare(leaves, schema, events)
    }

    fn observe(&mut self, event: &Event) {
        self.0.observe(event)
    }

    fn try_observe(&mut self, event: &Event) -> std::result::Result<(), Rejection> {
        self.0.try_observe(event)
    }

    fn set_generation(&mut self, generation: u64) {
        self.0.set_generation(generation)
    }

    fn evaluate(&mut self) -> std::result::Result<TemporalBindings, String> {
        self.0.evaluate()
    }

    fn supports_partitioning(&self) -> bool {
        self.0.supports_partitioning()
    }

    fn set_partition_keys(&mut self, keys: &[PartitionKey]) {
        self.0.set_partition_keys(keys)
    }
}

/// The built-in policy engine, recording the `context.providers` record of each request it
/// decides.
struct Recorder {
    inner: CedarPolicyEngine,
    seen: Arc<Mutex<Option<Result<Json>>>>,
}

impl PolicyEngine for Recorder {
    fn prepare(
        &mut self,
        policies: &cedar_policy::PolicySet,
        schema: &cedar_policy::Schema,
    ) -> std::result::Result<(), dogwood_language::Error> {
        self.inner.prepare(policies, schema)
    }

    fn is_authorized(&self, request: AuthorizationRequest<'_>) -> AuthorizationDecision {
        let providers = request
            .request
            .context()
            .and_then(|c| c.get("providers"));
        let record = match providers {
            Some(cedar_policy::EvalResult::Record(r)) => r
                .iter()
                .map(|(k, v)| Ok(json!([k, eval_value(v)?])))
                .collect::<Result<Vec<_>>>()
                .map(Json::Array),
            Some(other) => Err(format!("`context.providers` is not a record: {other:?}")),
            None => Ok(json!([])),
        };
        *self.seen.lock().expect("the recorder's lock") = Some(record);
        self.inner.is_authorized(request)
    }
}

/// A Cedar value of a request context, as a value of the specification.
fn eval_value(v: &cedar_policy::EvalResult) -> Result<Json> {
    use cedar_policy::EvalResult as E;
    Ok(match v {
        E::Bool(b) => json!(b),
        E::Long(i) => json!(i),
        E::String(s) => json!(s),
        E::EntityUid(u) => json!({"entity": cedar_uid(u)?}),
        E::Set(s) => json!({"set": s.iter().map(eval_value).collect::<Result<Vec<_>>>()?}),
        E::Record(r) => json!({"record": r
            .iter()
            .map(|(k, v)| Ok(json!([k, eval_value(v)?])))
            .collect::<Result<Vec<_>>>()?}),
        E::ExtensionValue(x) => match x
            .strip_prefix("decimal(\"")
            .and_then(|t| t.strip_suffix("\")"))
        {
            Some(text) => json!({"decimal": text}),
            None => return Err(format!("provider output extension value `{x}`")),
        },
    })
}

// ─── Provider invocations ────────────────────────────────────────────────

/// A provider field's invocation and output-method chain, as a `Dogwood.Spec.Provider.Call`.
fn call(f: &ProviderField) -> Result<Json> {
    let (id, path) = f
        .invocation
        .function
        .split_last()
        .ok_or("a provider invocation without a name")?;
    let methods = f
        .methods
        .iter()
        .map(|m| {
            Ok(json!({"name": m.name, "args": m.args.iter().map(arg).collect::<Result<Vec<_>>>()?}))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(json!({
        "function": {"id": id, "path": path},
        "args": f.invocation.args.iter().map(arg).collect::<Result<Vec<_>>>()?,
        "methods": methods,
    }))
}

/// A provider argument, as a `Dogwood.Spec.Provider.Arg`. A field path's first segment is its
/// root: `context`, `principal`, or `resource`.
fn arg(a: &Arg) -> Result<Json> {
    Ok(match a {
        Arg::Field(path) => match path.split_first() {
            Some((root, rest)) if root == "context" => ctor("context", json!({"path": rest})),
            Some((root, rest)) if root == "principal" || root == "resource" => {
                ctor("scope", json!({"root": root, "path": rest}))
            }
            _ => return Err(format!("provider argument path {path:?}")),
        },
        Arg::String(s) => ctor("string", json!({"s": s})),
        Arg::Integer(i) => ctor("long", json!({"i": i})),
        Arg::Decimal(t) => ctor("decimal", json!({"text": t})),
        Arg::Bool(b) => ctor("bool", json!({"b": b})),
        Arg::Set(items) => ctor("set", json!({"items": items.iter().map(arg).collect::<Result<Vec<_>>>()?})),
    })
}

// ─── Entities ────────────────────────────────────────────────────────────

fn uid_of(ty: &str, eid: &str) -> Result<Json> {
    let path: Vec<String> = ty.split("::").map(str::to_string).collect();
    crate::uid(&path, eid)
}

fn cedar_uid(u: &cedar_policy::EntityUid) -> Result<Json> {
    uid_of(&u.type_name().to_string(), u.id().unescaped())
}

/// The data of an entity, without tags.
fn entity_data(attrs: Json, ancestors: Vec<Json>) -> Json {
    json!({"attrs": attrs, "ancestors": ancestors, "tags": []})
}

// ─── Trace events ────────────────────────────────────────────────────────

fn value(v: &Value) -> Result<Json> {
    Ok(match v {
        Value::Null => return Err("a null value".into()),
        Value::Bool(b) => json!(b),
        Value::Int(i) => json!(i),
        Value::Decimal(s) => json!({"decimal": s}),
        Value::String(s) => json!(s),
        Value::Entity { ty, id } => json!({"entity": uid_of(ty, id)?}),
        Value::Array(xs) => json!({"set": xs.iter().map(value).collect::<Result<Vec<_>>>()?}),
        Value::Object(m) => match extension(m) {
            Some((f, arg)) => json!({"extension": {"fn": f, "arg": arg}}),
            None => json!({"record": record(m.iter().map(|(k, v)| (k.as_str(), v)))?}),
        },
    })
}

/// The constructor and argument of Cedar's JSON escape for an extension value,
/// `{"__extn": {"fn": F, "arg": A}}`: the crate's form of an `ipaddr`, `datetime`, or `duration`
/// value (`Value::extension`).
fn extension(m: &BTreeMap<String, Value>) -> Option<(&str, &str)> {
    if m.len() != 1 {
        return None;
    }
    let Value::Object(inner) = m.get("__extn")? else {
        return None;
    };
    match (inner.len(), inner.get("fn")?, inner.get("arg")?) {
        (2, Value::String(f), Value::String(arg)) => Some((f, arg)),
        _ => None,
    }
}

/// A record, as `[key, value]` pairs; a null field is absent.
fn record<'a>(fields: impl Iterator<Item = (&'a str, &'a Value)>) -> Result<Json> {
    let mut items = Vec::new();
    for (k, v) in fields {
        if matches!(v, Value::Null) {
            continue;
        }
        items.push(json!([k, value(v)?]));
    }
    Ok(Json::Array(items))
}

fn scope_uid(event: &Event, root: &str) -> Result<Json> {
    Ok(match event.scope_attr(root, &[]) {
        Some(Value::Entity { ty, id }) => uid_of(&ty, &id)?,
        _ => Json::Null,
    })
}

fn timepoint(event: &Event) -> Result<Json> {
    let action = uid_of(&event.namespace().join("::"), event.action())?;
    let top: BTreeSet<String> = event
        .logged_leaves()
        .into_iter()
        .filter_map(|(p, _)| p.first().cloned())
        .collect();
    let logged: Vec<(String, Value)> = top
        .into_iter()
        .filter_map(|k| event.field_path(std::slice::from_ref(&k)).map(|v| (k, v.clone())))
        .collect();
    let logged = record(logged.iter().map(|(k, v)| (k.as_str(), v)))?;
    let context = record(event.request_context_groups())?;
    // The entity store, with each entity's ancestors closed transitively, as Cedar's are. The
    // crate keys its store by the uid's text; each entity and each parent is keyed here by its type
    // and its id instead, so that an ancestor is found whatever characters its id holds.
    let mut uids = Vec::new();
    for u in event.entity_uids() {
        let Some(key) = split_uid(u) else {
            return Err(format!("entity uid `{u}`"));
        };
        uids.push((u, key));
    }
    let parents: BTreeMap<(String, String), Vec<(String, String)>> = uids
        .iter()
        .map(|(u, key)| {
            let ps = event
                .entity_parents(u)
                .iter()
                .filter_map(|p| match p {
                    Value::Entity { ty, id } => Some((ty.clone(), id.clone())),
                    _ => None,
                })
                .collect();
            (key.clone(), ps)
        })
        .collect();
    let mut entities = Vec::new();
    for (u, key) in &uids {
        let mut seen = BTreeSet::new();
        let mut todo: Vec<(String, String)> = parents.get(key).cloned().unwrap_or_default();
        while let Some(parent) = todo.pop() {
            if seen.insert(parent.clone()) {
                todo.extend(parents.get(&parent).cloned().unwrap_or_default());
            }
        }
        let ancestors: Result<Vec<Json>> = seen.iter().map(|(t, i)| uid_of(t, i)).collect();
        let (ty, id) = key;
        entities.push(json!([uid_of(ty, id)?, entity_data(record(event.entity_attributes(u))?, ancestors?)]));
    }
    Ok(json!({"ts": event.timestamp(), "event": {
        "action": action, "kind": event.kind(),
        "principal": scope_uid(event, "principal")?, "resource": scope_uid(event, "resource")?,
        "logged": logged, "context": context, "entities": entities,
    }}))
}

/// An entity uid as the crate keys its entity store, `Ns::Type::"id"`, as its type and its id.
///
/// The crate writes the key as Cedar writes a uid (`EntityUID`'s `Display`): the id escaped by
/// Rust's `str::escape_debug`, which escapes `"`, `\`, and `'`, writes `\0`, `\t`, `\n`, and
/// `\r`, and writes any other character that is not printable, a control character or U+2028
/// for example, as `\u{…}`. Cedar's own parser of uids inverts that form exactly, so the id is
/// the one the event was built with, whatever characters it holds. The previous hand-written
/// inverse undid only `\"` and `\\`, so the entity of an id holding any other escaped character
/// was exported under another id, and lost its attributes and ancestors.
fn split_uid(u: &str) -> Option<(String, String)> {
    let uid: cedar_policy::EntityUid = u.parse().ok()?;
    Some((uid.type_name().to_string(), uid.id().unescaped().to_string()))
}

// ─── Policies ────────────────────────────────────────────────────────────

struct Gen<'a> {
    temporal: &'a HashMap<String, &'a Condition>,
    providers: &'a HashMap<String, Json>,
}

fn field<'a>(j: &'a Json, key: &str) -> Result<&'a Json> {
    j.get(key).ok_or_else(|| format!("missing `{key}` in {j}"))
}

fn json_str<'a>(j: &'a Json, key: &str) -> Result<&'a str> {
    field(j, key)?.as_str().ok_or_else(|| format!("`{key}` must be a string in {j}"))
}

const EXT_FUNS: &[&str] = &[
    "decimal", "lessThan", "lessThanOrEqual", "greaterThan", "greaterThanOrEqual", "ip", "isIpv4",
    "isIpv6", "isLoopback", "isMulticast", "isInRange", "datetime", "duration", "offset",
    "durationSince", "toDate", "toTime", "toMilliseconds", "toSeconds", "toMinutes", "toHours",
    "toDays",
];

fn lit(p: Json) -> Json {
    ctor("lit", json!({"p": p}))
}

fn unary(op: Json, e: Json) -> Json {
    ctor("unaryApp", json!({"op": op, "expr": e}))
}

fn binary(op: &str, a: Json, b: Json) -> Json {
    ctor("binaryApp", json!({"op": op, "a": a, "b": b}))
}

impl Gen<'_> {
    fn policy(&self, id: &str, j: &Json) -> Result<Json> {
        let effect = match json_str(j, "effect")? {
            e @ ("permit" | "forbid") => e,
            e => return Err(format!("unknown effect {e}")),
        };
        let action = field(j, "action")?;
        let action = match json_str(action, "op")? {
            "All" => ctor("actionScope", json!({"scope": "any"})),
            "==" => ctor("actionScope", json!({"scope": ctor("eq", json!({"entity": self.uid(field(action, "entity")?)?}))})),
            "in" => match action.get("entities") {
                Some(Json::Array(es)) => {
                    ctor("actionInAny", json!({"ls": es.iter().map(|e| self.uid(e)).collect::<Result<Vec<_>>>()?}))
                }
                _ => ctor("actionScope", json!({"scope": ctor("mem", json!({"entity": self.uid(field(action, "entity")?)?}))})),
            },
            op => return Err(format!("unknown action constraint {op}")),
        };
        let mut conditions = Vec::new();
        if let Some(Json::Array(cs)) = j.get("conditions") {
            for c in cs {
                let body = self.expr(field(c, "body")?)?;
                match json_str(c, "kind")? {
                    k @ ("when" | "unless") => conditions.push(json!({"kind": k, "body": body})),
                    k => return Err(format!("unknown condition kind {k}")),
                }
            }
        }
        Ok(json!({
            "id": id, "effect": effect,
            "principalScope": ctor("principalScope", json!({"scope": self.scope(field(j, "principal")?)?})),
            "actionScope": action,
            "resourceScope": ctor("resourceScope", json!({"scope": self.scope(field(j, "resource")?)?})),
            "condition": conditions,
        }))
    }

    fn scope(&self, j: &Json) -> Result<Json> {
        Ok(match json_str(j, "op")? {
            "All" => json!("any"),
            "==" => ctor("eq", json!({"entity": self.uid(field(j, "entity")?)?})),
            "in" => ctor("mem", json!({"entity": self.uid(field(j, "entity")?)?})),
            "is" => {
                let ty = self.ety(json_str(j, "entity_type")?)?;
                match j.get("in") {
                    Some(inner) => ctor("isMem", json!({"ety": ty, "entity": self.uid(field(inner, "entity")?)?})),
                    None => ctor("is", json!({"ety": ty})),
                }
            }
            op => return Err(format!("unknown scope constraint {op}")),
        })
    }

    fn ety(&self, ty: &str) -> Result<Json> {
        let path: Vec<String> = ty.split("::").map(str::to_string).collect();
        let (id, ns) = path.split_last().ok_or("empty entity type")?;
        Ok(json!({"id": id, "path": ns}))
    }

    fn uid(&self, j: &Json) -> Result<Json> {
        uid_of(json_str(j, "type")?, json_str(j, "id")?)
    }

    fn value(&self, j: &Json) -> Result<Json> {
        Ok(match j {
            Json::Bool(b) => lit(json!(b)),
            Json::Number(n) => lit(json!(n.as_i64().ok_or_else(|| format!("{n} is not a Long"))?)),
            Json::String(s) => lit(json!(s)),
            Json::Array(items) => {
                ctor("set", json!({"ls": items.iter().map(|i| self.value(i)).collect::<Result<Vec<_>>>()?}))
            }
            Json::Object(o) => {
                if let Some(e) = o.get("__entity") {
                    lit(json!({"entity": self.uid(e)?}))
                } else if let Some(x) = o.get("__extn") {
                    let f = json_str(x, "fn")?;
                    if !EXT_FUNS.contains(&f) {
                        return Err(format!("extension function `{f}`"));
                    }
                    ctor("call", json!({"xfn": f, "args": [self.value(field(x, "arg")?)?]}))
                } else {
                    let map = o
                        .iter()
                        .map(|(k, v)| Ok(json!([k, self.value(v)?])))
                        .collect::<Result<Vec<_>>>()?;
                    ctor("record", json!({"map": map}))
                }
            }
            Json::Null => return Err("null is not a Cedar value".into()),
        })
    }

    fn expr(&self, j: &Json) -> Result<Json> {
        let obj = j.as_object().ok_or_else(|| format!("not an expression: {j}"))?;
        let (op, arg) = obj.iter().next().ok_or("an empty expression")?;
        let left = || self.expr(field(arg, "left")?);
        let right = || self.expr(field(arg, "right")?);
        let bin = |name: &str| -> Result<Json> { Ok(binary(name, left()?, right()?)) };
        // `a > b` is `b < a`, and `a >= b` is `b <= a`, as Cedar builds them.
        let flipped = |name: &str| -> Result<Json> { Ok(binary(name, right()?, left()?)) };
        let un = |name: &str| -> Result<Json> { Ok(unary(json!(name), self.expr(field(arg, "arg")?)?)) };
        let exprs = |xs: &Json, what: &str| -> Result<Vec<Json>> {
            xs.as_array()
                .ok_or_else(|| format!("{what} must be a list"))?
                .iter()
                .map(|e| self.expr(e))
                .collect()
        };
        Ok(match op.as_str() {
            "Value" => self.value(arg)?,
            "Var" => match arg.as_str() {
                Some(v @ ("principal" | "action" | "resource" | "context")) => ctor("var", json!({"v": v})),
                v => return Err(format!("unknown variable {v:?}")),
            },
            "." => {
                let attr = json_str(arg, "attr")?;
                let on = field(arg, "left")?;
                let on_context = on.get("Var").and_then(Json::as_str) == Some("context");
                // `context.providers.<id>`: the hoisted provider field `<id>`.
                let on_providers = on.get(".").is_some_and(|inner| {
                    inner.get("attr").and_then(Json::as_str) == Some("providers")
                        && inner.get("left").and_then(|l| l.get("Var")).and_then(Json::as_str)
                            == Some("context")
                });
                match (self.temporal.get(attr), self.providers.get(attr)) {
                    (Some(phi), _) if on_context => ctor("temporal", json!({"φ": formula(phi)?})),
                    (_, Some(c)) if on_providers => ctor("provider", json!({"c": c})),
                    _ => ctor("getAttr", json!({"expr": left()?, "attr": attr})),
                }
            }
            // `e has a`, or Cedar 4.14's extended `e has a.b.c`, whose `attr` is the path.
            "has" => match field(arg, "attr")? {
                Json::Array(path) => {
                    let path = path
                        .iter()
                        .map(|a| a.as_str().ok_or_else(|| format!("`attr` must hold strings in {arg}")))
                        .collect::<Result<Vec<_>>>()?;
                    match path.split_first() {
                        Some((a, [])) => ctor("hasAttr", json!({"expr": left()?, "attr": a})),
                        Some((a, rest)) => {
                            ctor("extHasAttr", json!({"expr": left()?, "attr": a, "attrs": rest}))
                        }
                        None => return Err(format!("an empty `has` path in {arg}")),
                    }
                }
                _ => ctor("hasAttr", json!({"expr": left()?, "attr": json_str(arg, "attr")?})),
            },
            "!" => un("not")?,
            "neg" => un("neg")?,
            "isEmpty" => un("isEmpty")?,
            "&&" => ctor("and", json!({"a": left()?, "b": right()?})),
            "||" => ctor("or", json!({"a": left()?, "b": right()?})),
            "==" => bin("eq")?,
            "!=" => unary(json!("not"), bin("eq")?),
            "<" => bin("less")?,
            "<=" => bin("lessEq")?,
            ">" => flipped("less")?,
            ">=" => flipped("lessEq")?,
            "+" => bin("add")?,
            "-" => bin("sub")?,
            "*" => bin("mul")?,
            "in" => bin("mem")?,
            "contains" => bin("contains")?,
            "containsAll" => bin("containsAll")?,
            "containsAny" => bin("containsAny")?,
            "getTag" => bin("getTag")?,
            "hasTag" => bin("hasTag")?,
            "like" => unary(ctor("like", json!({"p": self.like(field(arg, "pattern")?)?})), left()?),
            "is" => {
                let ty = self.ety(json_str(arg, "entity_type")?)?;
                let is = unary(ctor("is", json!({"ety": ty})), left()?);
                match arg.get("in") {
                    // `e is T in x` is `e is T && e in x`.
                    Some(x) => ctor("and", json!({"a": is, "b": binary("mem", left()?, self.expr(x)?)})),
                    None => is,
                }
            }
            "if-then-else" => ctor(
                "ite",
                json!({
                    "cond": self.expr(field(arg, "if")?)?,
                    "thenExpr": self.expr(field(arg, "then")?)?,
                    "elseExpr": self.expr(field(arg, "else")?)?,
                }),
            ),
            "Set" => ctor("set", json!({"ls": exprs(arg, "a set")?})),
            "Record" => {
                let map = arg
                    .as_object()
                    .ok_or("a record must be an object")?
                    .iter()
                    .map(|(k, v)| Ok(json!([k, self.expr(v)?])))
                    .collect::<Result<Vec<_>>>()?;
                ctor("record", json!({"map": map}))
            }
            f if EXT_FUNS.contains(&f) => ctor("call", json!({"xfn": f, "args": exprs(arg, "extension arguments")?})),
            other => return Err(format!("Cedar operator `{other}`")),
        })
    }

    fn like(&self, j: &Json) -> Result<Vec<Json>> {
        let elems = j.as_array().ok_or("a like pattern must be a list")?;
        let mut items = Vec::new();
        for e in elems {
            match e {
                Json::String(w) if w == "Wildcard" => items.push(json!("star")),
                Json::Object(o) => {
                    let lit = o
                        .get("Literal")
                        .and_then(Json::as_str)
                        .ok_or_else(|| format!("unknown like element {e}"))?;
                    for c in lit.chars() {
                        items.push(ctor("justChar", json!({"c": c.to_string()})));
                    }
                }
                _ => return Err(format!("unknown like element {e}")),
            }
        }
        Ok(items)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Ids that Cedar's form of a uid escapes: quotes and a backslash, control characters, the
    /// line and paragraph separators, a combining mark at the start (escaped) and after a letter
    /// (not escaped), a byte-order mark, and characters outside the basic plane.
    const IDS: &[&str] = &[
        "alice",
        "",
        "O'Brien",
        "say \"hi\"",
        "back\\slash",
        "\\\"",
        "'\"\\",
        "nul\0byte",
        "tab\tnewline\ncr\r",
        "\u{1}\u{1f}\u{7f}\u{9f}",
        "line\u{2028}paragraph\u{2029}",
        "\u{301}accent",
        "e\u{301}",
        "\u{feff}bom",
        "\u{10ffff}\u{1f600}",
        "\\u{41}",
        "::\"",
    ];

    /// The key the crate gives the entity `(ty, id)` in its entity store.
    fn store_key(ty: &str, id: &str) -> String {
        let event = Event::builder_for(&["Drupe", "Action"], "Read", "request")
            .entity_for(ty, id, [])
            .build();
        let keys: Vec<&str> = event.entity_uids().collect();
        assert_eq!(keys.len(), 1, "one entity, keyed once");
        keys[0].to_string()
    }

    #[test]
    fn split_uid_inverts_the_store_key() {
        for id in IDS {
            for ty in ["User", "Drupe::OAuthUser"] {
                let key = store_key(ty, id);
                assert_eq!(
                    split_uid(&key),
                    Some((ty.to_string(), id.to_string())),
                    "type {ty}, id {id:?}"
                );
            }
        }
    }

    #[test]
    fn split_uid_inverts_the_store_key_on_every_character_of_the_first_planes() {
        for c in (0..0x3400u32).chain(0xfe00..0x10000).filter_map(char::from_u32) {
            for id in [c.to_string(), format!("a{c}")] {
                let key = store_key("User", &id);
                assert_eq!(split_uid(&key), Some(("User".to_string(), id.clone())), "{c:?}");
            }
        }
    }

    /// The exported entities of an event whose principal, and the groups it is a member of, have
    /// ids that Cedar's form escapes: each keeps its id, its attributes, and its ancestors.
    #[test]
    fn exported_entities_keep_escaped_ids_attributes_and_ancestors() {
        let user = "O'Brien\u{2028}\t";
        let team = "team\u{1}'";
        let org = "org\\\"";
        let event = Event::builder_for(&["Drupe", "Action"], "Read", "request")
            .principal_for("Drupe::OAuthUser", user)
            .resource_for("Drupe::Gateway", "gw1")
            .entity_for("Drupe::OAuthUser", user, [("level", Value::Int(5))])
            .parents_for("Drupe::OAuthUser", user, [("Drupe::Group", team)])
            .entity_for("Drupe::Group", team, [("size", Value::Int(2))])
            .parents_for("Drupe::Group", team, [("Drupe::Group", org)])
            .entity_for("Drupe::Group", org, [])
            .build();
        let exported = timepoint(&event).expect("the event exports");
        let ev = &exported["event"];
        let entities = ev["entities"].as_array().expect("entities");
        let entity = |ty: &str, id: &str| {
            let want = uid_of(ty, id).unwrap();
            entities
                .iter()
                .find(|e| e[0] == want)
                .unwrap_or_else(|| panic!("no exported entity of type {ty} with id {id:?}"))[1]
                .clone()
        };
        assert_eq!(ev["principal"], uid_of("Drupe::OAuthUser", user).unwrap());
        let alice = entity("Drupe::OAuthUser", user);
        assert_eq!(alice["attrs"], json!([["level", 5]]));
        let mut ancestors = alice["ancestors"].as_array().unwrap().clone();
        ancestors.sort_by_key(|a| a.to_string());
        let mut want = vec![uid_of("Drupe::Group", team).unwrap(), uid_of("Drupe::Group", org).unwrap()];
        want.sort_by_key(|a| a.to_string());
        assert_eq!(ancestors, want, "the ancestors are closed transitively");
        let team_data = entity("Drupe::Group", team);
        assert_eq!(team_data["attrs"], json!([["size", 2]]));
        assert_eq!(team_data["ancestors"], json!([uid_of("Drupe::Group", org).unwrap()]));
        assert_eq!(entity("Drupe::Group", org)["ancestors"], json!([]));
    }
}
