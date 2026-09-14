//! Shared replay, observation, corpus-loading, and oracle machinery for the
//! leaf-slicing differentials.
#![allow(dead_code)] // each test target uses a subset

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use dogwood_language::{
    ActionScope, Authorizer, Decision, Error, Event, EventSignature, InMemoryTemporalEngine,
    LoweredPolicySet, PartitionKey, PolicySchema, ProviderDeclarations, ServiceSchema,
    TemporalBindings, TemporalEngine, TemporalField,
    cedar::{Entities, EntityUid, Schema},
    parse_trace,
};

// ── the observation seam ────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct Pass {
    pub event: Event,
    pub computed: BTreeSet<String>,
    pub bindings: BTreeMap<String, bool>,
}

/// Records evaluations while delegating behavior to `InMemoryTemporalEngine`.
pub struct Spy {
    inner: InMemoryTemporalEngine,
    last: Option<Event>,
    passes: Arc<Mutex<Vec<Pass>>>,
}

impl Spy {
    pub fn new(inner: InMemoryTemporalEngine) -> (Self, Arc<Mutex<Vec<Pass>>>) {
        let passes = Arc::new(Mutex::new(Vec::new()));
        (
            Spy {
                inner,
                last: None,
                passes: Arc::clone(&passes),
            },
            passes,
        )
    }
}

impl TemporalEngine for Spy {
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        schema: &Schema,
        events: &[EventSignature],
    ) -> Result<(), Error> {
        self.inner.prepare(leaves, schema, events)
    }

    fn observe(&mut self, event: &Event) {
        self.last = Some(event.clone());
        self.inner.observe(event);
    }

    fn evaluate(&mut self) -> Result<TemporalBindings, String> {
        let bindings = self.inner.evaluate()?;
        self.passes.lock().unwrap().push(Pass {
            event: self.last.clone().expect("evaluate follows observe"),
            computed: self.inner.computed_leaves().clone(),
            bindings: bindings.clone(),
        });
        Ok(bindings)
    }

    fn supports_partitioning(&self) -> bool {
        self.inner.supports_partitioning()
    }

    fn set_partition_keys(&mut self, keys: &[PartitionKey]) {
        self.inner.set_partition_keys(keys);
    }
}

pub struct Run {
    pub verdicts: Vec<String>,
    pub passes: Vec<Pass>,
}

pub fn replay(lowered: LoweredPolicySet, events: &[Event], slicing: bool) -> Run {
    let engine = if slicing {
        InMemoryTemporalEngine::new().slice_leaves()
    } else {
        InMemoryTemporalEngine::new()
    };
    let (spy, passes) = Spy::new(engine);
    let mut authorizer = Authorizer::builder(lowered)
        .temporal_engine(spy)
        .build()
        .expect("authorizer builds");
    let mut verdicts = Vec::new();
    for (i, event) in events.iter().enumerate() {
        if let Some(response) = authorizer.is_authorized(event) {
            let allowed = response.decision() == Decision::Allow;
            verdicts.push(format!(
                "@{} (time point {i}): {allowed}",
                event.timestamp()
            ));
        }
    }
    let passes = passes.lock().unwrap().clone();
    Run { verdicts, passes }
}

// ── the independent out-of-scope oracle ─────────────────────────────────

/// Independently determine whether Cedar could apply `scope` to `action`.
///
/// This uses schema action identities and Cedar's action hierarchy, not the
/// map's target expansion. Unrecognized scopes conservatively return `true`.
pub fn scope_could_match(
    scope: &ActionScope,
    action: &EntityUid,
    schema: &Schema,
    actions: &Entities,
) -> bool {
    match scope {
        ActionScope::Unconstrained => true,
        ActionScope::Concrete(a) => {
            uid_of(a.namespace.as_deref(), &a.id, schema).is_none_or(|listed| &listed == action)
        }
        ActionScope::List(list) => list.iter().any(|a| {
            match uid_of(a.namespace.as_deref(), &a.id, schema) {
                Some(listed) => &listed == action || actions.is_ancestor_of(&listed, action),
                None => true,
            }
        }),
    }
}

/// Find a schema action by structural identity rather than rendered spelling.
pub fn uid_of(namespace: Option<&str>, id: &str, schema: &Schema) -> Option<EntityUid> {
    schema
        .actions()
        .find(|uid| {
            uid.id().unescaped() == id
                && uid.type_name().namespace() == namespace.unwrap_or_default()
        })
        .cloned()
}

pub fn event_action_uid(event: &Event, schema: &Schema) -> Option<EntityUid> {
    let path = event.namespace().join("::");
    schema
        .actions()
        .find(|uid| uid.id().unescaped() == event.action() && uid.type_name().to_string() == path)
        .cloned()
}

// ── corpus loading (mirrors the passing/* harnesses) ────────────────────

pub fn norm(s: &str) -> Vec<String> {
    s.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(str::to_string)
        .collect()
}

pub fn case_dirs(root: &Path) -> Vec<PathBuf> {
    let mut v: Vec<_> = std::fs::read_dir(root)
        .unwrap_or_else(|e| panic!("read_dir({}): {e}", root.display()))
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    v.sort();
    v
}

pub fn read_sorted(dir: &Path, prefix: &str, ext: &str) -> Vec<PathBuf> {
    let mut v: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with(prefix))
                && p.extension().is_some_and(|e| e == ext)
        })
        .collect();
    v.sort();
    v
}

/// Sources and expected traces for a committed or synthesized corpus case.
#[derive(Clone)]
pub struct Case {
    pub name: String,
    pub policy: String,
    pub schema: String,
    pub event_schema: String,
    pub providers: Option<ProviderDeclarations>,
    pub traces: Vec<(String, String, String)>,
}

pub fn load_case(dir: &Path, shared_schema: &str, shared_event_schema: &str) -> Option<Case> {
    let policy = read_sorted(dir, "policy_", "dw")
        .iter()
        .map(|p| std::fs::read_to_string(p).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    if policy.is_empty() {
        return None;
    }
    let schema = if dir.join("schema.cedarschema").exists() {
        std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap()
    } else {
        shared_schema.to_string()
    };
    let event_schema = std::fs::read_to_string(dir.join("event.dwschema"))
        .unwrap_or_else(|_| shared_event_schema.to_string());
    let providers = dir
        .join("providers.json")
        .exists()
        .then(|| ProviderDeclarations::from_json_file(dir.join("providers.json")).ok())
        .flatten();

    let mut traces = Vec::new();
    for trace_path in read_sorted(dir, "trace_", "log") {
        let stem = trace_path
            .file_stem()
            .unwrap()
            .to_string_lossy()
            .to_string();
        let n = stem.trim_start_matches("trace_").to_string();
        let expected_path = dir.join(format!("expected_{n}.out"));
        if !expected_path.exists() {
            continue;
        }
        traces.push((
            n,
            std::fs::read_to_string(&trace_path).unwrap(),
            std::fs::read_to_string(&expected_path).unwrap(),
        ));
    }
    (!traces.is_empty()).then_some(Case {
        name: dir.file_name().unwrap().to_string_lossy().to_string(),
        policy,
        schema,
        event_schema,
        providers,
        traces,
    })
}

impl Case {
    pub fn lower(&self) -> Result<LoweredPolicySet, String> {
        let policy_schema =
            PolicySchema::from_cedarschema_str(&self.schema).map_err(|e| format!("{e:?}"))?;
        let mut builder = ServiceSchema::builder().event_schema_str(&self.event_schema);
        if let Some(d) = &self.providers {
            builder = builder.providers(d.clone());
        }
        let service = builder.build().map_err(|e| format!("{e:?}"))?;
        LoweredPolicySet::from_str(&self.policy, &service, &policy_schema)
            .map_err(|e| format!("{e:?}"))
    }
}

/// Load every case of both temporal corpora.
pub fn corpus() -> Vec<Case> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let shared_event_schema =
        std::fs::read_to_string(root.join("tests/fixtures/request_response.dwschema"))
            .expect("the shared unpinned event schema fixture");
    let temporal_shared =
        std::fs::read_to_string(root.join("tests/passing/temporal_only/shared_schema.cedarschema"))
            .expect("the temporal_only shared schema");

    let mut cases = Vec::new();
    for (dir, shared) in [
        ("tests/passing/temporal_only/corpus", &temporal_shared[..]),
        // The mixed corpus ships a schema per case, so it has no shared fallback.
        ("tests/passing/mixed/corpus", ""),
    ] {
        let dir = root.join(dir);
        if !dir.exists() {
            continue;
        }
        cases.extend(
            case_dirs(&dir)
                .iter()
                .filter_map(|d| load_case(d, shared, &shared_event_schema)),
        );
    }
    cases
}

// ── what a run measures ─────────────────────────────────────────────────

/// Coverage counters used to reject vacuous differentials.
#[derive(Default, Debug, Clone)]
pub struct Totals {
    pub cases: usize,
    pub traces: usize,
    pub decisions: usize,
    pub unsliced_leaves: usize,
    pub sliced_leaves: usize,
    pub sliced_decisions: usize,
    pub zero_leaf_decisions: usize,
    /// Decisions that suppressed a leaf whose unsliced value was `true`.
    pub suppressed_true_decisions: usize,
    pub cases_with_unresolved_scopes: usize,
}

impl Totals {
    pub fn merge(&mut self, other: &Totals) {
        self.cases += other.cases;
        self.traces += other.traces;
        self.decisions += other.decisions;
        self.unsliced_leaves += other.unsliced_leaves;
        self.sliced_leaves += other.sliced_leaves;
        self.sliced_decisions += other.sliced_decisions;
        self.zero_leaf_decisions += other.zero_leaf_decisions;
        self.suppressed_true_decisions += other.suppressed_true_decisions;
        self.cases_with_unresolved_scopes += other.cases_with_unresolved_scopes;
    }
}

/// Compare verdicts, exact computed sets, bindings, and the independent oracle.
pub fn check_case(case: &Case) -> (Totals, Vec<String>) {
    let mut totals = Totals {
        cases: 1,
        ..Totals::default()
    };
    let mut failures = Vec::new();

    let oracle = match case.lower() {
        Ok(l) => l,
        Err(e) => {
            failures.push(format!("{}: lowering: {e}", case.name));
            return (totals, failures);
        }
    };
    let leaves: Vec<TemporalField> = oracle.temporal_fields().cloned().collect();
    if leaves.is_empty() {
        return (totals, failures);
    }
    let all_ids: BTreeSet<String> = leaves.iter().map(|f| f.id.clone()).collect();
    let scope_of: BTreeMap<&str, &ActionScope> =
        leaves.iter().map(|f| (f.id.as_str(), &f.action)).collect();
    let map = oracle.leaf_map();
    if !map.unresolved().is_empty() {
        totals.cases_with_unresolved_scopes = 1;
    }
    let schema = oracle.cedar_schema();
    let action_entities = match schema.action_entities() {
        Ok(e) => e,
        Err(e) => {
            failures.push(format!("{}: schema action entities: {e}", case.name));
            return (totals, failures);
        }
    };

    for (n, trace, expected) in &case.traces {
        let events = match parse_trace(trace) {
            Ok(e) => e,
            Err(e) => {
                failures.push(format!("{}: trace_{n}: parse: {e:?}", case.name));
                continue;
            }
        };
        let (unsliced, sliced) = match (case.lower(), case.lower()) {
            (Ok(a), Ok(b)) => (replay(a, &events, false), replay(b, &events, true)),
            _ => {
                failures.push(format!("{}: trace_{n}: re-lowering failed", case.name));
                continue;
            }
        };
        totals.traces += 1;

        // (1) identical verdict streams, and the case's own expectation.
        if unsliced.verdicts != sliced.verdicts {
            failures.push(format!(
                "{}: trace_{n}: SLICING CHANGED A VERDICT\n  unsliced: {:?}\n  sliced:   {:?}",
                case.name, unsliced.verdicts, sliced.verdicts
            ));
            continue;
        }
        if norm(&sliced.verdicts.join("\n")) != norm(expected) {
            failures.push(format!(
                "{}: trace_{n}: sliced stream does not match expected_{n}.out\n  got: {:?}\n  exp: {:?}",
                case.name,
                norm(&sliced.verdicts.join("\n")),
                norm(expected)
            ));
            continue;
        }
        if unsliced.passes.len() != sliced.passes.len() {
            failures.push(format!(
                "{}: trace_{n}: different number of decision points",
                case.name
            ));
            continue;
        }

        for (k, pass) in sliced.passes.iter().enumerate() {
            // The event the engine decided for — carried by the pass, so the
            // attribution comes from the engine's own view rather than from a
            // reimplementation of which kinds are decision points.
            let event = &pass.event;
            totals.decisions += 1;
            totals.sliced_leaves += pass.computed.len();
            totals.unsliced_leaves += unsliced.passes[k].computed.len();

            // (2a) exactly what the map predicts — equality, not containment.
            let predicted: BTreeSet<String> = match map.needed_for(event) {
                Some(ids) => (*ids).clone(),
                None => all_ids.clone(),
            };
            if pass.computed != predicted {
                failures.push(format!(
                    "{}: trace_{n}: decision {k} ({}): computed {:?}, map predicts {:?}",
                    case.name,
                    event.action(),
                    pass.computed,
                    predicted
                ));
                continue;
            }
            if pass.bindings.keys().cloned().collect::<BTreeSet<_>>() != all_ids {
                failures.push(format!(
                    "{}: trace_{n}: decision {k}: not every leaf was bound",
                    case.name
                ));
                continue;
            }

            let skipped: Vec<&String> = all_ids.difference(&pass.computed).collect();
            if skipped.is_empty() {
                continue;
            }
            totals.sliced_decisions += 1;
            if pass.computed.is_empty() {
                totals.zero_leaf_decisions += 1;
            }
            if skipped
                .iter()
                .any(|id| unsliced.passes[k].bindings.get(*id) == Some(&true))
            {
                totals.suppressed_true_decisions += 1;
            }

            // (2b) the independent direction: a skipped leaf's rule must be one
            // Cedar could not have applied here. An undeclared action has no map
            // entry, so it cannot reach this point with anything skipped.
            let Some(action_uid) = event_action_uid(event, schema) else {
                failures.push(format!(
                    "{}: trace_{n}: decision {k}: leaves skipped for an action the \
                     schema does not declare ({})",
                    case.name,
                    event.action()
                ));
                continue;
            };
            for id in skipped {
                let scope = scope_of[id.as_str()];
                if scope_could_match(scope, &action_uid, schema, &action_entities) {
                    failures.push(format!(
                        "{}: trace_{n}: decision {k} ({}): skipped leaf {id}, but its \
                         scope {scope:?} CAN match that action",
                        case.name,
                        event.action()
                    ));
                }
                if pass.bindings.get(id) != Some(&false) {
                    failures.push(format!(
                        "{}: trace_{n}: decision {k}: skipped leaf {id} was not bound false",
                        case.name
                    ));
                }
            }
        }
    }
    (totals, failures)
}

/// `check_case` over many cases, chunked across worker threads as the corpus
/// harnesses do. Each case is independent and the fold is order-insensitive (a
/// sum and a concatenation), so the split is invisible to the result.
pub fn check_all(cases: &[Case]) -> (Totals, Vec<String>) {
    let nthreads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .min(cases.len().max(1));
    let chunk = cases.len().div_ceil(nthreads).max(1);
    let results: Vec<(Totals, Vec<String>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = cases
            .chunks(chunk)
            .map(|chunk| scope.spawn(move || chunk.iter().map(check_case).collect::<Vec<_>>()))
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect()
    });

    let mut totals = Totals::default();
    let mut failures = Vec::new();
    for (t, f) in &results {
        totals.merge(t);
        failures.extend(f.iter().cloned());
    }
    (totals, failures)
}
