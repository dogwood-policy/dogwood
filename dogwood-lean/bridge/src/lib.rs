//! `dogwood-lean-bridge` — export Dogwood policy-set bundles, as the
//! `dogwood-language` crate in this repository parses, lowers, and validates
//! them, as JSON values of the `dogwood-lean` specification's types.
//!
//! For each bundle directory it records either the stage at which the crate
//! rejected the bundle, or — when the bundle lowers — the derived event schema,
//! its `max_window` and `max_horizon` caps, every temporal leaf (after macro expansion and pin
//! injection, before the pin-relativization rewrite), and which categories of
//! temporal validation finding the crate reported. The `conformance` executable
//! of the Lake project compares those verdicts with the specification's own
//! checks.
//!
//! The output is a JSON array of `Dogwood.Conformance.Case`s, in the encoding
//! `Dogwood.Conformance.Json` reads: mostly Lean's derived encoding, where a
//! constructor is its name or `{"name": {"arg": …}}` and a structure is an
//! object of its fields.
//!
//! A bundle directory holds the policy source (`policy.dw`, or `policy_*.dw`
//! concatenated in name order), and optionally `schema.cedarschema`,
//! `event.dwschema` / `events.dwschema`, `providers.json`, and `macros.dw` —
//! the layouts of the crate's test corpora and of the guide's examples. With `--frontend`, a
//! bundle may also hold `ids.json` (`"annotation"`, or an array of explicit ids) and
//! `distincter.txt`, which the public pipeline of the export lowers with; and a bundle holding
//! `many.json` (`{"entries": [{"policy": FILE, "distincter": D, "ids": null | "annotation" |
//! [ID, …]}, …]}`) is several policy sets lowered together (`lower_many`) over the bundle's
//! schemas. `--many K` (with `--frontend`) instead makes multi-entry bundles of the directories
//! given, K at a time: each takes its schemas from its first directory and one entry per
//! directory, with the distincters `e0`, `e1`, …, and explicit ids for every second entry.
//!
//! Usage:
//!
//! ```text
//! dogwood-lean-bridge [--frontend [--many K]] --out FILE.json
//!     [--shared-schema FILE] [--default-event-schema FILE] DIR...
//! ```
//!
//! With `--frontend`, each bundle's record is instead the crate's export of its frontend
//! (`dogwood_language::frontend_export`): the parsers' outputs, and every stage's observable,
//! which the `frontend-diff` executable of the Lake project compares stage by stage with the Lean
//! frontend. The bridge adds what the comparison reads in the specification's types: each lowered
//! rule as a `Dogwood.Spec.Policy` with the crate's names (`spec`, next to Cedar's policy JSON),
//! the action schema and the augmented schema as Cedar compiles them (`baseValidatorSchema`,
//! `validatorSchema`, with every context attribute), and the bundle's record of the default mode
//! without its traces (`conformance`).
//!
//! The binary is [`main_with`] without an engine. A caller that links this library may run the
//! same export with a temporal engine of its own ([`EngineFactory`]): each trace's `Authorizer`
//! then evaluates the temporal leaves with a fresh engine from the factory, partitioned
//! (`AuthorizerBuilder::partition_temporal`), and the export records that engine's verdicts.

use std::path::{Path, PathBuf};

use serde_json::{Value as Json, json};

mod decisions;
mod schema;

use dogwood_language::temporal_ast::{
    AggExpr, AggExprKind, ArithOp, BinderSlot, CmpOp, Condition, ConditionKind, Term, TimeUnit,
    Type, TypedBinder, WithinSpec,
};
use dogwood_language::{
    DEFAULT_EVENT_SCHEMA, Error, IdSource, LoweredPolicySet, PolicySchema, ProviderDeclarations,
    ServiceSchema, TemporalEngine, ValidationError, ValidationWarning, Validator,
};

/// Makes the temporal engine of one trace's `Authorizer`: called once per trace, with the
/// bundle's lowered policy set (the one the `Authorizer` decides with) and a label naming the
/// trace (`<bundle>/<trace file>`). The `Authorizer` is built with the engine and
/// `partition_temporal()`.
pub type EngineFactory = dyn Fn(&LoweredPolicySet, &str) -> Box<dyn TemporalEngine>;

// ─── Command line ────────────────────────────────────────────────────────

struct Args {
    frontend: bool,
    many: Option<usize>,
    out: PathBuf,
    shared_schema: Option<PathBuf>,
    default_event_schema: Option<PathBuf>,
    dirs: Vec<PathBuf>,
}

fn parse_args() -> Result<Args, String> {
    let mut frontend = false;
    let mut many = None;
    let mut out = None;
    let mut shared_schema = None;
    let mut default_event_schema = None;
    let mut dirs = Vec::new();
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        let mut value = |name: &str| it.next().ok_or_else(|| format!("{name} needs a value"));
        match a.as_str() {
            "--frontend" => frontend = true,
            "--many" => {
                let k: usize = value("--many")?.parse().map_err(|_| "--many needs a number".to_string())?;
                if k == 0 {
                    return Err("--many needs a positive number".to_string());
                }
                many = Some(k);
            }
            "--out" => out = Some(PathBuf::from(value("--out")?)),
            "--shared-schema" => shared_schema = Some(PathBuf::from(value("--shared-schema")?)),
            "--default-event-schema" => {
                default_event_schema = Some(PathBuf::from(value("--default-event-schema")?))
            }
            flag if flag.starts_with("--") => return Err(format!("unknown flag {flag}")),
            dir => dirs.push(PathBuf::from(dir)),
        }
    }
    if many.is_some() && !frontend {
        return Err("--many needs --frontend".to_string());
    }
    Ok(Args {
        frontend,
        many,
        out: out.ok_or("--out is required")?,
        shared_schema,
        default_event_schema,
        dirs,
    })
}

/// The command line's export: each bundle directory's record, written to `--out`. With
/// `engine`, each trace is decided with a fresh engine of its own, partitioned
/// ([`EngineFactory`]); without, with the crate's built-in engine, as the binary does.
pub fn main_with(engine: Option<&EngineFactory>) {
    let args = match parse_args() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("dogwood-lean-bridge: {e}");
            std::process::exit(2);
        }
    };
    let shared_schema = args
        .shared_schema
        .as_ref()
        .map(|p| read(p))
        .unwrap_or_default();
    let default_event_schema = args
        .default_event_schema
        .as_ref()
        .map(|p| read(p))
        .unwrap_or_else(|| DEFAULT_EVENT_SCHEMA.to_string());

    let mut cases = Vec::new();
    let mut lowered = 0;
    if let Some(k) = args.many {
        for chunk in args.dirs.chunks(k) {
            let bundles: Vec<Bundle> =
                chunk.iter().map(|d| Bundle::load(d, &shared_schema, &default_event_schema)).collect();
            let many = ManyBundle::of_bundles(&bundles, k);
            let record = many.frontend();
            if record["frontend"]["many"]["outcome"].get("lowered").is_some() {
                lowered += 1;
            }
            cases.push(record);
        }
        write_cases(&args.out, &cases, cases.len(), lowered);
        return;
    }
    for dir in &args.dirs {
        if args.frontend && dir.join("many.json").exists() {
            let many = ManyBundle::load(dir, &shared_schema, &default_event_schema);
            let record = many.frontend();
            if record["frontend"]["many"]["outcome"].get("lowered").is_some() {
                lowered += 1;
            }
            cases.push(record);
            continue;
        }
        let bundle = Bundle::load(dir, &shared_schema, &default_event_schema);
        if args.frontend {
            let record = bundle.frontend();
            if record["frontend"]["conformance"].get("lowered").is_some() {
                lowered += 1;
            }
            cases.push(record);
            continue;
        }
        let outcome = bundle.run(engine);
        if matches!(outcome, Outcome::Lowered(_)) {
            lowered += 1;
        }
        cases.push(json!({"name": bundle.name, "outcome": outcome.to_json()}));
    }
    write_cases(&args.out, &cases, args.dirs.len(), lowered);
}

fn write_cases(path: &Path, cases: &[Json], bundles: usize, lowered: usize) {
    let out = serde_json::to_string(cases).expect("JSON values serialize");
    std::fs::write(path, out).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
    eprintln!("dogwood-lean-bridge: {bundles} bundles ({lowered} lowered) -> {}", path.display());
}

/// An id source as `ids.json` or `many.json` writes it: `"annotation"`, or an array of explicit
/// ids.
fn id_source_of(j: &Json) -> Option<IdSource> {
    match j {
        Json::String(s) if s == "annotation" => Some(IdSource::Annotation),
        Json::Array(ids) => Some(IdSource::Explicit(
            ids.iter().map(|i| i.as_str().unwrap_or_default().to_string()).collect(),
        )),
        _ => None,
    }
}

/// Several policy sets lowered together over one bundle's schemas (`many.json`, or `--many`).
struct ManyBundle {
    name: String,
    /// Each entry's policy text, distincter and id source.
    entries: Vec<(String, String, Option<IdSource>)>,
    schema_src: String,
    event_schema: String,
    providers: Option<PathBuf>,
    macros: Option<String>,
}

impl ManyBundle {
    fn load(dir: &Path, shared_schema: &str, default_event_schema: &str) -> ManyBundle {
        let base = Bundle::load_sources(dir, shared_schema, default_event_schema);
        let spec: Json = serde_json::from_str(&read(&dir.join("many.json")))
            .unwrap_or_else(|e| panic!("{}: many.json: {e}", dir.display()));
        let entries = spec["entries"]
            .as_array()
            .map(|es| {
                es.iter()
                    .map(|e| {
                        let file = e["policy"].as_str().unwrap_or_default();
                        (
                            read(&dir.join(file)),
                            e["distincter"].as_str().unwrap_or_default().to_string(),
                            id_source_of(&e["ids"]),
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();
        ManyBundle {
            name: base.name,
            entries,
            schema_src: base.schema_src,
            event_schema: base.event_schema,
            providers: base.providers,
            macros: base.macros,
        }
    }

    /// Bundles lowered together, `k` at a time: the schemas of the first, the policy of each,
    /// distincters `e0`, `e1`, …, and explicit ids `r0`, `r1`, … for every second entry (as many
    /// as its policy set has policies, under the first bundle's service schema).
    fn of_bundles(bundles: &[Bundle], k: usize) -> ManyBundle {
        let first = &bundles[0];
        let service = first.service_schema().ok();
        let entries = bundles
            .iter()
            .enumerate()
            .map(|(j, b)| {
                let ids = if j % 2 == 1 {
                    service.as_ref().and_then(|service| {
                        dogwood_language::ParsedPolicySet::parse(&b.policy_src, service).ok().map(|p| {
                            IdSource::Explicit((0..p.policy_count()).map(|i| format!("r{i}")).collect())
                        })
                    })
                } else {
                    None
                };
                (b.policy_src.clone(), format!("e{j}"), ids)
            })
            .collect();
        ManyBundle {
            name: format!("many{k}/{}+{}", first.name.replace('/', ":"), bundles.len() - 1),
            entries,
            schema_src: first.schema_src.clone(),
            event_schema: first.event_schema.clone(),
            providers: first.providers.clone(),
            macros: first.macros.clone(),
        }
    }

    fn frontend(&self) -> Json {
        let providers = self.providers.as_ref().map(|p| read(p));
        let entries: Vec<dogwood_language::frontend_export::ManyEntry<'_>> = self
            .entries
            .iter()
            .map(|(policy, distincter, ids)| dogwood_language::frontend_export::ManyEntry {
                policy,
                distincter,
                ids: ids.as_ref(),
            })
            .collect();
        let many = dogwood_language::frontend_export::export_many(
            &dogwood_language::frontend_export::ManySources {
                entries: &entries,
                event_schema: Some(&self.event_schema),
                providers: providers.as_deref(),
                macros: self.macros.as_deref(),
                action_schema: &self.schema_src,
            },
        );
        json!({"name": self.name, "frontend": {"many": many}})
    }
}

fn read(p: &Path) -> String {
    std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

// ─── Bundles ─────────────────────────────────────────────────────────────

#[derive(Clone)]
struct Bundle {
    name: String,
    traces: Vec<(String, String)>,
    policy_src: String,
    schema_src: String,
    event_schema: String,
    providers: Option<PathBuf>,
    macros: Option<String>,
    /// The id source of `ids.json`, if any (the export's public pipeline lowers with it).
    ids: Option<IdSource>,
    /// The distincter of `distincter.txt`, if any.
    distincter: Option<String>,
}

impl Bundle {
    /// The bundle's sources, without the trace files.
    fn load_sources(dir: &Path, shared_schema: &str, default_event_schema: &str) -> Bundle {
        let mut b = Bundle::load(dir, shared_schema, default_event_schema);
        b.traces = Vec::new();
        b
    }

    fn load(dir: &Path, shared_schema: &str, default_event_schema: &str) -> Bundle {
        let optional = |file: &str| std::fs::read_to_string(dir.join(file)).ok();
        let policy_src = match optional("policy.dw") {
            Some(src) => src,
            None => {
                let mut paths: Vec<PathBuf> = std::fs::read_dir(dir)
                    .unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display()))
                    .filter_map(|e| e.ok().map(|e| e.path()))
                    .filter(|p| {
                        p.extension().is_some_and(|e| e == "dw")
                            && p.file_name()
                                .and_then(|n| n.to_str())
                                .is_some_and(|n| n.starts_with("policy_"))
                    })
                    .collect();
                paths.sort();
                paths.iter().map(|p| read(p)).collect::<Vec<_>>().join("\n")
            }
        };
        let name = {
            let parent = dir
                .parent()
                .and_then(|p| p.file_name())
                .map(|n| n.to_string_lossy().to_string())
                .unwrap_or_default();
            let leaf = dir.file_name().unwrap().to_string_lossy().to_string();
            format!("{parent}/{leaf}")
        };
        Bundle {
            name,
            traces: decisions::trace_files(dir),
            policy_src,
            schema_src: optional("schema.cedarschema").unwrap_or_else(|| shared_schema.to_string()),
            event_schema: optional("event.dwschema")
                .or_else(|| optional("events.dwschema"))
                .unwrap_or_else(|| default_event_schema.to_string()),
            providers: Some(dir.join("providers.json")).filter(|p| p.exists()),
            macros: optional("macros.dw"),
            ids: optional("ids.json")
                .and_then(|t| serde_json::from_str::<Json>(&t).ok())
                .and_then(|j| id_source_of(&j)),
            distincter: optional("distincter.txt").map(|t| t.strip_suffix('\n').unwrap_or(&t).to_string()),
        }
    }

    /// The bundle's service schema, as the export's public pipeline builds it.
    fn service_schema(&self) -> std::result::Result<ServiceSchema, String> {
        let mut builder = ServiceSchema::builder().event_schema_str(&self.event_schema);
        if let Some(path) = &self.providers {
            let decls: ProviderDeclarations =
                serde_json::from_str(read(path).strip_prefix('\u{FEFF}').unwrap_or(&read(path))).map_err(|e| e.to_string())?;
            builder = builder.providers(decls);
        }
        if let Some(m) = &self.macros {
            builder = builder.macros_str(m);
        }
        builder.build().map_err(|e| e.to_string())
    }

    /// The bundle's provider declarations, read from the file, so that a `scriptFile` resolves
    /// against the bundle directory.
    fn provider_decls(&self) -> std::result::Result<Option<ProviderDeclarations>, String> {
        match &self.providers {
            Some(path) => ProviderDeclarations::from_json_file(path).map(Some).map_err(|e| e.to_string()),
            None => Ok(None),
        }
    }

    /// Lower the bundle, or the stage at which the crate rejected it and why.
    fn lower(&self) -> std::result::Result<LoweredPolicySet, (&'static str, String)> {
        let mut builder = ServiceSchema::builder().event_schema_str(&self.event_schema);
        match self.provider_decls() {
            Ok(Some(p)) => builder = builder.providers(p),
            Ok(None) => {}
            Err(e) => return Err(("providers", e)),
        }
        if let Some(m) = &self.macros {
            builder = builder.macros_str(m);
        }
        let service = match builder.build() {
            Ok(s) => s,
            Err(e) => return Err(("service schema", e.to_string())),
        };
        let policy_schema = match PolicySchema::from_cedarschema_str(&self.schema_src) {
            Ok(s) => s,
            Err(e) => return Err(("action schema", e.to_string())),
        };
        LoweredPolicySet::from_str(&self.policy_src, &service, &policy_schema).map_err(|e| {
            let stage = match &e {
                Error::Parse(_) => "parse",
                _ => "lower",
            };
            (stage, e.to_string())
        })
    }

    /// The bundle's frontend record (`--frontend`): the crate's export of its frontend, with each
    /// cedarified rule also in the specification's form, the compiled schemas, and the bundle's
    /// record of the default mode without its traces.
    fn frontend(&self) -> Json {
        let providers = self.providers.as_ref().map(|p| read(p));
        let mut out = dogwood_language::frontend_export::export(
            &dogwood_language::frontend_export::BundleSources {
                policy: &self.policy_src,
                event_schema: Some(&self.event_schema),
                providers: providers.as_deref(),
                macros: self.macros.as_deref(),
                action_schema: &self.schema_src,
                ids: self.ids.as_ref(),
                distincter: self.distincter.as_deref(),
            },
        );
        // Read with `get_mut`: indexing a JSON value mutably inserts the keys it misses.
        let policies = out
            .get_mut("stages")
            .and_then(|s| s.get_mut("cedarify"))
            .and_then(|c| c.get_mut("ok"))
            .and_then(|o| o.get_mut("policies"))
            .and_then(Json::as_array_mut);
        if let Some(policies) = policies {
            for p in policies {
                let id = p["id"].as_str().unwrap_or_default().to_string();
                p["spec"] = match decisions::crate_named_policy(&id, &p["est"]) {
                    Ok(spec) => json!({"ok": spec}),
                    Err(e) => json!({"error": e}),
                };
            }
        }
        let src = self.schema_src.strip_prefix('\u{FEFF}').unwrap_or(&self.schema_src);
        out["baseValidatorSchema"] = match cedar_policy::Schema::from_cedarschema_str(src) {
            Ok((schema, _)) => match schema::validator_schema(schema.as_ref(), &Default::default()) {
                Ok(j) => json!({"ok": j}),
                Err(e) => json!({"error": e}),
            },
            Err(e) => json!({"error": e.to_string()}),
        };
        let without_traces = Bundle { traces: Vec::new(), ..self.clone() };
        out["conformance"] = match self.lower() {
            Ok(lowered) => {
                out["validatorSchema"] =
                    match schema::validator_schema(lowered.cedar_schema().as_ref(), &Default::default()) {
                        Ok(j) => json!({"ok": j}),
                        Err(e) => json!({"error": e}),
                    };
                match without_traces.export(&lowered, None) {
                    Ok(o) => o.to_json(),
                    Err(e) => Outcome::rejected("export", &e).to_json(),
                }
            }
            Err((stage, message)) => Outcome::rejected(stage, &message).to_json(),
        };
        json!({"name": self.name, "frontend": out})
    }

    fn run(&self, engine: Option<&EngineFactory>) -> Outcome {
        let policies = match self.lower() {
            Ok(p) => p,
            Err((stage, message)) => return Outcome::rejected(stage, &message),
        };
        match self.export(&policies, engine) {
            Ok(o) => o,
            Err(e) => Outcome::rejected("export", &e),
        }
    }

    fn export(
        &self,
        policies: &LoweredPolicySet,
        engine: Option<&EngineFactory>,
    ) -> std::result::Result<Outcome, String> {
        let leaves = policies
            .nonrelativized_temporal_fields()
            .map(|f| formula(&f.condition.condition))
            .collect::<std::result::Result<Vec<Json>, String>>()?;
        let signatures = policies
            .event_signatures()
            .map(|s| schema::signature(&s, policies))
            .collect::<std::result::Result<Vec<Json>, String>>()?;
        let action_schema = schema::action_schema(policies)?;
        let (provider_decls, decls_skipped) =
            schema::provider_decls(self.provider_decls()?.as_ref(), policies)?;
        let (rules, provider_fields) = decisions::policies(policies)?;
        let result = Validator::new().validate(policies);
        let mut findings: Vec<Json> = result
            .validation_errors()
            .map(|e| {
                let code = match e {
                    ValidationError::Extension { code, .. } => code.to_string(),
                    _ => "cedar".to_string(),
                };
                json!({"code": code, "message": e.to_string(), "warning": false})
            })
            .collect();
        findings.extend(result.validation_warnings().map(|w| {
            let code = match w {
                ValidationWarning::Extension { code, .. } => code.to_string(),
                _ => "cedar".to_string(),
            };
            json!({"code": code, "message": w.to_string(), "warning": true})
        }));
        let (decisions, skipped) = if self.traces.is_empty() {
            (Json::Null, Json::Null)
        } else {
            let fresh = || match self.lower() {
                Ok(p) => p,
                Err(_) => unreachable!("the bundle lowered once"),
            };
            match decisions::export(policies, &fresh, &self.traces, &self.name, engine) {
                Ok(d) => (d, Json::Null),
                Err(e) => (Json::Null, Json::String(e)),
            }
        };
        Ok(Outcome::Lowered(json!({
            "schema": signatures, "maxWindow": limits(&self.event_schema).0,
            "maxHorizon": limits(&self.event_schema).1, "leaves": leaves,
            "actionSchema": action_schema, "providerDecls": provider_decls,
            "providerDeclsSkipped": decls_skipped, "policies": rules,
            "providers": provider_fields, "crateFindings": findings, "decisions": decisions,
            "decisionsSkipped": skipped,
        })))
    }
}

/// The interval a `<name> = <interval>` directive of the event-schema source
/// declares, in seconds, if it declares one.
fn directive(src: &str, name: &str) -> Option<i64> {
    for line in src.lines() {
        let line = line.split("//").next().unwrap_or("").trim();
        let Some(rest) = line.strip_prefix(name) else {
            continue;
        };
        let Some(rest) = rest.trim().strip_prefix('=') else {
            continue;
        };
        let rest = rest.trim();
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        let unit = rest[digits.len()..].trim();
        let Ok(amount) = digits.parse::<i64>() else {
            continue;
        };
        let factor = match unit {
            "s" => 1,
            "m" => 60,
            "h" => 3600,
            "d" => 86_400,
            _ => continue,
        };
        return Some(amount.saturating_mul(factor));
    }
    None
}

/// The `max_window` and `max_horizon` caps of the event-schema source, in
/// seconds, resolved as the crate resolves them (`EventSchema::limits`): the
/// horizon is the directive, or none; the window is the directive, else the
/// declared horizon, else 24h.
fn limits(src: &str) -> (i64, Option<i64>) {
    let window = directive(src, "max_window");
    let horizon = directive(src, "max_horizon");
    (window.or(horizon).unwrap_or(86_400), horizon)
}

// ─── Outcomes ────────────────────────────────────────────────────────────

enum Outcome {
    Rejected { stage: String, message: String },
    Lowered(Json),
}

impl Outcome {
    fn rejected(stage: &str, message: &str) -> Outcome {
        Outcome::Rejected {
            stage: stage.to_string(),
            message: message.to_string(),
        }
    }

    fn to_json(&self) -> Json {
        match self {
            Outcome::Rejected { stage, message } => {
                ctor("rejected", json!({"stage": stage, "message": message}))
            }
            Outcome::Lowered(l) => ctor("lowered", json!({"l": l})),
        }
    }
}

// ─── JSON values ─────────────────────────────────────────────────────────

/// A constructor applied to its named arguments, in Lean's derived encoding.
pub(crate) fn ctor(name: &str, args: Json) -> Json {
    let mut m = serde_json::Map::new();
    m.insert(name.to_string(), args);
    Json::Object(m)
}

/// A Cedar entity uid from a type path and an id.
pub(crate) fn uid(type_path: &[String], eid: &str) -> Result<Json, String> {
    let (id, path) = type_path
        .split_last()
        .ok_or_else(|| format!("empty entity type for `{eid}`"))?;
    Ok(json!({"ty": {"id": id, "path": path}, "eid": eid}))
}

fn window(w: &WithinSpec) -> Result<Json, String> {
    match w {
        WithinSpec::Concrete(i) => {
            let unit = match i.unit {
                TimeUnit::Seconds => "seconds",
                TimeUnit::Minutes => "minutes",
                TimeUnit::Hours => "hours",
                TimeUnit::Days => "days",
            };
            Ok(json!({"amount": i.amount, "unit": unit}))
        }
        WithinSpec::ParamRef(p) => Err(format!("unexpanded window parameter `?{p}`")),
    }
}

fn name(slot: &BinderSlot) -> Result<Json, String> {
    match slot {
        BinderSlot::Name(n) => Ok(json!(n)),
        BinderSlot::ParamRef(p) => Err(format!("unexpanded binder parameter `?{p}`")),
        BinderSlot::BinderRef(b) => Err(format!("unexpanded binder `${b}`")),
    }
}

fn binder(b: &TypedBinder) -> Result<Json, String> {
    let ty = match &b.ty {
        Type::Timepoint => json!("timepoint"),
        Type::Named(path) => ctor("named", json!({"path": path})),
    };
    Ok(json!({"name": name(&b.slot)?, "ty": ty}))
}

pub(crate) fn formula(c: &Condition) -> Result<Json, String> {
    Ok(match &c.kind {
        ConditionKind::And { left, right } => {
            ctor("and", json!({"φ": formula(left)?, "ψ": formula(right)?}))
        }
        ConditionKind::Not { inner } => ctor("not", json!({"φ": formula(inner)?})),
        ConditionKind::Formerly { within, body } => {
            ctor("formerly", json!({"w": window(within)?, "φ": formula(body)?}))
        }
        ConditionKind::Previous { within, body } => {
            ctor("previous", json!({"w": window(within)?, "φ": formula(body)?}))
        }
        ConditionKind::Since { left, within, right } => ctor(
            "since",
            json!({"φ": formula(left)?, "w": window(within)?, "ψ": formula(right)?}),
        ),
        ConditionKind::Predicate(p) => {
            let args: Result<Vec<Json>, String> = p
                .args
                .iter()
                .map(|a| Ok(json!([a.field_path(), term(&a.value)?])))
                .collect();
            ctor("pred", json!({"action": uid(&p.namespace, &p.action)?, "kind": p.kind, "args": args?}))
        }
        ConditionKind::Comparison { op, left, right } => {
            let op = match op {
                CmpOp::Eq => "eq",
                CmpOp::NotEq => "ne",
                CmpOp::Lt => "lt",
                CmpOp::Le => "le",
                CmpOp::Gt => "gt",
                CmpOp::Ge => "ge",
            };
            ctor("cmp", json!({"op": op, "l": term(left)?, "r": term(right)?}))
        }
        ConditionKind::Exists { var, body } => {
            ctor("exist", json!({"x": binder(var)?, "φ": formula(body)?}))
        }
        ConditionKind::Tp { var } => ctor("tp", json!({"x": name(var)?})),
        ConditionKind::Or { .. } => return Err("internal disjunction in an authored leaf".into()),
        ConditionKind::Call(call) => return Err(format!("unexpanded macro call `{}`", call.name)),
        ConditionKind::SigilRef { name, .. } => {
            return Err(format!("unexpanded condition sigil `{name}`"));
        }
        ConditionKind::Refine { .. } => return Err("unfolded field refinement".into()),
    })
}

fn term(t: &Term) -> Result<Json, String> {
    Ok(match t {
        Term::Entity { ty, id } => {
            let path: Vec<String> = ty.split("::").map(str::to_string).collect();
            ctor("entity", json!({"uid": uid(&path, id)?}))
        }
        Term::Integer(i) => ctor("long", json!({"i": i})),
        Term::Decimal(s) => ctor("decimal", json!({"text": s})),
        Term::String(s) => ctor("string", json!({"s": s})),
        Term::Bool(b) => ctor("bool", json!({"b": b})),
        Term::ContextField(path) => ctor("context", json!({"path": path})),
        Term::ScopeField(path) => {
            let (root, rest) = path.split_first().ok_or("empty scope field")?;
            if root != "principal" && root != "resource" {
                return Err(format!("scope field rooted at `{root}`"));
            }
            ctor("scope", json!({"root": root, "path": rest}))
        }
        Term::Var(x) => ctor("var", json!({"x": x})),
        Term::Wildcard => json!("wildcard"),
        Term::Array(_) => return Err("array constant".into()),
        Term::Agg(a) => ctor("agg", json!({"a": aggregate(a)?})),
        Term::Arith { op, left, right } => {
            let op = match op {
                ArithOp::Add => "add",
                ArithOp::Sub => "sub",
                ArithOp::Mul => "mul",
            };
            ctor("arith", json!({"op": op, "l": term(left)?, "r": term(right)?}))
        }
        Term::ParamRef(p) => return Err(format!("unexpanded parameter `?{p}`")),
        Term::BinderRef(b) => return Err(format!("unexpanded binder `${b}`")),
    })
}

fn aggregate(a: &AggExpr) -> Result<Json, String> {
    let domain = |vars: &[TypedBinder]| -> Result<Vec<Json>, String> { vars.iter().map(binder).collect() };
    Ok(match &a.kind {
        AggExprKind::Count { for_vars, body } => {
            ctor("count", json!({"domain": domain(for_vars)?, "body": formula(body)?}))
        }
        AggExprKind::Sum { bound_var, for_vars, body } => ctor(
            "sum",
            json!({"summand": name(bound_var)?, "domain": domain(for_vars)?, "body": formula(body)?}),
        ),
        AggExprKind::Call(call) => return Err(format!("unexpanded aggregate macro `{}`", call.name)),
    })
}
