//! Schema-coverage analysis over the corpus test suites.
//!
//! Motivation: the corpora vary *policies* far more than they vary the
//! *schemas* those policies are validated against. Several past bugs were
//! schema-shape-dependent and sat outside every corpus schema (see commits
//! ded81043 — datetime/ipaddr fields and deep nested paths "unreachable by
//! the current corpus" — and f29b808b, b4a7e10e). This harness quantifies
//! that axis: it resolves the *effective* schema of every corpus case
//! (per-case `schema.cedarschema`, else the corpus's shared fallback,
//! mirroring each harness), extracts structural features from each distinct
//! schema, and reports which schema shapes each corpus does and does not
//! exercise.
//!
//! The test itself only asserts liveness (cases were found, schemas parse)
//! so it stays green while gaps are being filled; the report is the product.
//! Because it produces a report rather than guarding behavior — and its corpus
//! walk costs ~40s — it is `#[ignore]`d so it does not run on every build. Run
//! it on demand:
//!
//! ```bash
//! cargo test --test schema_coverage -- --ignored --nocapture
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use serde_json::Value;

// ─── Corpus walking ──────────────────────────────────────────────────

/// One corpus case and the schema text it is actually tested against.
struct Case {
    corpus: &'static str,
    #[allow(dead_code)]
    name: String,
    schema_src: String,
}

fn tests_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests")
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()))
}

/// Directory-per-case corpora: each case dir may carry `schema.cedarschema`,
/// otherwise `fallback` applies (mirrors the harnesses' resolution).
fn collect_dir_corpus(
    corpus: &'static str,
    dir: &Path,
    fallback: Option<&str>,
    out: &mut Vec<Case>,
) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries {
        let entry = entry.unwrap();
        if !entry.file_type().unwrap().is_dir() {
            continue;
        }
        let case_dir = entry.path();
        let per_case = case_dir.join("schema.cedarschema");
        let schema_src = if per_case.exists() {
            read(&per_case)
        } else if let Some(shared) = fallback {
            shared.to_string()
        } else {
            continue; // no schema, nothing to analyze
        };
        out.push(Case {
            corpus,
            name: entry.file_name().to_string_lossy().into_owned(),
            schema_src,
        });
    }
}

/// Flat-file corpora (cedar_only): `<hash>.cedar` paired with
/// `<hash>.cedarschema`.
fn collect_flat_corpus(corpus: &'static str, dir: &Path, out: &mut Vec<Case>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("cedar") {
            continue;
        }
        let schema_path = path.with_extension("cedarschema");
        if !schema_path.exists() {
            continue;
        }
        out.push(Case {
            corpus,
            name: path.file_stem().unwrap().to_string_lossy().into_owned(),
            schema_src: read(&schema_path),
        });
    }
}

fn collect_all_cases() -> Vec<Case> {
    let root = tests_root();
    let temporal_shared = read(&root.join("passing/temporal_only/shared_schema.cedarschema"));
    let provider_shared = read(&root.join("passing/provider_only/shared_schema.cedarschema"));

    let mut cases = Vec::new();
    collect_flat_corpus(
        "cedar_fuzz",
        &root.join("passing/cedar_only/corpus_fuzz"),
        &mut cases,
    );
    collect_dir_corpus(
        "cedar_hand",
        &root.join("passing/cedar_only/corpus_handwritten"),
        None,
        &mut cases,
    );
    collect_dir_corpus(
        "temporal",
        &root.join("passing/temporal_only/corpus"),
        Some(&temporal_shared),
        &mut cases,
    );
    collect_dir_corpus(
        "provider",
        &root.join("passing/provider_only/corpus"),
        Some(&provider_shared),
        &mut cases,
    );
    collect_dir_corpus(
        "macros",
        &root.join("passing/macros/corpus"),
        Some(&temporal_shared),
        &mut cases,
    );
    collect_dir_corpus(
        "mixed",
        &root.join("passing/mixed/corpus"),
        Some(&temporal_shared),
        &mut cases,
    );
    collect_dir_corpus(
        "xfail",
        &root.join("expected_failures/corpus"),
        Some(&temporal_shared),
        &mut cases,
    );
    cases
}

// ─── Feature extraction ──────────────────────────────────────────────

/// The structural features of one schema, as a set of feature tags.
///
/// Feature tags are the unit of the coverage report: a schema either
/// exhibits a tag or not, and a corpus covers a tag if at least one of its
/// cases' effective schemas exhibits it.
#[derive(Default)]
struct Features(BTreeSet<&'static str>);

/// All feature tags the extractor can emit, in report order. Kept explicit
/// so tags with ZERO coverage anywhere still show up in the report — absent
/// rows are the finding, not an omission.
const ALL_FEATURES: &[&str] = &[
    // Scale
    "actions: exactly 1",
    "actions: 2-5",
    "actions: 6+",
    "entity types: 3+",
    "namespace: named (non-empty)",
    "namespaces: 2+ in one schema",
    "common types declared",
    "action without appliesTo (pure group)",
    // Scope shape
    "action with multiple principal types",
    "action with multiple resource types",
    "action with empty/no context",
    "context: declared as type reference",
    "context ref: multi-hop alias chain",
    "context ref: crosses namespace boundary",
    "context ref: optional attribute in referenced record",
    "context ref: sibling references in referenced record",
    // Entity shape
    "entity type with attributes",
    "entity hierarchy (memberOfTypes)",
    // Context attribute types
    "context attr: Long",
    "context attr: String",
    "context attr: Boolean",
    "context attr: Set",
    "context attr: entity reference",
    "context attr: extension datetime",
    "context attr: extension ipaddr",
    "context attr: extension decimal",
    "context attr: extension duration",
    "context attr: optional (required=false)",
    // Nesting (the ded81043 / f29b808b axis)
    "context nesting: depth >= 2 (record in context)",
    "context nesting: depth >= 3",
];

fn extract_features(schema_json: &Value) -> Features {
    let mut f = Features::default();
    let Some(namespaces) = schema_json.as_object() else {
        return f;
    };

    // Resolver: common-type definitions by bare and namespace-qualified
    // name. The cedarschema->JSON conversion renders type-name references
    // (common types, entity types, and sometimes primitives) as
    // `EntityOrCommon`, so classification must resolve names through this
    // map before deciding what a reference is.
    let mut common_types: BTreeMap<String, &Value> = BTreeMap::new();
    // Definition-site-aware view: per-namespace maps, for chain walking with
    // Cedar's resolution semantics (each hop resolves relative to the
    // namespace where that definition is written).
    let mut per_ns: BTreeMap<String, BTreeMap<String, &Value>> = BTreeMap::new();
    for (ns_name, ns) in namespaces {
        if let Some(cts) = ns.get("commonTypes").and_then(Value::as_object) {
            for (name, def) in cts {
                common_types.insert(name.clone(), def);
                if !ns_name.is_empty() {
                    common_types.insert(format!("{ns_name}::{name}"), def);
                }
                per_ns
                    .entry(ns_name.clone())
                    .or_default()
                    .insert(name.clone(), def);
            }
        }
    }
    let resolver = Resolver {
        common_types,
        per_ns,
    };

    let mut action_count = 0usize;
    let mut entity_count = 0usize;

    if namespaces.len() >= 2 {
        f.0.insert("namespaces: 2+ in one schema");
    }

    for (ns_name, ns) in namespaces {
        if !ns_name.is_empty() {
            f.0.insert("namespace: named (non-empty)");
        }
        if ns
            .get("commonTypes")
            .and_then(Value::as_object)
            .is_some_and(|m| !m.is_empty())
        {
            f.0.insert("common types declared");
        }
        if let Some(entity_types) = ns.get("entityTypes").and_then(Value::as_object) {
            entity_count += entity_types.len();
            for et in entity_types.values() {
                if et
                    .get("shape")
                    .and_then(|s| s.get("attributes"))
                    .and_then(Value::as_object)
                    .is_some_and(|a| !a.is_empty())
                {
                    f.0.insert("entity type with attributes");
                }
                if et
                    .get("memberOfTypes")
                    .and_then(Value::as_array)
                    .is_some_and(|m| !m.is_empty())
                {
                    f.0.insert("entity hierarchy (memberOfTypes)");
                }
            }
        }
        if let Some(actions) = ns.get("actions").and_then(Value::as_object) {
            action_count += actions.len();
            for action in actions.values() {
                let Some(applies) = action.get("appliesTo") else {
                    f.0.insert("action without appliesTo (pure group)");
                    f.0.insert("action with empty/no context");
                    continue;
                };
                // Cedar's JSON export renders an appliesTo-less action (a
                // pure group) as an appliesTo with EMPTY principal/resource
                // type lists — such an action can never receive a request.
                let list_empty = |key: &str| {
                    applies
                        .get(key)
                        .and_then(Value::as_array)
                        .is_none_or(|a| a.is_empty())
                };
                if list_empty("principalTypes") && list_empty("resourceTypes") {
                    f.0.insert("action without appliesTo (pure group)");
                }
                for (key, tag) in [
                    ("principalTypes", "action with multiple principal types"),
                    ("resourceTypes", "action with multiple resource types"),
                ] {
                    if applies
                        .get(key)
                        .and_then(Value::as_array)
                        .is_some_and(|a| a.len() > 1)
                    {
                        f.0.insert(tag);
                    }
                }
                // The context may itself be a common-type reference;
                // resolve before reading attributes. The unresolved
                // (reference) spelling is a distinct schema shape: grafting
                // passes must inline it (see schema_augment), so track it.
                // In the JSON rendering a reference appears as the bare
                // type name in the `type` field: `{"type": "ReadCtx"}`.
                let raw_ctx = applies.get("context");
                if let Some(raw) = raw_ctx
                    && let Some(info) = resolver.context_chain_info(ns_name, raw)
                {
                    f.0.insert("context: declared as type reference");
                    if info.hops >= 2 {
                        f.0.insert("context ref: multi-hop alias chain");
                    }
                    if info.crosses_namespace {
                        f.0.insert("context ref: crosses namespace boundary");
                    }
                    // Shape facts about the RESOLVED record: optional
                    // attributes and sibling type references inside a
                    // referenced context are load-bearing for the grafting
                    // passes' inlining (required-flag preservation;
                    // per-chain vs global substitution budgets).
                    let resolved = resolver.resolve(raw);
                    if let Some(attrs) = resolved.get("attributes").and_then(Value::as_object) {
                        if attrs
                            .values()
                            .any(|a| a.get("required") == Some(&Value::Bool(false)))
                        {
                            f.0.insert("context ref: optional attribute in referenced record");
                        }
                        let sibling_refs = attrs
                            .values()
                            .filter(|a| {
                                // Attribute-position references render as
                                // EntityOrCommon nodes; context position as
                                // bare type names. Accept both.
                                let name = match a.get("type").and_then(Value::as_str) {
                                    Some("EntityOrCommon") => a.get("name").and_then(Value::as_str),
                                    other => other,
                                };
                                name.is_some_and(|t| resolver.common_types.contains_key(t))
                            })
                            .count();
                        if sibling_refs >= 2 {
                            f.0.insert("context ref: sibling references in referenced record");
                        }
                    }
                }
                let ctx = raw_ctx.map(|c| resolver.resolve(c));
                let attrs = ctx
                    .and_then(|c| c.get("attributes"))
                    .and_then(Value::as_object)
                    .filter(|a| !a.is_empty());
                match attrs {
                    None => {
                        f.0.insert("action with empty/no context");
                    }
                    Some(attrs) => {
                        let mut max_depth = 0usize;
                        for attr in attrs.values() {
                            if attr.get("required") == Some(&Value::Bool(false)) {
                                f.0.insert("context attr: optional (required=false)");
                            }
                            walk_type(attr, 1, &mut max_depth, &mut f, &resolver);
                        }
                        if max_depth >= 2 {
                            f.0.insert("context nesting: depth >= 2 (record in context)");
                        }
                        if max_depth >= 3 {
                            f.0.insert("context nesting: depth >= 3");
                        }
                    }
                }
            }
        }
    }

    f.0.insert(match action_count {
        1 => "actions: exactly 1",
        2..=5 => "actions: 2-5",
        _ => "actions: 6+",
    });
    if entity_count >= 3 {
        f.0.insert("entity types: 3+");
    }
    f
}

/// Resolves `EntityOrCommon` name references to common-type definitions.
struct Resolver<'a> {
    common_types: BTreeMap<String, &'a Value>,
    /// Definitions grouped by the namespace they are written in, for
    /// definition-site-aware chain walking (`context_chain_info`).
    per_ns: BTreeMap<String, BTreeMap<String, &'a Value>>,
}

/// Shape facts about one context reference chain.
struct ChainInfo {
    hops: usize,
    crosses_namespace: bool,
}

impl<'a> Resolver<'a> {
    /// Follow a context type-reference chain with CEDAR's resolution
    /// semantics: each hop's name resolves relative to the namespace where
    /// the CURRENT definition is written (start: the action's namespace),
    /// falling back to the empty namespace; an explicit `Ns::T`
    /// qualification wins. Returns `None` if the context is not a
    /// reference; hop-count and whether any hop's definition lives in a
    /// namespace different from the action's otherwise.
    fn context_chain_info(&self, action_ns: &str, ctx: &'a Value) -> Option<ChainInfo> {
        let ref_name = |ty: &'a Value| -> Option<String> {
            let t = ty.get("type").and_then(Value::as_str)?;
            let name = if t == "EntityOrCommon" {
                ty.get("name").and_then(Value::as_str)?
            } else {
                t
            };
            Some(name.to_string())
        };
        // (definition namespace, definition value) for a name referenced
        // from within namespace `from_ns`.
        let lookup = |from_ns: &str, name: &str| -> Option<(String, &'a Value)> {
            if let Some((ns, ident)) = name.rsplit_once("::") {
                return self
                    .per_ns
                    .get(ns)
                    .and_then(|m| m.get(ident))
                    .map(|d| (ns.to_string(), *d));
            }
            if let Some(d) = self.per_ns.get(from_ns).and_then(|m| m.get(name)) {
                return Some((from_ns.to_string(), *d));
            }
            self.per_ns
                .get("")
                .and_then(|m| m.get(name))
                .map(|d| (String::new(), *d))
        };

        let first = ref_name(ctx)?;
        let (mut def_ns, mut def) = lookup(action_ns, &first)?;
        let mut info = ChainInfo {
            hops: 1,
            crosses_namespace: def_ns != action_ns,
        };
        for _ in 0..32 {
            let Some(next) = ref_name(def) else {
                return Some(info); // terminal structural type
            };
            let Some((ns, d)) = lookup(&def_ns, &next) else {
                return Some(info); // unresolvable (or an entity name) — stop
            };
            info.hops += 1;
            info.crosses_namespace |= ns != action_ns;
            def_ns = ns;
            def = d;
        }
        Some(info)
    }

    /// Follow type references through the common-type map until hitting a
    /// structural type (or an unknown name, i.e. an entity type). References
    /// appear in two JSON spellings: `EntityOrCommon` nodes (attribute
    /// positions) and bare type names in the `type` field (context
    /// positions, e.g. `{"type": "ReadCtx"}`). Bounded to guard against
    /// reference cycles.
    fn resolve(&self, mut ty: &'a Value) -> &'a Value {
        for _ in 0..16 {
            let type_name = ty.get("type").and_then(Value::as_str).unwrap_or("");
            let ref_name = if type_name == "EntityOrCommon" {
                ty.get("name").and_then(Value::as_str).unwrap_or("")
            } else {
                type_name
            };
            match self.common_types.get(ref_name) {
                Some(def) => ty = def,
                None => return ty,
            }
        }
        ty
    }
}

/// Recursively walk a JSON-schema type node, tagging attribute types and
/// tracking record-nesting depth. `depth` is the record depth of the node's
/// enclosing attributes (context top level = 1).
fn walk_type(
    ty: &Value,
    depth: usize,
    max_depth: &mut usize,
    f: &mut Features,
    resolver: &Resolver<'_>,
) {
    *max_depth = (*max_depth).max(depth);
    let ty = resolver.resolve(ty);
    let type_name = ty.get("type").and_then(Value::as_str).unwrap_or("");
    match type_name {
        "Long" => {
            f.0.insert("context attr: Long");
        }
        "String" => {
            f.0.insert("context attr: String");
        }
        "Boolean" | "Bool" => {
            f.0.insert("context attr: Boolean");
        }
        "Set" => {
            f.0.insert("context attr: Set");
            if let Some(el) = ty.get("element") {
                walk_type(el, depth, max_depth, f, resolver);
            }
        }
        "Record" => {
            if let Some(attrs) = ty.get("attributes").and_then(Value::as_object) {
                for attr in attrs.values() {
                    if attr.get("required") == Some(&Value::Bool(false)) {
                        f.0.insert("context attr: optional (required=false)");
                    }
                    walk_type(attr, depth + 1, max_depth, f, resolver);
                }
            }
        }
        "Extension" => tag_extension(ty.get("name").and_then(Value::as_str).unwrap_or(""), f),
        "Entity" => {
            f.0.insert("context attr: entity reference");
        }
        // An unresolved EntityOrCommon: not a common type, so classify by
        // name — primitives/extensions render this way in some positions,
        // anything else is an entity-type reference.
        "EntityOrCommon" => match ty.get("name").and_then(Value::as_str).unwrap_or("") {
            "Long" => {
                f.0.insert("context attr: Long");
            }
            "String" => {
                f.0.insert("context attr: String");
            }
            "Bool" | "Boolean" => {
                f.0.insert("context attr: Boolean");
            }
            name @ ("datetime" | "ipaddr" | "decimal" | "duration") => tag_extension(name, f),
            _ => {
                f.0.insert("context attr: entity reference");
            }
        },
        _ => {}
    }
}

fn tag_extension(name: &str, f: &mut Features) {
    match name {
        "datetime" => {
            f.0.insert("context attr: extension datetime");
        }
        "ipaddr" => {
            f.0.insert("context attr: extension ipaddr");
        }
        "decimal" => {
            f.0.insert("context attr: extension decimal");
        }
        "duration" => {
            f.0.insert("context attr: extension duration");
        }
        _ => {}
    }
}

// ─── The analysis test ───────────────────────────────────────────────

const CORPORA: &[&str] = &[
    "cedar_fuzz",
    "cedar_hand",
    "temporal",
    "provider",
    "macros",
    "mixed",
    "xfail",
];

#[test]
#[ignore = "coverage report, not an assertion; run on demand with --ignored --nocapture"]
fn schema_coverage_report() {
    let cases = collect_all_cases();

    // Dedup schema texts and parse each distinct schema once.
    let mut distinct: BTreeMap<&str, Result<Features, String>> = BTreeMap::new();
    for case in &cases {
        distinct.entry(&case.schema_src).or_insert_with(|| {
            cedar_policy::SchemaFragment::from_cedarschema_str(&case.schema_src)
                .map_err(|e| e.to_string())
                .and_then(|(frag, _warnings)| frag.to_json_string().map_err(|e| e.to_string()))
                .map(|json| {
                    extract_features(&serde_json::from_str::<Value>(&json).expect("valid JSON"))
                })
        });
    }

    // Per-corpus tallies: cases, distinct schemas, parse failures,
    // and per-feature case counts.
    let mut corpus_cases: BTreeMap<&str, usize> = BTreeMap::new();
    let mut corpus_schemas: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut parse_failures: BTreeMap<&str, usize> = BTreeMap::new();
    let mut feature_cases: BTreeMap<&str, BTreeMap<&str, usize>> = BTreeMap::new();
    let mut feature_schemas: BTreeMap<&str, usize> = BTreeMap::new();

    for (src, features) in &distinct {
        if let Ok(f) = features {
            for tag in &f.0 {
                *feature_schemas.entry(tag).or_default() += 1;
            }
        }
        let _ = src;
    }
    for case in &cases {
        *corpus_cases.entry(case.corpus).or_default() += 1;
        corpus_schemas
            .entry(case.corpus)
            .or_default()
            .insert(&case.schema_src);
        match &distinct[case.schema_src.as_str()] {
            Ok(f) => {
                for tag in &f.0 {
                    *feature_cases
                        .entry(tag)
                        .or_default()
                        .entry(case.corpus)
                        .or_default() += 1;
                }
            }
            Err(_) => *parse_failures.entry(case.corpus).or_default() += 1,
        }
    }

    // ── Report ──
    println!("\n=== SCHEMA COVERAGE REPORT ===\n");
    println!("Per corpus (cases / distinct effective schemas / schema parse failures):");
    for corpus in CORPORA {
        println!(
            "  {corpus:<12} cases={:<6} distinct_schemas={:<6} parse_failures={}",
            corpus_cases.get(corpus).unwrap_or(&0),
            corpus_schemas.get(corpus).map_or(0, BTreeSet::len),
            parse_failures.get(corpus).unwrap_or(&0),
        );
    }

    let dogwood_corpora = &CORPORA[2..]; // everything but the two cedar_only sets
    println!("\nFeature coverage (cases whose effective schema exhibits the feature).");
    println!("Columns: distinct schemas with feature, then per-corpus case counts.\n");
    println!(
        "  {:<48} {:>7} | {}",
        "feature",
        "schemas",
        dogwood_corpora
            .iter()
            .map(|c| format!("{c:>9}"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    let mut dogwood_gaps: Vec<&str> = Vec::new();
    for tag in ALL_FEATURES {
        let per_corpus = feature_cases.get(tag);
        let counts: Vec<String> = dogwood_corpora
            .iter()
            .map(|c| {
                format!(
                    "{:>9}",
                    per_corpus.and_then(|m| m.get(c)).copied().unwrap_or(0)
                )
            })
            .collect();
        let dogwood_total: usize = dogwood_corpora
            .iter()
            .map(|c| per_corpus.and_then(|m| m.get(c)).copied().unwrap_or(0))
            .sum();
        if dogwood_total == 0 {
            dogwood_gaps.push(tag);
        }
        println!(
            "  {:<48} {:>7} | {}",
            tag,
            feature_schemas.get(tag).copied().unwrap_or(0),
            counts.join(" ")
        );
    }

    println!("\nSchema features with ZERO coverage across all Dogwood-dialect corpora");
    println!("(temporal/provider/macros/mixed/xfail — the cedar_only fuzz corpus is");
    println!("excluded because it never exercises Dogwood lowering paths):");
    if dogwood_gaps.is_empty() {
        println!("  (none)");
    } else {
        for tag in &dogwood_gaps {
            println!("  - {tag}");
        }
    }

    // Event-schema axis: overrides are the only variation, count them.
    let event_overrides = walkdir_count(&tests_root(), "event.dwschema");
    println!(
        "\nEvent-schema axis: {event_overrides} `event.dwschema` override(s) in tests/ \
         (all other cases run the single default event schema)."
    );

    // ── Liveness guardrails (in the spirit of 9252687a): the report must
    // actually be measuring something. Analysis findings are NOT asserted.
    for corpus in CORPORA {
        assert!(
            corpus_cases.get(corpus).copied().unwrap_or(0) > 0,
            "corpus '{corpus}' contributed no cases — walker or layout broke"
        );
    }
    let total_failures: usize = parse_failures.values().sum();
    let failure_rate = total_failures as f64 / cases.len() as f64;
    assert!(
        failure_rate < 0.01,
        "{total_failures}/{} effective schemas failed to parse — schema resolution \
         is likely mis-mirroring a harness",
        cases.len()
    );
}

/// Count files with the given name anywhere under `root`.
fn walkdir_count(root: &Path, file_name: &str) -> usize {
    let mut count = 0;
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.file_name().and_then(|n| n.to_str()) == Some(file_name) {
                count += 1;
            }
        }
    }
    count
}
