//! Cedar-only test harness.
//!
//! - `handwritten_parse_and_validate`: 32 handwritten Cedar policies —
//!   `LoweredPolicySet::from_str` + `Validator::validate`.
//! - `corpus_fuzz_parse_and_span`: 7,467 fuzz-generated policies — empty-schema
//!   `LoweredPolicySet::from_str` acceptance plus differential leaf/all-node
//!   span checks against Cedar's own parse.
//! - `corpus_fuzz_validate_and_authorize`: over one corpus walk, each policy is
//!   lowered **once** against its real paired schema and then fed to two
//!   independent checks — `shouldValidate=true` cases go through
//!   [`dogwood_language::Validator`], and cases with a manifest + entities have
//!   their lowered `as_cedar()` decisions cross-validated against Cedar's own
//!   parse of the same source. Sharing the lowering avoids doing the dominant
//!   cost of this suite twice.
//!
//! Pure-Cedar cases build the action schema with
//! [`dogwood_language::PolicySchema::from_cedarschema_str`] paired with the DEFAULT service
//! schema ([`dogwood_language::ServiceSchema::defaults`]) and lower policies with
//! [`dogwood_language::LoweredPolicySet::from_str`], then validate with
//! [`dogwood_language::Validator`].

use cedar_policy_core::ast::{Expr, ExprKind, PolicySet};
use dogwood_language::{Error, LoweredPolicySet, PolicySchema, ServiceSchema, Validator};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

const MAX_KNOWN_INVALID: usize = 51;

/// The `corpus_fuzz/` directory shared by every fuzz-corpus test.
fn corpus_fuzz_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing/cedar_only/corpus_fuzz")
}

#[test]
fn handwritten_parse_and_validate() {
    let root =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing/cedar_only/corpus_handwritten");
    let mut failures = Vec::new();
    let mut passed = 0usize;

    let mut entries: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().map(|t| t.is_dir()).unwrap_or(false))
        .collect();
    entries.sort_by_key(|e| e.file_name());

    for entry in entries {
        let dir = entry.path();
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        let schema_path = dir.join("schema.cedarschema");
        if !schema_path.exists() {
            continue;
        }

        let mut policy_paths: Vec<_> = std::fs::read_dir(&dir)
            .unwrap()
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| {
                p.extension().and_then(|e| e.to_str()) == Some("dw")
                    && p.file_name()
                        .and_then(|n| n.to_str())
                        .is_some_and(|n| n.starts_with("policy_"))
            })
            .collect();
        policy_paths.sort();
        if policy_paths.is_empty() {
            continue;
        }

        let policy_src = policy_paths
            .iter()
            .map(|p| std::fs::read_to_string(p).unwrap())
            .collect::<Vec<_>>()
            .join("\n");
        let schema_src = std::fs::read_to_string(&schema_path).unwrap();

        // Pure-Cedar case: DEFAULT event schema, no providers.
        let service = ServiceSchema::defaults();
        let policy_schema = match PolicySchema::from_cedarschema_str(&schema_src) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!("{name}: {e:?}"));
                continue;
            }
        };
        let policies = match LoweredPolicySet::from_str(&policy_src, &service, &policy_schema) {
            Ok(p) => p,
            Err(e) => {
                failures.push(format!("{name}: {e:?}"));
                continue;
            }
        };
        let result = Validator::new().validate(&policies);
        if !result.validation_passed() {
            let errs: Vec<_> = result.validation_errors().map(|e| e.to_string()).collect();
            failures.push(format!("{name}: {}", errs.join("\n  ")));
        } else {
            passed += 1;
        }
    }

    eprintln!("handwritten: {passed} passed, {} failed", failures.len());
    assert!(
        passed > 0,
        "no cases were tested — check that corpus/ contains policy_*.dw files"
    );
    assert!(
        failures.is_empty(),
        "failures:\n\n{}",
        failures.join("\n\n")
    );
}

// ===========================================================================
// Regime A — empty-schema corpus checks (parse-acceptance + span differential)
//
// `corpus_fuzz_parse` and the two span-differential asserts all lower each
// corpus policy against an *empty* action schema (spans and parse-acceptance
// are schema-independent; the real schema would only drop cases). They are
// merged here into one parallelized walk so each case is lowered against the
// empty schema — and parsed with Cedar — exactly once, feeding three checks:
//
//   * parse-acceptance  — `Err(Error::Parse(..))` is a known-invalid, tallied
//     against `MAX_KNOWN_INVALID`.
//   * leaf-span match   — content-keyed leaf spans equal Cedar's (100%).
//   * all-node match     — kind-keyed spans over every node equal Cedar's (100%).
//
// This subsumes the former `tests/span_differential.rs` binary. Its two
// `#[ignore]`d measurement helpers (categorized divergence breakdowns for
// exploratory runs) were not carried over; the summary line and the on-failure
// divergence report below cover the regression path. Recover the breakdowns
// from git history (`tests/span_differential.rs`) if ever needed.
// ===========================================================================

/// Lower `src` through Dogwood against an **empty** action schema — the
/// schema-independent lowering shared by every regime-A check. `None` if the
/// parse/lower fails. The loc-bearing Cedar `PolicySet` is reached via
/// `.as_cedar().as_ref()`.
fn lower_ours_empty(src: &str) -> Option<LoweredPolicySet> {
    let service = ServiceSchema::defaults();
    let policy_schema = PolicySchema::from_cedarschema_str("").ok()?;
    LoweredPolicySet::from_str(src, &service, &policy_schema).ok()
}

/// A leaf's identity for content-keyed comparison: which kind of leaf, and its
/// rendered content (so we compare *the same* `context`/`5`/`.foo` leaf's span
/// on both sides, independent of tree position).
type LeafKey = (&'static str, String);

/// Collect `(leaf-key, (start, end))` for every leaf in a policy set's
/// condition ASTs. A leaf with no source location is skipped.
fn leaf_spans(pset: &PolicySet) -> Vec<(LeafKey, (usize, usize))> {
    let mut out = Vec::new();
    for policy in pset.policies() {
        collect_leaves(&policy.condition(), &mut out);
    }
    out.sort();
    out
}

fn collect_leaves(e: &Expr, out: &mut Vec<(LeafKey, (usize, usize))>) {
    for sub in e.subexpressions() {
        let key: Option<LeafKey> = match sub.expr_kind() {
            ExprKind::Lit(lit) => Some(("lit", lit.to_string())),
            ExprKind::Var(v) => Some(("var", v.to_string())),
            ExprKind::Slot(s) => Some(("slot", s.to_string())),
            ExprKind::GetAttr { attr, .. } => Some(("attr", attr.to_string())),
            _ => None,
        };
        if let Some(key) = key
            && let Some(loc) = sub.source_loc()
        {
            out.push((key, (loc.start(), loc.end())));
        }
    }
}

/// A structural discriminant for *every* `ExprKind`, so interior nodes can be
/// compared too — keyed by kind (not content), since interior nodes have no
/// single token to render; the span is what we compare.
fn node_kind(e: &Expr) -> &'static str {
    match e.expr_kind() {
        ExprKind::Lit(_) => "lit",
        ExprKind::Var(_) => "var",
        ExprKind::Slot(_) => "slot",
        ExprKind::Unknown(_) => "unknown",
        ExprKind::If { .. } => "if",
        ExprKind::And { .. } => "and",
        ExprKind::Or { .. } => "or",
        ExprKind::UnaryApp { .. } => "unary",
        ExprKind::BinaryApp { .. } => "binary",
        ExprKind::ExtensionFunctionApp { .. } => "extfn",
        ExprKind::GetAttr { .. } => "getattr",
        ExprKind::HasAttr { .. } => "hasattr",
        ExprKind::Like { .. } => "like",
        ExprKind::Is { .. } => "is",
        ExprKind::Set(_) => "set",
        ExprKind::Record(_) => "record",
        #[allow(unreachable_patterns)]
        _ => "other",
    }
}

/// Collect `(kind-discriminant, (start, end))` for **every** node (interior
/// included) in a policy set's condition ASTs. A node with no source location
/// is skipped.
fn node_spans(pset: &PolicySet) -> Vec<(&'static str, (usize, usize))> {
    let mut out = Vec::new();
    for policy in pset.policies() {
        for sub in policy.condition().subexpressions() {
            if let Some(loc) = sub.source_loc() {
                out.push((node_kind(sub), (loc.start(), loc.end())));
            }
        }
    }
    out.sort();
    out
}

/// Per-case result of the regime-A (empty-schema) checks. Produced
/// independently per case (no shared state) so cases run on worker threads,
/// then folded serially in corpus order.
#[derive(Default)]
struct EmptySchemaOutcome {
    /// `Some(msg)` = a parse rejection (`Error::Parse`); counts toward the
    /// known-invalid threshold. `None` = parsed (or a non-parse error, which
    /// the acceptance check treats as passed, matching the original).
    parse_failure: Option<String>,
    /// Whether this case's manifest says `shouldValidate=true` (for the
    /// known-invalid breakdown line).
    should_validate: bool,
    /// Cedar leaves we did not reproduce: `(case-stem, key, span)`. The stem is
    /// carried so the on-failure divergence report names the offending corpus
    /// file (as the pre-consolidation span test did). Empty = full match or case
    /// not comparable (Cedar/our parse failed).
    leaf_divergences: Vec<(String, LeafKey, (usize, usize))>,
    /// Total Cedar leaves compared (0 if not comparable).
    leaf_total: usize,
    leaf_agreed: usize,
    /// All-node agreement over comparable cases.
    node_total: usize,
    node_agreed: usize,
}

/// Run every empty-schema check for one corpus case. Pure and thread-safe.
fn run_empty_schema_case(path: &Path) -> EmptySchemaOutcome {
    let mut out = EmptySchemaOutcome::default();
    let src = std::fs::read_to_string(path).unwrap();

    // ---- parse-acceptance (empty schema) ----
    let ours_lowered = match LoweredPolicySet::from_str(
        &src,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str("").expect("empty Cedar schema is valid"),
    ) {
        Ok(p) => Some(p),
        Err(Error::Parse(errs)) => {
            let msgs: Vec<_> = errs.iter().map(|e| e.to_string()).collect();
            out.parse_failure = Some(format!("{}:\n  {}", path.display(), msgs.join("\n  ")));
            // Categorize for the known-invalid breakdown line.
            let json_path = path.with_extension("json");
            if json_path.exists() {
                let j = std::fs::read_to_string(&json_path).unwrap_or_default();
                out.should_validate =
                    j.contains("\"shouldValidate\": true") || j.contains("\"shouldValidate\":true");
            }
            None
        }
        // A non-parse error counts as "parsed" for acceptance, as before.
        Err(_) => None,
    };

    // ---- span differential (only for cases both parsers accept) ----
    // Reuse the lowering from the acceptance step when available; otherwise the
    // case simply isn't span-comparable (matching the span tests' skip on our
    // parse failure). Cedar must also parse it.
    let ours_lowered = ours_lowered.or_else(|| lower_ours_empty(&src));
    if let (Ok(cedar_pset), Some(dogwood_pset)) = (
        cedar_policy_core::parser::parse_policyset(&src),
        ours_lowered,
    ) {
        let ours: &PolicySet = dogwood_pset.as_cedar().as_ref();

        // leaf spans (content-keyed multiset)
        let mut our_leaf_set: BTreeMap<(LeafKey, (usize, usize)), usize> = BTreeMap::new();
        for item in leaf_spans(ours) {
            *our_leaf_set.entry(item).or_default() += 1;
        }
        let stem = path.file_stem().unwrap().to_string_lossy();
        for (key, span) in leaf_spans(&cedar_pset) {
            out.leaf_total += 1;
            match our_leaf_set.get_mut(&(key.clone(), span)) {
                Some(n) if *n > 0 => {
                    *n -= 1;
                    out.leaf_agreed += 1;
                }
                _ => out.leaf_divergences.push((stem.to_string(), key, span)),
            }
        }

        // all-node spans (kind-keyed multiset)
        let mut our_node_set: BTreeMap<(&'static str, (usize, usize)), usize> = BTreeMap::new();
        for item in node_spans(ours) {
            *our_node_set.entry(item).or_default() += 1;
        }
        for item in node_spans(&cedar_pset) {
            out.node_total += 1;
            if let Some(n) = our_node_set.get_mut(&item)
                && *n > 0
            {
                *n -= 1;
                out.node_agreed += 1;
            }
        }
    }

    out
}

/// Parallel corpus map for regime A: split the sorted corpus into contiguous
/// per-thread chunks, run [`run_empty_schema_case`] on each, and return the
/// outcomes in corpus order (deterministic regardless of scheduling).
fn empty_schema_outcomes(entries: &[PathBuf]) -> Vec<EmptySchemaOutcome> {
    let nthreads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .min(entries.len().max(1));
    let chunk_size = entries.len().div_ceil(nthreads).max(1);
    std::thread::scope(|scope| {
        let handles: Vec<_> = entries
            .chunks(chunk_size)
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .iter()
                        .map(|p| run_empty_schema_case(p))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect()
    })
}

#[test]
fn corpus_fuzz_parse_and_span() {
    let root = corpus_fuzz_root();
    if !root.exists() {
        return;
    }
    let mut entries: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("cedar"))
        .collect();
    entries.sort();
    let total = entries.len();
    if total == 0 {
        return;
    }

    let outcomes = empty_schema_outcomes(&entries);

    // Fold in corpus order.
    let mut parse_failures = Vec::new();
    let mut sv_true = 0usize;
    let mut sv_false = 0usize;
    let mut leaf_total = 0usize;
    let mut leaf_agreed = 0usize;
    let mut leaf_divergences: Vec<(String, LeafKey, (usize, usize))> = Vec::new();
    let mut node_total = 0usize;
    let mut node_agreed = 0usize;
    for o in outcomes {
        if let Some(f) = o.parse_failure {
            parse_failures.push(f);
            if o.should_validate {
                sv_true += 1;
            } else {
                // Matches the original: only cases with a `.json` are counted,
                // and every corpus case has one, so `!should_validate` == false.
                sv_false += 1;
            }
        }
        leaf_total += o.leaf_total;
        leaf_agreed += o.leaf_agreed;
        leaf_divergences.extend(o.leaf_divergences);
        node_total += o.node_total;
        node_agreed += o.node_agreed;
    }
    let passed = total - parse_failures.len();

    eprintln!(
        "corpus fuzz parse: {passed}/{total} parsed, {} known-invalid ({sv_false} also rejected by Cedar, {sv_true} dead-code only)",
        parse_failures.len()
    );
    eprintln!(
        "corpus fuzz span: leaf {leaf_agreed}/{leaf_total}, all-node {node_agreed}/{node_total}"
    );

    // parse-acceptance regression.
    if parse_failures.len() > MAX_KNOWN_INVALID {
        let report_path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../target/cedar-corpus-failures.txt");
        std::fs::write(&report_path, parse_failures.join("\n\n")).unwrap();
        let preview: Vec<_> = parse_failures
            .iter()
            .take(5)
            .map(|f| f.lines().next().unwrap_or(""))
            .collect();
        panic!(
            "Regression: {} > {} threshold.\n  First failures:\n    {}\n  Full report: {}",
            parse_failures.len(),
            MAX_KNOWN_INVALID,
            preview.join("\n    "),
            report_path.display()
        );
    }

    // leaf-span 100% assertion (content-keyed), with divergence report.
    if leaf_total > 0 && leaf_agreed != leaf_total {
        let report_path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../target/cedar-span-divergences.txt");
        let body: Vec<String> = leaf_divergences
            .iter()
            .map(|(stem, key, span)| format!("{stem}: {key:?}@{span:?}"))
            .collect();
        let _ = std::fs::write(&report_path, body.join("\n"));
        let pct = 100.0 * leaf_agreed as f64 / leaf_total as f64;
        panic!(
            "leaf-span agreement must be 100% ({leaf_agreed}/{leaf_total} = {pct:.2}%). \
             Full divergence report: {}",
            report_path.display(),
        );
    }

    // all-node 100% assertion (kind-keyed).
    if node_total > 0 {
        assert_eq!(
            node_agreed, node_total,
            "all-node span agreement must be 100% ({node_agreed}/{node_total})"
        );
    }
}

/// Ordinary policies (no pathological fuzz shapes). For these, EVERY leaf span —
/// literals, variables, slots, and attributes (including chained `a.b.c` and
/// index access) — must match Cedar's own parser exactly.
#[test]
fn hand_written_leaves_match_cedar_exactly() {
    let cases = [
        r#"permit(principal, action, resource) when { context.x > 5 };"#,
        r#"permit(principal == User::"alice", action, resource) when { principal.age >= 18 };"#,
        r#"forbid(principal, action, resource) when { context.a.b.c == "z" && resource.id != "0" };"#,
        r#"permit(principal, action, resource) when { if context.k then -7 else 42 };"#,
        r#"permit(principal, action, resource) when { context["k"] == 3 && -(4) < 5 };"#,
    ];
    for src in cases {
        let cedar_pset = cedar_policy_core::parser::parse_policyset(src)
            .unwrap_or_else(|e| panic!("cedar parse `{src}`: {e:?}"));
        let ours_pset = lower_ours_empty(src).unwrap_or_else(|| panic!("dogwood parse `{src}`"));
        let ours: &PolicySet = ours_pset.as_cedar().as_ref();

        let cedar_leaves = leaf_spans(&cedar_pset);
        let our_leaves = leaf_spans(ours);
        assert_eq!(
            cedar_leaves, our_leaves,
            "leaf spans must match Cedar exactly for `{src}`\n  cedar: {cedar_leaves:?}\n  ours:  {our_leaves:?}"
        );
    }
}

const MAX_KNOWN_AUTHORIZE_MISMATCHES: usize = 0;

/// The per-case result of the merged validate+authorize checks. Produced
/// independently per corpus case (no shared state) so cases can be processed on
/// worker threads, then folded serially in corpus order by the test.
#[derive(Default)]
struct CaseOutcome {
    // validate check
    validated: bool,
    validate_skipped: bool,
    validation_failure: Option<String>,
    // authorize check
    authorized: bool,
    authorize_skipped: bool,
    decision_mismatches: Vec<String>,
}

/// Lower one fuzz-corpus policy against its real paired schema **once** and run
/// both the validate and authorize checks on it. Pure: reads only its own case
/// files and returns a [`CaseOutcome`]; safe to call from a worker thread. The
/// skip/pass/fail logic mirrors the original independent tests exactly — a
/// `return` here is the analog of the old per-check `continue`.
fn run_fuzz_case(path: &Path, root: &Path) -> CaseOutcome {
    use cedar_policy::{Authorizer, Context, Decision, Entities, PolicySet, Request, Schema};
    use std::str::FromStr;

    let mut out = CaseOutcome::default();
    let stem = path.file_stem().unwrap().to_string_lossy();
    let schema_path = path.with_extension("cedarschema");
    let json_path = path.with_extension("json");
    let entities_path = root.join(format!("{stem}.entities.json"));
    let policy_src = std::fs::read_to_string(path).unwrap();

    // Lower once against the real paired schema. `unwrap_or_default` matches the
    // historical authorize behavior (a missing schema lowers against the empty
    // schema); every corpus case has a `.cedarschema` in practice, so this is
    // identical to validate's required-schema read. `None` = the schema failed
    // to parse or the policy failed to lower — a skip for both checks below.
    let schema_src = std::fs::read_to_string(&schema_path).unwrap_or_default();
    let service = ServiceSchema::defaults();
    let lowered: Option<LoweredPolicySet> = PolicySchema::from_cedarschema_str(&schema_src)
        .ok()
        .and_then(|ps| LoweredPolicySet::from_str(&policy_src, &service, &ps).ok());

    // ---- validate check (shouldValidate=true cases) ----
    let should_validate = schema_path.exists() && json_path.exists() && {
        let j = std::fs::read_to_string(&json_path).unwrap_or_default();
        j.contains("\"shouldValidate\": true") || j.contains("\"shouldValidate\":true")
    };
    if should_validate {
        match lowered.as_ref() {
            Some(policies) => {
                let result = Validator::new().validate(policies);
                if !result.validation_passed() {
                    let errs: Vec<_> = result.validation_errors().map(|e| e.to_string()).collect();
                    out.validation_failure = Some(format!("{stem}:\n  {}", errs.join("\n  ")));
                } else {
                    out.validated = true;
                }
            }
            None => out.validate_skipped = true,
        }
    } else {
        out.validate_skipped = true;
    }

    // ---- authorize check (cases with manifest + entities) ----
    if !json_path.exists() || !entities_path.exists() {
        out.authorize_skipped = true;
        return out;
    }
    let manifest: serde_json::Value =
        match serde_json::from_str(&std::fs::read_to_string(&json_path).unwrap()) {
            Ok(v) => v,
            Err(_) => {
                out.authorize_skipped = true;
                return out;
            }
        };
    let requests = match manifest.get("requests").and_then(|r| r.as_array()) {
        Some(r) if !r.is_empty() => r,
        _ => {
            out.authorize_skipped = true;
            return out;
        }
    };
    let dogwood_policies = match lowered.as_ref() {
        Some(p) => p,
        None => {
            out.authorize_skipped = true;
            return out;
        }
    };
    let entities_json = std::fs::read_to_string(&entities_path).unwrap();
    let entities = match Entities::from_json_str(&entities_json, None) {
        Ok(e) => e,
        Err(_) => {
            out.authorize_skipped = true;
            return out;
        }
    };
    // Also parse with Cedar directly for the PolicySet.
    let cedar_policies = match PolicySet::from_str(&policy_src) {
        Ok(p) => p,
        Err(_) => {
            out.authorize_skipped = true;
            return out;
        }
    };

    let schema_for_request: Option<&Schema> = None;
    let authorizer = Authorizer::new();
    let mut case_ok = true;

    for (i, req) in requests.iter().enumerate() {
        let expected_decision = match req.get("decision").and_then(|d| d.as_str()) {
            Some("allow") => Decision::Allow,
            Some("deny") => Decision::Deny,
            _ => continue,
        };

        let principal = match build_entity_uid(req.get("principal")) {
            Some(p) => p,
            None => continue,
        };
        let action = match build_entity_uid(req.get("action")) {
            Some(a) => a,
            None => continue,
        };
        let resource = match build_entity_uid(req.get("resource")) {
            Some(r) => r,
            None => continue,
        };

        let context = match req.get("context") {
            Some(ctx) => match Context::from_json_value(ctx.clone(), None) {
                Ok(c) => c,
                Err(_) => continue,
            },
            None => Context::empty(),
        };

        let request = match Request::new(principal, action, resource, context, schema_for_request) {
            Ok(r) => r,
            Err(_) => continue,
        };

        // Authorize with Cedar directly; if Cedar's own parse disagrees with the
        // oracle, skip the request rather than blame Dogwood.
        let response = authorizer.is_authorized(&request, &cedar_policies, &entities);
        if response.decision() != expected_decision {
            continue;
        }

        // Now authorize using the Cedar PolicySet that Dogwood lowered to
        // (`PolicySet::as_cedar`), verifying the lowering produces the same
        // decision.
        let dogwood_response =
            authorizer.is_authorized(&request, dogwood_policies.as_cedar(), &entities);
        if dogwood_response.decision() != expected_decision {
            case_ok = false;
            out.decision_mismatches.push(format!(
                "{stem} request {i}: expected {:?}, got {:?}",
                expected_decision,
                dogwood_response.decision()
            ));
        }
    }

    if case_ok {
        out.authorized = true;
    }
    out
}

/// One corpus walk that lowers each policy against its real paired schema
/// **once**, then feeds the lowered set to two independent checks:
///
/// * **validate** — cases whose manifest says `shouldValidate=true` are run
///   through [`Validator`]; tallied as `validated`/`validate_skipped`.
/// * **authorize** — cases with a manifest + entities have their lowered
///   `as_cedar()` decisions cross-validated against Cedar's own parse of the
///   same source; tallied as `authorized`/`authorize_skipped`.
///
/// The two checks keep entirely separate skip logic, counters, thresholds, and
/// failure reports — merging the loops only removes the redundant second
/// lowering (previously `corpus_fuzz_validate` and `corpus_fuzz_authorize`
/// lowered the same corpus independently).
#[test]
fn corpus_fuzz_validate_and_authorize() {
    let root = corpus_fuzz_root();
    if !root.exists() {
        return;
    }

    let mut entries: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("cedar"))
        .collect();
    entries.sort();
    let total = entries.len();

    // Map: process each case independently across worker threads. Split the
    // (sorted) corpus into `nthreads` contiguous chunks so each thread owns a
    // disjoint slice, and collect per-chunk outcome vectors. Concatenating the
    // chunk results in chunk order reproduces corpus order, so the serial fold
    // below — and therefore every counter and failure report — is deterministic
    // and independent of thread scheduling.
    let nthreads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .min(entries.len().max(1));
    let chunk_size = entries.len().div_ceil(nthreads);
    let root_ref = root.as_path();
    let outcomes: Vec<CaseOutcome> = std::thread::scope(|scope| {
        let handles: Vec<_> = entries
            .chunks(chunk_size.max(1))
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .iter()
                        .map(|path| run_fuzz_case(path, root_ref))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect()
    });

    // Reduce: fold the per-case outcomes in corpus order.
    let mut validated = 0usize;
    let mut validate_skipped = 0usize;
    let mut validation_failures = Vec::new();
    let mut authorized = 0usize;
    let mut authorize_skipped = 0usize;
    let mut decision_mismatches = Vec::new();

    for outcome in outcomes {
        validated += outcome.validated as usize;
        validate_skipped += outcome.validate_skipped as usize;
        if let Some(f) = outcome.validation_failure {
            validation_failures.push(f);
        }
        authorized += outcome.authorized as usize;
        authorize_skipped += outcome.authorize_skipped as usize;
        decision_mismatches.extend(outcome.decision_mismatches);
    }

    eprintln!(
        "corpus fuzz validate: {validated}/{total} validated, {validate_skipped} skipped, {} failures",
        validation_failures.len()
    );
    eprintln!(
        "corpus fuzz authorize: {authorized} cases checked, {authorize_skipped} skipped, {} mismatches",
        decision_mismatches.len()
    );

    if !validation_failures.is_empty() {
        let report_path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/cedar-corpus-validation-failures.txt");
        std::fs::write(&report_path, validation_failures.join("\n\n")).unwrap();
        let preview: Vec<_> = validation_failures
            .iter()
            .take(5)
            .map(|f| f.lines().next().unwrap_or(""))
            .collect();
        panic!(
            "{} shouldValidate=true failed.\n  First failures:\n    {}\n  Full report: {}",
            validation_failures.len(),
            preview.join("\n    "),
            report_path.display()
        );
    }

    if decision_mismatches.len() > MAX_KNOWN_AUTHORIZE_MISMATCHES {
        let report_path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/cedar-corpus-authorize-failures.txt");
        std::fs::write(&report_path, decision_mismatches.join("\n")).unwrap();
        let preview: Vec<_> = decision_mismatches.iter().take(5).collect();
        panic!(
            "Regression: {} > {} threshold.\n  First mismatches:\n    {}\n  Full report: {}",
            decision_mismatches.len(),
            MAX_KNOWN_AUTHORIZE_MISMATCHES,
            preview
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join("\n    "),
            report_path.display()
        );
    }
}

fn build_entity_uid(value: Option<&serde_json::Value>) -> Option<cedar_policy::EntityUid> {
    use std::str::FromStr;

    let obj = value?.as_object()?;
    let type_name = obj.get("type")?.as_str()?;
    let id = obj.get("id")?.as_str()?;
    Some(cedar_policy::EntityUid::from_type_name_and_id(
        cedar_policy::EntityTypeName::from_str(type_name).ok()?,
        cedar_policy::EntityId::from_str(id).ok()?,
    ))
}
