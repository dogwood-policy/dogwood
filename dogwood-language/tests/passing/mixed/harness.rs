//! Mixed-dialect corpus harness: parse/validate **and** verdicts.
//!
//! Each case under `corpus/` has `policy_*.dw` + `schema.cedarschema`, and most
//! also ship `trace_N.log` + `expected_N.out` for verdict checking, plus
//! (10 of 15) a `providers.json`.
//!
//! Two tests, both driven through the Cedar-parity public API:
//!
//!   * [`mixed_cases_parse`] — build a [`ServiceSchema`] (the shared
//!     request/response event schema, needed for temporal predicates) and a
//!     [`PolicySchema`] (the case's action schema), then lower the policy via
//!     [`LoweredPolicySet::from_str`]. Success iff both steps succeed.
//!   * [`mixed_cases_verdicts`] — for each case with a `trace_N.log` /
//!     `expected_N.out` pair, replay the trace with [`replay_log`] and compare
//!     the verdict stream. This mirrors the temporal_only / provider_only /
//!     macros harnesses; it was dropped when the public API was migrated to the
//!     Cedar-parity surface (the `api::authorize_trace` it used was removed) and
//!     is restored here on `replay_log`.

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, replay_log,
};
use std::path::{Path, PathBuf};

/// The `.out` verdict stream, trimmed to non-empty lines for comparison.
fn norm(s: &str) -> Vec<String> {
    s.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(str::to_string)
        .collect()
}

fn case_dirs(root: &Path) -> Vec<PathBuf> {
    let mut v: Vec<_> = std::fs::read_dir(root)
        .unwrap_or_else(|e| panic!("read_dir({}): {e}", root.display()))
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    v.sort();
    v
}

fn read_sorted(dir: &Path, prefix: &str, ext: &str) -> Vec<PathBuf> {
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

#[test]
fn mixed_cases_parse() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing/mixed/corpus");
    if !root.exists() {
        return;
    }

    let event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .expect("event schema");

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
        let schema_src =
            std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap_or_default();

        // Build the service schema (the shared request/response event
        // schema) and the policy (action) schema, then lower the policy.
        // Either step failing means the case did not parse.
        let result = ServiceSchema::builder()
            .event_schema_str(&event_schema)
            .build()
            .and_then(|service| {
                PolicySchema::from_cedarschema_str(&schema_src).and_then(|policy_schema| {
                    LoweredPolicySet::from_str(&policy_src, &service, &policy_schema)
                })
            });

        match result {
            Ok(_) => passed += 1,
            Err(e) => failures.push(format!("{name}: {e:?}")),
        }
    }

    eprintln!("mixed cases: {passed} passed, {} failed", failures.len());
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

/// Replay each case's `trace_N.log` and compare its verdict stream to
/// `expected_N.out`. A case with no trace/expected pair contributes nothing
/// (parse-only cases are covered by [`mixed_cases_parse`]).
#[test]
fn mixed_cases_verdicts() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing/mixed/corpus");
    if !root.exists() {
        return;
    }

    let event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .expect("event schema");

    let mut failures: Vec<String> = Vec::new();
    let mut passed = 0usize;

    for dir in case_dirs(&root) {
        let case = dir.file_name().unwrap().to_string_lossy().to_string();

        let policy_src = read_sorted(&dir, "policy_", "dw")
            .iter()
            .map(|p| std::fs::read_to_string(p).unwrap())
            .collect::<Vec<_>>()
            .join("\n");
        if policy_src.is_empty() {
            continue;
        }
        let schema_src =
            std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap_or_default();

        // Load provider declarations if present (10 of the 15 mixed cases have
        // them); a case without is pure cedar+temporal.
        let decls_path = dir.join("providers.json");
        let decls = if decls_path.exists() {
            match ProviderDeclarations::from_json_file(&decls_path) {
                Ok(d) => Some(d),
                Err(e) => {
                    failures.push(format!("{case}: providers.json: {e}"));
                    continue;
                }
            }
        } else {
            None
        };

        let traces = read_sorted(&dir, "trace_", "log");
        for trace_path in traces {
            let stem = trace_path.file_stem().unwrap().to_string_lossy();
            let n = stem.trim_start_matches("trace_");
            let expected_path = dir.join(format!("expected_{n}.out"));
            if !expected_path.exists() {
                continue;
            }
            let trace = std::fs::read_to_string(&trace_path).unwrap();
            let expected = std::fs::read_to_string(&expected_path).unwrap();

            // Reassemble the schema + lowered set per trace: `replay_log`
            // consumes the `LoweredPolicySet` (and the service-schema build
            // consumes the `ProviderDeclarations`).
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let policy_schema = PolicySchema::from_cedarschema_str(&schema_src)
                    .map_err(|e| format!("{e:?}"))?;
                let mut builder = ServiceSchema::builder().event_schema_str(&event_schema);
                if let Some(d) = &decls {
                    builder = builder.providers(d.clone());
                }
                let service = builder.build().map_err(|e| format!("{e:?}"))?;
                let policies = LoweredPolicySet::from_str(&policy_src, &service, &policy_schema)
                    .map_err(|e| format!("{e:?}"))?;
                replay_log(policies, &trace).map_err(|e| format!("{e:?}"))
            }));

            match result {
                Ok(Ok(got)) if norm(&got) == norm(&expected) => passed += 1,
                Ok(Ok(got)) => failures.push(format!(
                    "{case}: trace_{n}: mismatch\n  got: {:?}\n  exp: {:?}",
                    norm(&got),
                    norm(&expected)
                )),
                Ok(Err(e)) => failures.push(format!("{case}: trace_{n}: {e}")),
                Err(_) => failures.push(format!("{case}: trace_{n}: PANIC")),
            }
        }
    }

    eprintln!(
        "mixed corpus verdicts: {passed} passed, {} failed",
        failures.len()
    );
    assert!(
        passed > 0,
        "no verdict cases were exercised — check that corpus/ cases carry trace_*.log + expected_*.out"
    );
    assert!(
        failures.is_empty(),
        "failures:\n\n{}",
        failures.join("\n\n")
    );
}
