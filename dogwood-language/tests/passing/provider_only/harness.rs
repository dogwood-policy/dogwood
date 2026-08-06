//! Information-provider dialect test harness.
//!
//! Verdict-corpus tests for `guardrails { … }` policies (the marker keyword
//! is `guardrails`; the concept is an information provider). Each case under
//! `corpus/` has policy + schema + providers.json + trace + expected.
//!
//! Each case is driven through the Cedar-parity public API: build a
//! [`PolicySchema`] from the action schema and a [`ServiceSchema`] from the
//! `request_response` event schema fixture and (when present) the case's
//! [`ProviderDeclarations`]; parse the policy into a [`LoweredPolicySet`] via
//! [`LoweredPolicySet::from_str`]; then replay the trace with [`replay_log`],
//! comparing the verdict stream to the expected output.

use std::path::{Path, PathBuf};

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, replay_log,
};

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
fn provider_corpus_verdicts() {
    let event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .expect("event schema");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing/provider_only/corpus");
    if !root.exists() {
        return;
    }

    let shared_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/passing/provider_only/shared_schema.cedarschema"),
    )
    .expect("shared provider schema");

    let mut failures: Vec<String> = Vec::new();
    let mut passed = 0usize;

    for dir in case_dirs(&root) {
        let case = dir.file_name().unwrap().to_string_lossy().to_string();
        let policy_src = read_sorted(&dir, "policy_", "dw")
            .iter()
            .map(|p| std::fs::read_to_string(p).unwrap())
            .collect::<Vec<_>>()
            .join("\n");
        let schema_src = if dir.join("schema.cedarschema").exists() {
            std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap()
        } else {
            shared_schema.clone()
        };

        // Load provider declarations if present
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
        let mut case_ok = true;
        for trace_path in traces {
            let stem = trace_path.file_stem().unwrap().to_string_lossy();
            let n = stem.trim_start_matches("trace_");
            let expected_path = dir.join(format!("expected_{n}.out"));
            if !expected_path.exists() {
                continue;
            }
            let trace = std::fs::read_to_string(&trace_path).unwrap();
            let expected = std::fs::read_to_string(&expected_path).unwrap();

            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                // Build the schema: action schema (PolicySchema) + the
                // request_response event schema fixture, plus the case's provider
                // declarations when present (ServiceSchema). `replay_log` consumes the
                // LoweredPolicySet (and the service-schema build consumes the
                // ProviderDeclarations), so assemble both fresh per trace.
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
                Ok(Ok(got)) if norm(&got) == norm(&expected) => {}
                Ok(Ok(got)) => {
                    case_ok = false;
                    failures.push(format!(
                        "{case}: trace_{n}: mismatch\n  got: {:?}\n  exp: {:?}",
                        norm(&got),
                        norm(&expected)
                    ));
                }
                Ok(Err(e)) => {
                    case_ok = false;
                    failures.push(format!("{case}: trace_{n}: {e}"));
                }
                Err(_) => {
                    case_ok = false;
                    failures.push(format!("{case}: trace_{n}: PANIC"));
                }
            }
        }
        if case_ok {
            passed += 1;
        }
    }

    eprintln!(
        "provider corpus: {passed} passed, {} failed",
        failures.len()
    );
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
