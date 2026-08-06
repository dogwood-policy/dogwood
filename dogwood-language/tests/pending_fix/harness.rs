//! Pending-fix harness.
//!
//! Reads from `tests/pending_fix/corpus/` — cases whose verdict stream does
//! not match their `expected_<n>.out`. Asserts they STILL FAIL. If one starts
//! passing, it should be moved to
//! `tests/passing/temporal_only/corpus/`.
//!
//! Each case is driven through the Cedar-parity public API: build a
//! [`ServiceSchema`] from the shared `request_response` event schema fixture
//! and a [`PolicySchema`] from the action schema; parse the policy into a
//! [`LoweredPolicySet`] via [`LoweredPolicySet::from_str`]; then replay the
//! trace with [`replay_log`]. A build or parse error counts as a mismatch,
//! just as an `authorize_trace` Err did.

use std::path::{Path, PathBuf};

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema, replay_log};

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
fn temporal_mismatches_still_fail() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/pending_fix/corpus");
    if !root.exists() {
        return;
    }

    let event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .expect("event schema");

    let mut unexpectedly_passing = Vec::new();
    let mut still_failing = 0usize;

    for dir in case_dirs(&root) {
        let case = dir.file_name().unwrap().to_string_lossy().to_string();

        let policy_src = read_sorted(&dir, "policy_", "dw")
            .iter()
            .map(|p| std::fs::read_to_string(p).unwrap())
            .collect::<Vec<_>>()
            .join("\n");
        let schema_src =
            std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap_or_default();

        let traces = read_sorted(&dir, "trace_", "log");
        let mut case_mismatches = false;
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
                // Build the service schema from the shared `request_response`
                // event schema fixture and the policy schema from the action
                // schema, parse the policy, then replay the trace. A build or
                // parse Err is surfaced as an Err (a mismatch), exactly as the
                // old `authorize_trace` Err was. `replay_log` consumes the
                // LoweredPolicySet, so assemble it fresh per trace.
                let service = ServiceSchema::builder()
                    .event_schema_str(&event_schema)
                    .build()?;
                let policy_schema = PolicySchema::from_cedarschema_str(&schema_src)?;
                let policies = LoweredPolicySet::from_str(&policy_src, &service, &policy_schema)?;
                replay_log(policies, &trace)
            }));
            match result {
                Ok(Ok(got)) if norm(&got) != norm(&expected) => {
                    case_mismatches = true;
                }
                Ok(Err(_)) | Err(_) => {
                    case_mismatches = true;
                }
                _ => {}
            }
        }

        if case_mismatches {
            still_failing += 1;
        } else {
            unexpectedly_passing.push(case);
        }
    }

    eprintln!(
        "pending_fix: {still_failing} still failing, {} unexpectedly passing",
        unexpectedly_passing.len()
    );
    if !unexpectedly_passing.is_empty() {
        panic!(
            "These cases now PASS — move them to tests/passing/temporal_only/corpus/:\n  {}",
            unexpectedly_passing.join("\n  ")
        );
    }
}
