//! Temporal-only verdict-corpus harness.
//!
//! Reads from `tests/passing/temporal_only/corpus/` — cases that parse,
//! evaluate, and produce the expected verdict stream. No skip lists;
//! category is determined by physical directory location.
//!
//! Each case is driven through the Cedar-parity public API: build a
//! [`PolicySchema`] from the action schema and a [`ServiceSchema`] from the
//! event schema (the case's `event.dwschema` override when present, otherwise
//! the shared `request_response` fixture); parse the policy into a
//! [`LoweredPolicySet`] via [`LoweredPolicySet::from_str`]; then replay the
//! trace with [`replay_log`], comparing the verdict stream to the expected
//! output.

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

/// Per-case result: whether every trace in the case matched, and the failure
/// strings for any that did not. Produced independently per case (no shared
/// mutable state) so cases can run on worker threads and be folded in corpus
/// order.
struct CaseResult {
    case_ok: bool,
    failures: Vec<String>,
}

/// Replay every trace of one corpus case against the expected verdict stream.
/// Pure: reads only this case's files plus the shared schema fallbacks passed
/// in; safe to call from a worker thread. Skip/pass/fail logic (including the
/// per-trace `catch_unwind`) mirrors the original serial loop exactly.
fn run_temporal_case(dir: &Path, shared_schema: &str, event_schema: &str) -> CaseResult {
    let case = dir.file_name().unwrap().to_string_lossy().to_string();

    let policy_src = read_sorted(dir, "policy_", "dw")
        .iter()
        .map(|p| std::fs::read_to_string(p).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    // Per-case schema overrides the shared one; fall back to shared schema.
    let schema_src = if dir.join("schema.cedarschema").exists() {
        std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap()
    } else {
        shared_schema.to_string()
    };
    let case_event_schema = std::fs::read_to_string(dir.join("event.dwschema"))
        .unwrap_or_else(|_| event_schema.to_string());

    let mut result = CaseResult {
        case_ok: true,
        failures: Vec::new(),
    };
    for trace_path in read_sorted(dir, "trace_", "log") {
        let stem = trace_path.file_stem().unwrap().to_string_lossy();
        let n = stem.trim_start_matches("trace_");
        let expected_path = dir.join(format!("expected_{n}.out"));
        if !expected_path.exists() {
            continue;
        }
        let trace = std::fs::read_to_string(&trace_path).unwrap();
        let expected = std::fs::read_to_string(&expected_path).unwrap();

        let replayed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            // Build the policy schema from the action schema and the service
            // schema from this case's event schema (the per-case
            // `event.dwschema` override when present, else the shared
            // `request_response` fixture). A build or parse Err is mapped to
            // the failure string, exactly as the old `authorize_trace` Err was.
            // `replay_log` consumes the LoweredPolicySet, so assemble it fresh
            // per trace.
            let policy_schema =
                PolicySchema::from_cedarschema_str(&schema_src).map_err(|e| format!("{e:?}"))?;
            let service = ServiceSchema::builder()
                .event_schema_str(&case_event_schema)
                .build()
                .map_err(|e| format!("{e:?}"))?;
            let policies = LoweredPolicySet::from_str(&policy_src, &service, &policy_schema)
                .map_err(|e| format!("{e:?}"))?;
            replay_log(policies, &trace).map_err(|e| format!("{e:?}"))
        }));
        match replayed {
            Ok(Ok(got)) if norm(&got) == norm(&expected) => {}
            Ok(Ok(got)) => {
                result.case_ok = false;
                result.failures.push(format!(
                    "{case}: trace_{n}: mismatch\n  got: {:?}\n  exp: {:?}",
                    norm(&got),
                    norm(&expected)
                ));
            }
            Ok(Err(e)) => {
                result.case_ok = false;
                result.failures.push(format!("{case}: trace_{n}: {e}"));
            }
            Err(_) => {
                result.case_ok = false;
                result.failures.push(format!("{case}: trace_{n}: PANIC"));
            }
        }
    }
    result
}

#[test]
fn temporal_corpus_verdicts() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing/temporal_only/corpus");
    if !root.exists() {
        return;
    }

    let event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .expect("event schema");

    let shared_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/passing/temporal_only/shared_schema.cedarschema"),
    )
    .expect("shared schema");

    let dirs = case_dirs(&root);

    // Map: process each case independently across worker threads, split into
    // contiguous per-thread chunks over the sorted case list. Concatenating the
    // per-chunk results in chunk order reproduces corpus order, so the fold —
    // and therefore the failure list — is deterministic regardless of
    // scheduling.
    let nthreads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .min(dirs.len().max(1));
    let chunk_size = dirs.len().div_ceil(nthreads).max(1);
    let (shared_ref, event_ref) = (shared_schema.as_str(), event_schema.as_str());
    let results: Vec<CaseResult> = std::thread::scope(|scope| {
        let handles: Vec<_> = dirs
            .chunks(chunk_size)
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .iter()
                        .map(|dir| run_temporal_case(dir, shared_ref, event_ref))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect()
    });

    // Reduce: fold per-case results in corpus order.
    let mut failures: Vec<String> = Vec::new();
    let mut passed = 0usize;
    for r in results {
        if r.case_ok {
            passed += 1;
        }
        failures.extend(r.failures);
    }

    eprintln!(
        "temporal corpus: {passed} passed, {} failed",
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
