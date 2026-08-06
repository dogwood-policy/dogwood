//! Macro expansion verdict-corpus harness.
//!
//! Each case under `corpus/` tests `def cedar` and `def temporal`
//! macro expansion end-to-end.
//!
//! Migrated to the Cedar-parity public API: each case builds a
//! [`PolicySchema`] from its `schema.cedarschema` action schema plus a
//! [`ServiceSchema`] for the shared request/response event schema, parses
//! the corpus policy into a [`LoweredPolicySet`]
//! (`LoweredPolicySet::from_str`), then drives each recorded trace through
//! [`replay_log`] and compares the verdict stream against the expected
//! output. `replay_log` consumes the `LoweredPolicySet`, so the policy is
//! re-parsed per trace.

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema};
use std::path::{Path, PathBuf};

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

/// Per-case result: whether every trace of the case matched, plus failure
/// strings for any that did not. Produced independently per case (no shared
/// mutable state) so cases can run on worker threads and be folded in corpus
/// order.
struct CaseResult {
    case_ok: bool,
    failures: Vec<String>,
}

/// Replay every trace of one macro-corpus case against its expected verdict
/// stream. Pure: reads only this case's files plus the shared `event_schema`
/// passed in; safe to call from a worker thread. Skip/pass/fail logic
/// (including the per-trace `catch_unwind`) mirrors the original serial loop.
fn run_macro_case(dir: &Path, event_schema: &str) -> CaseResult {
    let case = dir.file_name().unwrap().to_string_lossy().to_string();
    let policy_src = read_sorted(dir, "policy_", "dw")
        .iter()
        .map(|p| std::fs::read_to_string(p).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    let schema_src = std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap_or_default();

    // Optional per-case macro library. When a `macros.dw` file is present, its
    // `def`s are loaded into the ServiceSchema via `macros_str` — the same path
    // a deployment uses to ship a reusable macro library (the CLI `--macros`
    // flag / `ServiceSchemaBuilder::macros_str`), rather than inlining the
    // `def`s in the policy. A policy's own `def` still wins over a same-named
    // library macro (library precedence rule). Absent the file, the case uses
    // the default macro library (`DEFAULT_MACROS`, the built-in stdlib).
    let macros_src = std::fs::read_to_string(dir.join("macros.dw")).ok();

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
            // Build the service schema (shared request/response event schema)
            // and the policy (action) schema, parse the policy into a
            // LoweredPolicySet, then replay the trace. `replay_log` consumes the
            // LoweredPolicySet, so it is parsed per trace.
            let mut builder = ServiceSchema::builder().event_schema_str(event_schema);
            if let Some(ref m) = macros_src {
                builder = builder.macros_str(m);
            }
            let service = builder.build().map_err(|e| format!("{e:?}"))?;
            let policy_schema =
                PolicySchema::from_cedarschema_str(&schema_src).map_err(|e| format!("{e:?}"))?;
            let policies = LoweredPolicySet::from_str(&policy_src, &service, &policy_schema)
                .map_err(|e| format!("{e:?}"))?;
            dogwood_language::replay_log(policies, &trace).map_err(|e| format!("{e:?}"))
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
fn macro_corpus_verdicts() {
    let event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .expect("event schema");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing/macros/corpus");
    if !root.exists() {
        return;
    }

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
    let event_ref = event_schema.as_str();
    let results: Vec<CaseResult> = std::thread::scope(|scope| {
        let handles: Vec<_> = dirs
            .chunks(chunk_size)
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .iter()
                        .map(|dir| run_macro_case(dir, event_ref))
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

    eprintln!("macro corpus: {passed} passed, {} failed", failures.len());
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
