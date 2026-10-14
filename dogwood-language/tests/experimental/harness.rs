//! Experimental harness.
//!
//! Reads from `tests/experimental/corpus/` — cases that pass in the
//! reference interpreter (with the matching feature on, e.g.
//! `experimental-arithmetic`) but use syntax the embedded corpus does not
//! yet require of a conforming engine. Unlike `pending_fix` (asserted to still
//! fail), these cases are asserted to PASS: the reference interpreter
//! defines their semantics.
//!
//! This directory is deliberately not embedded in `src/corpus.rs`, so
//! harnesses that consume the embedded corpus never see it. Once the syntax
//! joins that portable contract, move the case to the matching embedded
//! directory (`tests/passing/temporal_only/corpus/`, `macros/corpus/`, or
//! `mixed/corpus/`); embedding picks it up automatically.
//!
//! Each case is driven through the Cedar-parity public API, exactly as in
//! the passing temporal harness: build a [`PolicySchema`] from the per-case
//! action schema and a [`ServiceSchema`] from the shared `request_response`
//! event schema fixture (or the case's `event.dwschema` override); parse the
//! policy into a [`LoweredPolicySet`]; then replay the trace with
//! [`replay_log`], comparing the verdict stream to the expected output.
//!
//! EXPERIMENTAL-ARITHMETIC: every case in this corpus uses arithmetic, so
//! the whole harness runs only with the `experimental-arithmetic` feature
//! on. If a non-arithmetic case is ever added, split it out or
//! lift this gate.
#![cfg(feature = "experimental-arithmetic")]

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

fn corpus_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/experimental/corpus")
}

fn default_event_schema() -> String {
    std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .expect("event schema")
}

/// Replay one trace of a case. Cases here are self-contained (per-case
/// `schema.cedarschema` required, no shared-schema fallback) so the eventual
/// move to `tests/passing/temporal_only/corpus/` is a plain `git mv`.
fn replay_case_trace(dir: &Path, trace: &str, event_schema: &str) -> Result<String, String> {
    let policy_src = read_sorted(dir, "policy_", "dw")
        .iter()
        .map(|p| std::fs::read_to_string(p).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    let schema_src = std::fs::read_to_string(dir.join("schema.cedarschema"))
        .unwrap_or_else(|e| panic!("{}: schema.cedarschema: {e}", dir.display()));
    let case_event_schema = std::fs::read_to_string(dir.join("event.dwschema"))
        .unwrap_or_else(|_| event_schema.to_string());

    let policy_schema =
        PolicySchema::from_cedarschema_str(&schema_src).map_err(|e| format!("{e:?}"))?;
    let service = ServiceSchema::builder()
        .event_schema_str(&case_event_schema)
        .build()
        .map_err(|e| format!("{e:?}"))?;
    let policies = LoweredPolicySet::from_str(&policy_src, &service, &policy_schema)
        .map_err(|e| format!("{e:?}"))?;
    replay_log(policies, trace).map_err(|e| format!("{e:?}"))
}

#[test]
fn experimental_cases_pass_in_reference_interpreter() {
    let root = corpus_root();
    if !root.exists() {
        return;
    }
    let event_schema = default_event_schema();

    let mut failures: Vec<String> = Vec::new();
    let mut passed = 0usize;

    for dir in case_dirs(&root) {
        let case = dir.file_name().unwrap().to_string_lossy().to_string();
        let mut case_ok = true;
        for trace_path in read_sorted(&dir, "trace_", "log") {
            let stem = trace_path.file_stem().unwrap().to_string_lossy();
            let n = stem.trim_start_matches("trace_");
            let expected_path = dir.join(format!("expected_{n}.out"));
            if !expected_path.exists() {
                continue;
            }
            let trace = std::fs::read_to_string(&trace_path).unwrap();
            let expected = std::fs::read_to_string(&expected_path).unwrap();

            match replay_case_trace(&dir, &trace, &event_schema) {
                Ok(got) if norm(&got) == norm(&expected) => {}
                Ok(got) => {
                    case_ok = false;
                    failures.push(format!(
                        "{case}: trace_{n}: mismatch\n  got: {:?}\n  exp: {:?}",
                        norm(&got),
                        norm(&expected)
                    ));
                }
                Err(e) => {
                    case_ok = false;
                    failures.push(format!("{case}: trace_{n}: {e}"));
                }
            }
        }
        if case_ok {
            passed += 1;
        }
    }

    eprintln!(
        "experimental corpus: {passed} passed, {} failed",
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

/// Generate or update `expected_<n>.out` files for cases that don't already
/// have one, or for all cases (when `OVERWRITE=1`). Run with:
///   cargo test --test experimental --features experimental-arithmetic -- --ignored generate_expected_out_files --nocapture
#[test]
#[ignore = "generates expected_<n>.out files — run manually"]
fn generate_expected_out_files() {
    let root = corpus_root();
    let event_schema = default_event_schema();
    let overwrite = std::env::var("OVERWRITE").is_ok();
    let mut written = 0usize;
    let mut skipped = 0usize;

    for dir in case_dirs(&root) {
        let case = dir.file_name().unwrap().to_string_lossy().to_string();
        for trace_path in read_sorted(&dir, "trace_", "log") {
            let stem = trace_path.file_stem().unwrap().to_string_lossy();
            let n = stem.trim_start_matches("trace_");
            let expected_path = dir.join(format!("expected_{n}.out"));
            if expected_path.exists() && !overwrite {
                skipped += 1;
                continue;
            }
            let trace = std::fs::read_to_string(&trace_path).unwrap();
            match replay_case_trace(&dir, &trace, &event_schema) {
                Ok(got) => {
                    std::fs::write(&expected_path, format!("{}\n", got.trim())).unwrap();
                    written += 1;
                    eprintln!("wrote: {case}/expected_{n}.out");
                }
                Err(e) => eprintln!("SKIP (error): {case}/trace_{n}: {e}"),
            }
        }
    }

    eprintln!(
        "\ngenerate_expected_out_files: {written} written, {skipped} skipped (already exist)"
    );
}
