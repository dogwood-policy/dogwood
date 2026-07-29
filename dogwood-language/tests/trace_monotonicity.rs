//! Corpus invariant: every `.log` trace must have **strictly increasing**
//! timestamps.
//!
//! The engine and every downstream consumer are only required to behave
//! correctly under strictly-monotone event timestamps: two events sharing a
//! timestamp (or going backwards) is outside the contract, so a corpus trace
//! that does it is testing behavior we do not guarantee. This test scans every
//! `trace_*.log` fixture under `tests/`, parses it with the real trace parser
//! (`dogwood_language::parse_trace`, the same one the harnesses use), and fails
//! if any adjacent pair of timepoints is not strictly increasing in `ts`.
//!
//! It reports *all* offending files at once (not just the first) so a bulk fix
//! can be verified in one run.

use std::path::{Path, PathBuf};

use dogwood_language::parse_trace;

/// Recursively collect every `trace_*.log` under `dir`.
fn trace_logs(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries =
        std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir({}): {e}", dir.display()));
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if path.is_dir() {
            trace_logs(&path, out);
        } else if path
            .file_name()
            .and_then(|n| n.to_str())
            .is_some_and(|n| n.starts_with("trace_") && n.ends_with(".log"))
        {
            out.push(path);
        }
    }
}

#[test]
fn all_corpus_traces_have_strictly_increasing_timestamps() {
    let tests_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut logs = Vec::new();
    trace_logs(&tests_root, &mut logs);
    logs.sort();
    assert!(
        !logs.is_empty(),
        "no trace_*.log files found under {} — did the corpus move?",
        tests_root.display()
    );

    let mut violations: Vec<String> = Vec::new();
    for path in &logs {
        let src = std::fs::read_to_string(path).unwrap();
        // Parse with the engine's own parser so we check exactly the timeline
        // the engine would see. A parse failure is itself a corpus defect.
        let events = match parse_trace(&src) {
            Ok(t) => t,
            Err(e) => {
                violations.push(format!("{}: parse error: {e}", rel(path)));
                continue;
            }
        };
        for i in 1..events.len() {
            let prev = events[i - 1].timestamp();
            let cur = events[i].timestamp();
            if cur <= prev {
                let how = if cur == prev { "equal" } else { "decreasing" };
                violations.push(format!(
                    "{}: timepoint {i} is not strictly after {}: ts {prev} -> {cur} ({how})",
                    rel(path),
                    i - 1
                ));
            }
        }
    }

    assert!(
        violations.is_empty(),
        "found {} trace(s) whose timestamps are not strictly increasing \
         (the engine only guarantees correct behavior under strictly-monotone \
         timestamps):\n\n{}",
        violations.len(),
        violations.join("\n")
    );
}

/// Render a path relative to the crate manifest dir, for compact messages.
fn rel(path: &Path) -> String {
    let base = Path::new(env!("CARGO_MANIFEST_DIR"));
    path.strip_prefix(base)
        .unwrap_or(path)
        .display()
        .to_string()
}
