//! The regression corpora, embedded so other implementations can reuse them
//! (feature `corpus`).
//!
//! Three temporal corpus directories are embedded, each living in its
//! respective test-category directory:
//!
//!   * `tests/passing/temporal_only/corpus/` — cases that parse, evaluate,
//!     and produce the expected verdict stream.
//!   * `tests/pending_fix/corpus/` — a holding area for cases whose verdict
//!     stream does not match their expected output. Currently empty.
//!   * `tests/expected_failures/corpus/` — cases using removed
//!     syntax (implicit-domain aggregation) plus event-schema errors;
//!     asserted to fail at parse time.
//!
//! Additionally:
//!
//!   * `tests/passing/macros/corpus/` — the macro-layer corpus
//!     (`def cedar` / `def temporal` expansion). No tolerated failures.
//!
//! This module embeds all corpora into the crate so that an alternative
//! implementation of the temporal engine can run the same cases through its
//! own backend and check them against the same expected verdicts.
//!
//! Category is derived from physical directory location — there are no
//! separate name lists to maintain. To recategorize a case, move it
//! between directories.

use include_dir::{Dir, include_dir};

static TEMPORAL_PASSING: Dir<'_> =
    include_dir!("$CARGO_MANIFEST_DIR/tests/passing/temporal_only/corpus");
/// The pending-fix corpus is expected to be empty. We construct an empty
/// `Dir` directly rather than using `include_dir!` because an empty directory
/// is not reliably preserved across crate packaging (git does not track empty
/// dirs, and a packaging step may strip dotfile placeholders like `.gitkeep`).
static TEMPORAL_PENDING_FIX: Dir<'_> = Dir::new("tests/pending_fix/corpus", &[]);
static TEMPORAL_PARSE_REJECTED: Dir<'_> =
    include_dir!("$CARGO_MANIFEST_DIR/tests/expected_failures/corpus");
static MACRO_CORPUS: Dir<'_> = include_dir!("$CARGO_MANIFEST_DIR/tests/passing/macros/corpus");
static MIXED_CORPUS: Dir<'_> = include_dir!("$CARGO_MANIFEST_DIR/tests/passing/mixed/corpus");

/// The shared schema stub that covers the common actions and entity types.
/// Cases without their own `schema.cedarschema` use this default.
const SHARED_SCHEMA: &str =
    include_str!("../tests/passing/temporal_only/shared_schema.cedarschema");

/// One trace + its expected verdict stream within a [`TemporalCase`].
#[derive(Debug, Clone)]
pub struct CorpusTrace {
    /// The `trace_<n>` suffix number (`1`, `2`, …).
    pub index: String,
    /// The `.log` trace wire text.
    pub trace_log: String,
    /// The expected verdict stream (`expected_<n>.out` contents).
    pub expected: String,
}

/// The outcome category of a temporal corpus case, derived from which
/// directory it lives in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemporalCategory {
    /// Parses, evaluates, and produces the expected verdict stream.
    Passing,
    /// Parses and evaluates, but the verdict stream does not match the
    /// expected output.
    Divergence,
    /// Uses removed syntax; expected to fail at parse time.
    ParseRejected,
}

/// A single temporal corpus case: the concatenated policy source, the
/// schema, the trace/expected pairs, and the category.
#[derive(Debug, Clone)]
pub struct TemporalCase {
    /// The case directory name, e.g. `0018_permit_when_unless`.
    pub name: String,
    /// All `policy_*.dw` files, concatenated in sorted order.
    pub policy_src: String,
    /// The `schema.cedarschema` (the Cedar policy schema).
    pub schema_src: String,
    /// The optional per-case `event.dwschema` override (the event/service
    /// schema, where a case declares custom event shape or reserved-field
    /// pins). `None` when the case uses the default event schema.
    pub event_schema_src: Option<String>,
    /// The `trace_<n>.log` / `expected_<n>.out` pairs, in order.
    pub traces: Vec<CorpusTrace>,
    /// The outcome category, derived from the on-disk directory.
    pub category: TemporalCategory,
}

impl TemporalCase {
    /// Whether the case is expected to produce a verdict stream that does not
    /// match its expected output.
    pub fn is_xfail(&self) -> bool {
        self.category == TemporalCategory::Divergence
    }

    /// Whether the case is expected to fail at parse time.
    pub fn is_parse_rejected(&self) -> bool {
        self.category == TemporalCategory::ParseRejected
    }
}

/// A single macro corpus case: same on-disk shape as a [`TemporalCase`],
/// but the macro corpus has no tolerated failures — every case is expected
/// to expand and evaluate cleanly.
#[derive(Debug, Clone)]
pub struct MacroCase {
    /// The case directory name, e.g. `0001_count_formerly_login_history`.
    pub name: String,
    /// All `policy_*.dw` files, concatenated in sorted order.
    pub policy_src: String,
    /// The `schema.cedarschema` (the Cedar policy schema).
    pub schema_src: String,
    /// The optional per-case `event.dwschema` override; `None` for the default.
    pub event_schema_src: Option<String>,
    /// The optional per-case macro library (`macros.dw`), supplied to the
    /// service schema via `macros_str` — the shipped-library path, as opposed
    /// to inlining `def`s in the policy. `None` for the default (empty) library.
    pub macros_src: Option<String>,
    /// The `trace_<n>.log` / `expected_<n>.out` pairs, in order.
    pub traces: Vec<CorpusTrace>,
}

/// Load every temporal corpus case from all three categories, sorted by name.
pub fn temporal_cases() -> Vec<TemporalCase> {
    let mut cases = Vec::new();
    load_temporal_dir(&TEMPORAL_PASSING, TemporalCategory::Passing, &mut cases);
    load_temporal_dir(
        &TEMPORAL_PENDING_FIX,
        TemporalCategory::Divergence,
        &mut cases,
    );
    load_temporal_dir(
        &TEMPORAL_PARSE_REJECTED,
        TemporalCategory::ParseRejected,
        &mut cases,
    );
    cases.sort_by(|a, b| a.name.cmp(&b.name));
    cases
}

/// Load every macro corpus case, sorted by name.
pub fn macro_cases() -> Vec<MacroCase> {
    let mut cases: Vec<MacroCase> = MACRO_CORPUS
        .dirs()
        .filter_map(|dir| {
            let parts = load_parts(dir)?;
            Some(MacroCase {
                name: parts.name,
                policy_src: parts.policy_src,
                schema_src: parts.schema_src,
                event_schema_src: parts.event_schema_src,
                macros_src: parts.macros_src,
                traces: parts.traces,
            })
        })
        .collect();
    cases.sort_by(|a, b| a.name.cmp(&b.name));
    cases
}

/// A single mixed-dialect corpus case: policies combining Cedar, temporal,
/// and/or provider clauses. Same on-disk shape as the other corpora.
#[derive(Debug, Clone)]
pub struct MixedCase {
    /// The case directory name, e.g. `0001_cedar_and_temporal_formerly`.
    pub name: String,
    /// All `policy_*.dw` files, concatenated in sorted order.
    pub policy_src: String,
    /// The `schema.cedarschema` (the Cedar policy schema).
    pub schema_src: String,
    /// The optional per-case `event.dwschema` override; `None` for the default.
    pub event_schema_src: Option<String>,
    /// The `trace_<n>.log` / `expected_<n>.out` pairs, in order.
    pub traces: Vec<CorpusTrace>,
}

/// Load every mixed corpus case, sorted by name.
pub fn mixed_cases() -> Vec<MixedCase> {
    let mut cases: Vec<MixedCase> = MIXED_CORPUS
        .dirs()
        .filter_map(|dir| {
            let parts = load_parts(dir)?;
            Some(MixedCase {
                name: parts.name,
                policy_src: parts.policy_src,
                schema_src: parts.schema_src,
                event_schema_src: parts.event_schema_src,
                traces: parts.traces,
            })
        })
        .collect();
    cases.sort_by(|a, b| a.name.cmp(&b.name));
    cases
}

fn load_temporal_dir(dir: &Dir<'_>, category: TemporalCategory, out: &mut Vec<TemporalCase>) {
    for case_dir in dir.dirs() {
        if let Some(parts) = load_parts(case_dir) {
            out.push(TemporalCase {
                name: parts.name,
                policy_src: parts.policy_src,
                schema_src: parts.schema_src,
                event_schema_src: parts.event_schema_src,
                traces: parts.traces,
                category,
            });
        }
    }
}

/// The pieces shared by every corpus case, loaded from one case directory.
struct CaseParts {
    name: String,
    policy_src: String,
    schema_src: String,
    event_schema_src: Option<String>,
    macros_src: Option<String>,
    traces: Vec<CorpusTrace>,
}

/// Load one case directory (used by both corpora — same on-disk layout):
/// concatenate `policy_*.dw` in order, read `schema.cedarschema`, read the
/// optional `event.dwschema` override, and pair `trace_<n>.log` with
/// `expected_<n>.out`.
fn load_parts(dir: &Dir<'_>) -> Option<CaseParts> {
    let name = dir.path().file_name()?.to_string_lossy().to_string();

    // Concatenate policy_*.dw in sorted order.
    let mut policy_files: Vec<&include_dir::File> = dir
        .files()
        .filter(|f| {
            let n = f
                .path()
                .file_name()
                .map(|n| n.to_string_lossy())
                .unwrap_or_default();
            n.starts_with("policy_") && n.ends_with(".dw")
        })
        .collect();
    policy_files.sort_by_key(|f| f.path().to_path_buf());
    let policy_src = policy_files
        .iter()
        .filter_map(|f| f.contents_utf8())
        .collect::<Vec<_>>()
        .join("\n");

    let schema_src = dir
        .get_file(dir.path().join("schema.cedarschema"))
        .and_then(|f| f.contents_utf8())
        .map(|s| s.to_string())
        .unwrap_or_else(|| SHARED_SCHEMA.to_string());

    // Optional per-case event-schema override (`event.dwschema`). When present
    // it replaces the shared default event schema — this is where a case
    // declares custom event shape / reserved-field pins. `None` means the case
    // uses the default event schema.
    let event_schema_src = dir
        .get_file(dir.path().join("event.dwschema"))
        .and_then(|f| f.contents_utf8())
        .map(|s| s.to_string());

    // Optional per-case macro library (`macros.dw`), supplied via `macros_str`.
    // `None` means the case uses the default macro library (`DEFAULT_MACROS`,
    // the built-in stdlib).
    let macros_src = dir
        .get_file(dir.path().join("macros.dw"))
        .and_then(|f| f.contents_utf8())
        .map(|s| s.to_string());

    // Pair trace_<n>.log with expected_<n>.out by suffix number.
    let mut traces: Vec<CorpusTrace> = Vec::new();
    let mut trace_files: Vec<&include_dir::File> = dir
        .files()
        .filter(|f| {
            let n = f
                .path()
                .file_name()
                .map(|n| n.to_string_lossy())
                .unwrap_or_default();
            n.starts_with("trace_") && n.ends_with(".log")
        })
        .collect();
    trace_files.sort_by_key(|f| f.path().to_path_buf());
    for tf in trace_files {
        let stem = tf.path().file_stem()?.to_string_lossy().to_string();
        let index = stem.trim_start_matches("trace_").to_string();
        let trace_log = tf.contents_utf8().unwrap_or_default().to_string();
        let expected = dir
            .get_file(dir.path().join(format!("expected_{index}.out")))
            .and_then(|f| f.contents_utf8())
            .map(|s| s.to_string());
        if let Some(expected) = expected {
            traces.push(CorpusTrace {
                index,
                trace_log,
                expected,
            });
        }
    }

    Some(CaseParts {
        name,
        policy_src,
        schema_src,
        event_schema_src,
        macros_src,
        traces,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    /// Count subdirectories in a path (the on-disk case count).
    fn dir_count(path: &Path) -> usize {
        std::fs::read_dir(path)
            .map(|entries| {
                entries
                    .filter_map(|e| e.ok())
                    .filter(|e| e.path().is_dir())
                    .count()
            })
            .unwrap_or(0)
    }

    #[test]
    fn embedded_corpus_loads_all_categories() {
        let cases = temporal_cases();
        let passing = cases
            .iter()
            .filter(|c| c.category == TemporalCategory::Passing)
            .count();
        let pending_fix = cases
            .iter()
            .filter(|c| c.category == TemporalCategory::Divergence)
            .count();
        let parse_rejected = cases
            .iter()
            .filter(|c| c.category == TemporalCategory::ParseRejected)
            .count();

        // Compare embedded counts against on-disk directory counts so
        // the assertion stays correct as cases are added — no static
        // number to update.
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let expected_passing = dir_count(&manifest.join("tests/passing/temporal_only/corpus"));
        let expected_rejected = dir_count(&manifest.join("tests/expected_failures/corpus"));

        assert_eq!(
            passing, expected_passing,
            "embedded passing count doesn't match on-disk"
        );
        assert_eq!(
            pending_fix, 0,
            "expected 0 pending-fix cases, got {pending_fix}"
        );
        assert_eq!(
            parse_rejected, expected_rejected,
            "embedded parse_rejected count doesn't match on-disk"
        );

        // Spot-check a known passing case.
        let sample = cases
            .iter()
            .find(|c| c.name == "0018_permit_when_unless")
            .expect("a known case is present");
        assert_eq!(sample.category, TemporalCategory::Passing);
        assert!(sample.policy_src.contains("permit"), "policy text loaded");
        assert!(
            sample.schema_src.contains("namespace"),
            "schema text loaded"
        );
        assert!(!sample.traces.is_empty(), "trace/expected pairs loaded");
    }

    #[test]
    fn embedded_macro_corpus_loads_cases() {
        let cases = macro_cases();
        let expected =
            dir_count(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing/macros/corpus"));
        assert_eq!(
            cases.len(),
            expected,
            "embedded macro count doesn't match on-disk"
        );
        let sample = cases
            .iter()
            .find(|c| c.name == "0001_count_formerly_login_history")
            .expect("a known macro case is present");
        assert!(
            sample.policy_src.contains("count_formerly"),
            "macro policy text loaded"
        );
        assert!(!sample.traces.is_empty(), "trace/expected pairs loaded");
    }

    #[test]
    fn embedded_mixed_corpus_loads_cases() {
        let cases = mixed_cases();
        let expected =
            dir_count(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing/mixed/corpus"));
        assert_eq!(
            cases.len(),
            expected,
            "embedded mixed count doesn't match on-disk"
        );
        let sample = cases
            .iter()
            .find(|c| c.name == "0001_cedar_and_temporal_formerly")
            .expect("a known mixed case is present");
        assert!(
            sample.policy_src.contains("permit"),
            "mixed policy text loaded"
        );
        assert!(!sample.traces.is_empty(), "trace/expected pairs loaded");
    }

    #[test]
    fn categories_are_disjoint() {
        let cases = temporal_cases();
        // Each case should appear exactly once.
        let mut names: Vec<&str> = cases.iter().map(|c| c.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(names.len(), before, "duplicate case names found");
    }
}
