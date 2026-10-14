use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use dogwood_formatter::format_policies;
use dogwood_language::{ParsedPolicySet, ServiceSchema};

static NEXT_TEMP_FILE: AtomicUsize = AtomicUsize::new(0);

/// `ParsedPolicySet` deliberately has no `PartialEq`: source locations and the
/// private surface representation are not a public stability contract.
/// `expanded_source` is its canonical, AST-derived semantic representation,
/// so equal expanded documents mean both parses produced the same effective
/// policy trees while ignoring formatting and source spans.
fn canonical_ast(path: &Path, service: &ServiceSchema) -> Vec<String> {
    let source =
        fs::read_to_string(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let parsed = ParsedPolicySet::parse(&source, service)
        .unwrap_or_else(|error| panic!("parse {}: {error}", path.display()));
    parsed
        .policies()
        .map(|policy| policy.expanded_source())
        .collect()
}

fn assert_formatting_preserves_ast(fixture: &str) {
    let input_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join(fixture);
    let original = fs::read_to_string(&input_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", input_path.display()));
    let formatted = format_policies(&original);

    assert_ne!(
        formatted, original,
        "{fixture} must exercise an actual formatting change"
    );

    let output_file = TempDwFile::write(fixture, &formatted);
    let service = ServiceSchema::defaults();
    assert_eq!(
        canonical_ast(&input_path, &service),
        canonical_ast(output_file.path(), &service),
        "formatting changed the parsed AST for {fixture}"
    );
}

#[test]
fn cedar_policy_file_keeps_the_same_ast_after_formatting() {
    assert_formatting_preserves_ast("cedar.dw");
}

#[test]
fn temporal_policy_file_keeps_the_same_ast_after_formatting() {
    assert_formatting_preserves_ast("temporal.dw");
}

#[test]
fn macro_policy_file_keeps_the_same_expanded_ast_after_formatting() {
    assert_formatting_preserves_ast("macros.dw");
}

struct TempDwFile {
    path: PathBuf,
}

impl TempDwFile {
    fn write(fixture: &str, contents: &str) -> Self {
        let stem = Path::new(fixture)
            .file_stem()
            .and_then(|stem| stem.to_str())
            .expect("fixture has a UTF-8 file stem");

        loop {
            let sequence = NEXT_TEMP_FILE.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "dogwood_formatter_{}_{}_{}.dw",
                std::process::id(),
                sequence,
                stem
            ));
            match OpenOptions::new().write(true).create_new(true).open(&path) {
                Ok(mut file) => {
                    file.write_all(contents.as_bytes())
                        .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
                    return TempDwFile { path };
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("create {}: {error}", path.display()),
            }
        }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDwFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}
