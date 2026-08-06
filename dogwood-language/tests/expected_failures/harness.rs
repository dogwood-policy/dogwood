//! Expected-failure harness.
//!
//! Cases in `corpus/` SHOULD be rejected by the frontend. A case is
//! "correctly rejected" if it fails to build the [`ServiceSchema`] OR fails to
//! lower via [`LoweredPolicySet::from_str`], OR, having lowered, fails
//! [`Validator`] validation (produces at least one validation error). The
//! harness does not care *which* layer catches it — an event-schema *parse*
//! defect surfaces from `ServiceSchema::builder().build()`; syntax / macro /
//! lowering defects (including event-schema *derivation* against the action
//! schema) surface from `LoweredPolicySet::from_str`; and temporal / provider
//! defects surface as `validate` findings. Panics only if a case builds a
//! service schema AND lowers a policy set AND validates cleanly.
//!
//! Additionally, when a case directory contains an `expected_error.txt` file,
//! the harness asserts that the error message matches its contents. This pins
//! error-message parity with Cedar for pure-Cedar parse errors and prevents
//! regressions in diagnostic quality.

use dogwood_language::{
    Error, LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, Validator,
};
use std::path::Path;

/// Extract the error message(s) from running the pipeline on a case.
/// Returns `None` if the case unexpectedly passes all stages.
fn case_error_message(
    policy_src: &str,
    schema_src: &str,
    event_schema: &str,
    providers: Option<&ProviderDeclarations>,
) -> Option<String> {
    let mut builder = ServiceSchema::builder().event_schema_str(event_schema);
    if let Some(p) = providers {
        builder = builder.providers(p.clone());
    }
    let service_schema = match builder.build() {
        Err(e) => return Some(e.to_string()),
        Ok(s) => s,
    };
    let policy_schema = match PolicySchema::from_cedarschema_str(schema_src) {
        Err(e) => return Some(e.to_string()),
        Ok(s) => s,
    };

    match LoweredPolicySet::from_str(policy_src, &service_schema, &policy_schema) {
        Err(e) => {
            let mut messages = Vec::new();
            match &e {
                Error::Parse(errs) => {
                    for err in errs.iter() {
                        messages.push(err.to_string());
                    }
                }
                other => messages.push(other.to_string()),
            }
            Some(messages.join("\n"))
        }
        Ok(policies) => {
            let result = Validator::new().validate(&policies);
            if result.validation_passed() {
                None
            } else {
                let msgs: Vec<String> = result.validation_errors().map(|e| e.to_string()).collect();
                Some(msgs.join("\n"))
            }
        }
    }
}

/// Load a case's policy source, schema, and event schema from its directory.
struct CaseFiles {
    name: String,
    policy_src: String,
    schema_src: String,
    event_schema: String,
    providers: Option<ProviderDeclarations>,
    dir: std::path::PathBuf,
}

fn load_cases() -> Vec<CaseFiles> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/expected_failures/corpus");
    if !root.exists() {
        return Vec::new();
    }

    let event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .unwrap_or_default();

    let mut entries: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().map(|t| t.is_dir()).unwrap_or(false))
        .collect();
    entries.sort_by_key(|e| e.file_name());

    entries
        .into_iter()
        .filter_map(|entry| {
            let dir = entry.path();
            let name = dir.file_name()?.to_string_lossy().to_string();

            let mut policy_paths: Vec<_> = std::fs::read_dir(&dir)
                .ok()?
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
                return None;
            }

            let policy_src = policy_paths
                .iter()
                .map(|p| std::fs::read_to_string(p).unwrap())
                .collect::<Vec<_>>()
                .join("\n");
            let schema_src =
                std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap_or_default();

            let providers = std::fs::read_to_string(dir.join("providers.json"))
                .ok()
                .and_then(|json| ProviderDeclarations::from_json(&json).ok());

            Some(CaseFiles {
                name,
                policy_src,
                schema_src,
                event_schema: event_schema.clone(),
                providers,
                dir,
            })
        })
        .collect()
}

#[test]
fn parse_rejected_cases() {
    let cases = load_cases();
    if cases.is_empty() {
        return;
    }

    let mut unexpectedly_passing = Vec::new();
    let mut correctly_rejected = 0usize;

    for case in &cases {
        let error = case_error_message(
            &case.policy_src,
            &case.schema_src,
            &case.event_schema,
            case.providers.as_ref(),
        );
        if error.is_some() {
            correctly_rejected += 1;
        } else {
            unexpectedly_passing.push(case.name.clone());
        }
    }

    eprintln!(
        "expected_failures: {correctly_rejected} rejected, {} unexpectedly passing",
        unexpectedly_passing.len()
    );
    assert!(
        correctly_rejected > 0,
        "no cases were tested — check that corpus/ contains policy_*.dw files"
    );
    if !unexpectedly_passing.is_empty() {
        panic!(
            "These should FAIL but now parse:\n  {}",
            unexpectedly_passing.join("\n  ")
        );
    }
}

/// When a case directory contains `expected_error.txt`, assert that the
/// actual error message matches its contents. This pins error-message quality
/// and prevents regressions.
#[test]
fn error_messages_match_expected() {
    let cases = load_cases();
    let mut mismatches = Vec::new();
    let mut checked = 0usize;

    for case in &cases {
        let expected_path = case.dir.join("expected_error.txt");
        let expected = match std::fs::read_to_string(&expected_path) {
            Ok(s) => s,
            Err(_) => continue, // no expected_error.txt — skip
        };
        checked += 1;

        let actual = case_error_message(
            &case.policy_src,
            &case.schema_src,
            &case.event_schema,
            case.providers.as_ref(),
        )
        .unwrap_or_else(|| "(no error — case unexpectedly passed)".to_string());

        let expected_trimmed = expected.trim();
        let actual_trimmed = actual.trim();

        if actual_trimmed != expected_trimmed {
            mismatches.push(format!(
                "[{}]\n  expected: {}\n  actual:   {}",
                case.name, expected_trimmed, actual_trimmed,
            ));
        }
    }

    eprintln!(
        "error_messages_match_expected: {checked} checked, {} mismatches",
        mismatches.len()
    );
    if !mismatches.is_empty() {
        panic!(
            "Error message mismatches ({}/{checked}):\n  {}",
            mismatches.len(),
            mismatches.join("\n  ")
        );
    }
}

/// Generate or update `expected_error.txt` files for all cases that don't
/// already have one, or for all cases (when `OVERWRITE=1`). Run with:
///   cargo test --test expected_failures -- --ignored generate_expected_error_files --nocapture
#[test]
#[ignore = "generates expected_error.txt files — run manually"]
fn generate_expected_error_files() {
    let cases = load_cases();
    let overwrite = std::env::var("OVERWRITE").is_ok();
    let mut written = 0usize;
    let mut skipped = 0usize;

    for case in &cases {
        let expected_path = case.dir.join("expected_error.txt");
        if expected_path.exists() && !overwrite {
            skipped += 1;
            continue;
        }

        let error = case_error_message(
            &case.policy_src,
            &case.schema_src,
            &case.event_schema,
            case.providers.as_ref(),
        );
        if let Some(msg) = error {
            std::fs::write(&expected_path, format!("{}\n", msg.trim())).unwrap();
            written += 1;
            eprintln!("wrote: {}/expected_error.txt", case.name);
        } else {
            eprintln!("SKIP (no error): {}", case.name);
        }
    }

    eprintln!(
        "\ngenerate_expected_error_files: {written} written, {skipped} skipped (already exist)"
    );
}
