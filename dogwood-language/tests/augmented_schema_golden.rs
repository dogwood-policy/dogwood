//! What the action schema looks like after Dogwood enriches it with provider
//! values, pinned as golden files.
//!
//! Each case lowers a provider corpus case and compares the exported schema,
//! as `.cedarschema` text and as the Cedar JSON a policy store receives, and the lowered Cedar policies, against
//! `tests/fixtures/augmented_schema/<case>.cedarschema`, `<case>.json` and
//! `<case>.cedar`:
//!
//! - `guardrails_legacy`: case `0075`, a multi-vendor guardrail declarations file with
//!   no `entityTypes`. Only the shared `DogwoodProviders` type is added, and
//!   `threatSeverity` stays `String`.
//! - `guardrails_enums`: case `0076`. The `BedrockGuardrails::Confidence` and
//!   `GuardDuty::Severity` enums are exported into the action schema's
//!   namespace as `Drupe::BedrockGuardrails_Confidence` and
//!   `Drupe::GuardDuty_Severity`; the provider fields and the policies'
//!   enum literals use those names.
//! - `two_namespaces`: case `0081`. The action schema has `App` and `Audit`;
//!   the enum is exported once, into `App`, and `Audit` refers to it by its
//!   full name.
//!
//! To regenerate after an intended change:
//!
//! ```text
//! OVERWRITE=1 cargo test --test augmented_schema_golden
//! ```

use std::path::{Path, PathBuf};

use dogwood_language::{LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema};

fn manifest_dir() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// Lower the provider corpus case `case` with its schema, providers and
/// policies.
fn lower(case: &str) -> LoweredPolicySet {
    let dir = manifest_dir()
        .join("tests/passing/provider_only/corpus")
        .join(case);
    let decls = ProviderDeclarations::from_json_file(dir.join("providers.json"))
        .unwrap_or_else(|e| panic!("{case}: providers.json: {e}"));
    let service = ServiceSchema::builder()
        .event_schema_str(&read(
            &manifest_dir().join("tests/fixtures/request_response.dwschema"),
        ))
        .providers(decls)
        .build()
        .expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(&read(&dir.join("schema.cedarschema")))
        .expect("action schema");
    LoweredPolicySet::from_str(&read(&dir.join("policy_1.dw")), &service, &schema)
        .unwrap_or_else(|e| panic!("{case}: lowering: {e}"))
}

/// Compare `actual` with the golden file `name`, or write it when
/// `OVERWRITE=1`.
fn check_golden(name: &str, actual: &str) {
    let path: PathBuf = manifest_dir()
        .join("tests/fixtures/augmented_schema")
        .join(name);
    if std::env::var("OVERWRITE").is_ok() {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, actual).unwrap();
        return;
    }
    let expected = read(&path);
    assert!(
        expected == actual,
        "{name} differs from the golden file; rerun with OVERWRITE=1 if the change is \
         intended.\n--- expected\n{expected}\n--- actual\n{actual}"
    );
}

fn check_case(case: &str, golden: &str) -> LoweredPolicySet {
    let set = lower(case);
    let text = set.cedar_schema_str().expect("text export");
    check_golden(&format!("{golden}.cedarschema"), &text);
    let json: serde_json::Value =
        serde_json::from_str(&set.cedar_schema_json().expect("JSON export")).unwrap();
    check_golden(
        &format!("{golden}.json"),
        &(serde_json::to_string_pretty(&json).unwrap() + "\n"),
    );
    let policies: String = set
        .as_cedar()
        .policies()
        .map(|p| format!("{p}\n"))
        .collect();
    check_golden(&format!("{golden}.cedar"), &policies);
    set
}

/// The top-level namespaces of `set`'s exported schema.
fn exported_namespaces(set: &LoweredPolicySet) -> Vec<String> {
    let json: serde_json::Value =
        serde_json::from_str(&set.cedar_schema_json().expect("JSON export")).unwrap();
    json.as_object().unwrap().keys().cloned().collect()
}

#[test]
fn guardrails_legacy_declarations_add_only_provider_fields() {
    let set = check_case(
        "0075_enum_guardrails_legacy_providers_unchanged",
        "guardrails_legacy",
    );
    let text = set.cedar_schema_str().unwrap();
    // No vendor namespace is injected (the app's own enums stay as they are).
    for injected in ["namespace BedrockGuardrails", "namespace GuardDuty"] {
        assert!(!text.contains(injected), "`{injected}` injected:\n{text}");
    }
    assert!(text.contains("threatSeverity: String"), "{text}");
}

#[test]
fn guardrails_enums_are_exported_into_the_action_schema_namespace() {
    let set = check_case(
        "0076_enum_guardrails_enums_in_both_vendor_namespaces",
        "guardrails_enums",
    );
    assert_eq!(exported_namespaces(&set), ["Drupe"]);
    let text = set.cedar_schema_str().unwrap();
    for expected in [
        "@dogwood_provider_enum(\"BedrockGuardrails::Confidence\")\n  entity BedrockGuardrails_Confidence enum [\"NONE\", \"LOW\", \"MEDIUM\", \"HIGH\"];",
        "@dogwood_provider_enum(\"GuardDuty::Severity\")\n  entity GuardDuty_Severity enum [\"LOW\", \"MEDIUM\", \"HIGH\", \"CRITICAL\"];",
        "confidence: Drupe::BedrockGuardrails_Confidence",
        "threatSeverity: Drupe::GuardDuty_Severity",
    ] {
        assert!(text.contains(expected), "missing `{expected}` in:\n{text}");
    }
    let policies: Vec<String> = set.as_cedar().policies().map(|p| p.to_string()).collect();
    assert!(
        policies
            .iter()
            .any(|p| p.contains("Drupe::GuardDuty_Severity::\"CRITICAL\"")),
        "{policies:#?}"
    );
}

#[test]
fn a_second_namespace_refers_to_the_one_exported_enum() {
    let set = check_case(
        "0081_enum_unscoped_policy_across_two_namespaces",
        "two_namespaces",
    );
    assert_eq!(exported_namespaces(&set), ["App", "Audit"]);
    let text = set.cedar_schema_str().unwrap();
    assert_eq!(text.matches(" enum [").count(), 1, "one copy:\n{text}");
    assert!(text.contains("result: App::MyGuardrails_Score"), "{text}");
}
