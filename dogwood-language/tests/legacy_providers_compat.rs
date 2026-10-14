//! `providers.json` files written before enum-typed provider values
//! (`entityTypes`, `paramType: "entity"`) keep loading, lowering and
//! validating unchanged. The only new signal is a validation *warning* for an
//! unknown `paramType`, which is still typed `String` (deprecated).
//!
//! A realistic multi-vendor guardrail declarations file lives in the
//! provider corpus case `0075_enum_guardrails_legacy_providers_unchanged`: two vendor
//! namespaces in one file, zero-argument methods, nested records.

use std::path::{Path, PathBuf};

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, ValidationWarning,
    Validator,
};

const GUARDRAILS_PROVIDERS: &str = "tests/passing/provider_only/corpus/\
     0075_enum_guardrails_legacy_providers_unchanged/providers.json";

fn manifest_dir() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

const APP_SCHEMA: &str = r#"
namespace Drupe {
  entity Gateway;
  entity OAuthUser;
  action "Invoke" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: { prompt: String } }
  };
}
"#;

/// Lower and validate `policy` against `decls` and [`APP_SCHEMA`].
fn lower(policy: &str, decls: ProviderDeclarations) -> LoweredPolicySet {
    let service = ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(APP_SCHEMA).expect("app schema");
    LoweredPolicySet::from_str(policy, &service, &schema).expect("policy lowers")
}

fn extension_warnings(set: &LoweredPolicySet) -> Vec<String> {
    let result = Validator::new().validate(set);
    assert!(
        result.validation_passed(),
        "{:?}",
        result
            .validation_errors()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    );
    result
        .validation_warnings()
        .filter(|w| matches!(w, ValidationWarning::Extension { .. }))
        .map(ToString::to_string)
        .collect()
}

/// Every `providers.json` under `dir`, recursively.
fn providers_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("read dir") {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            providers_files(&path, out);
        } else if path.file_name().is_some_and(|n| n == "providers.json") {
            out.push(path);
        }
    }
}

#[test]
fn every_pre_enum_corpus_file_loads_without_errors_or_warnings() {
    let mut files = Vec::new();
    for dir in [
        "tests/passing",
        "tests/expected_failures",
        "../dogwood-docs/examples",
    ] {
        providers_files(&manifest_dir().join(dir), &mut files);
    }
    let mut legacy = 0;
    for path in &files {
        let text = std::fs::read_to_string(path).expect("read");
        if text.contains("entityType") {
            continue; // uses the new keys
        }
        legacy += 1;
        let decls = ProviderDeclarations::from_json_file(path)
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        assert!(decls.entity_type_decls.is_empty(), "{}", path.display());
        // The one deliberate unknown `paramType` in the corpora.
        if !path
            .to_string_lossy()
            .contains("0053_enum_accept_unknown_param_type")
        {
            assert_eq!(decls.warnings(), Vec::<String>::new(), "{}", path.display());
        }
    }
    // Guard against the sweep silently finding nothing (e.g. a moved corpus).
    assert!(
        legacy >= 90,
        "only {legacy} pre-enum providers.json files found"
    );
}

#[test]
fn guardrails_declarations_load_lower_and_validate_unchanged() {
    let decls = ProviderDeclarations::from_json_file(manifest_dir().join(GUARDRAILS_PROVIDERS))
        .expect("loads");
    assert!(decls.entity_type_decls.is_empty());
    assert!(decls.warnings().is_empty(), "{:?}", decls.warnings());

    let set = lower(
        r#"
        forbid (principal, action == Drupe::Action::"Invoke", resource)
        when {
            BedrockGuardrails::ContentFilter([context.input.prompt], ["VIOLENCE"])
                .maxConfidenceScore().greaterThan(decimal("0.5"))
            || GuardDuty::ThreatDetector([context.input.prompt]).threatSeverity == "HIGH"
        };
        "#,
        decls,
    );
    assert!(extension_warnings(&set).is_empty());

    // Fields keep their pre-enum Cedar types, and nothing is injected.
    let text = set.cedar_schema_str().expect("cedarschema text");
    assert!(text.contains("policy_0_p_0: decimal"), "{text}");
    assert!(text.contains("threatSeverity: String"), "{text}");
    assert!(!text.contains("enum"), "{text}");
}

#[test]
fn unknown_param_type_still_validates_but_warns_once_at_the_call() {
    let decls = ProviderDeclarations::from_json(
        r#"{ "availableProviders": { "Vendor::Scan": {
            "argumentTypes": [ { "paramType": "string" } ],
            "outputType": { "paramType": "record", "fields": {
                "verdict": { "paramType": "string" },
                "scannedAt": { "paramType": "datetime" },
                "risk": { "paramType": "Decimal" } },
                "required": ["verdict", "scannedAt", "risk"] } } } }"#,
    )
    .expect("an unknown paramType without an entity type still loads");

    // Called twice; each fallback is reported once.
    let set = lower(
        r#"
        forbid (principal, action == Drupe::Action::"Invoke", resource)
        when { Vendor::Scan(context.input.prompt).verdict == "block" };
        forbid (principal, action == Drupe::Action::"Invoke", resource)
        when { Vendor::Scan(context.input.prompt).scannedAt == "never" };
        "#,
        decls,
    );
    let warnings = extension_warnings(&set);
    assert_eq!(warnings.len(), 2, "{warnings:#?}");
    assert!(
        warnings[0].contains(
            "provider `Vendor::Scan` outputType.risk: unknown paramType `Decimal` does not \
             match a known paramType; falling back to String"
        ),
        "{warnings:#?}"
    );
    assert!(
        warnings[1].contains(
            "provider `Vendor::Scan` outputType.scannedAt: unknown paramType `datetime` does \
             not match a known paramType; falling back to String"
        ),
        "{warnings:#?}"
    );
}

#[test]
fn a_provider_that_is_never_called_does_not_warn_at_validation() {
    let decls = ProviderDeclarations::from_json(
        r#"{ "availableProviders": {
            "Vendor::Unused": { "outputType": { "paramType": "bolean" } },
            "Vendor::Used": { "argumentTypes": [ { "paramType": "string" } ],
                              "outputType": { "paramType": "bool" } } } }"#,
    )
    .expect("loads");
    assert_eq!(
        decls.warnings().len(),
        1,
        "the file-level check still reports it"
    );
    let set = lower(
        r#"
        permit (principal, action == Drupe::Action::"Invoke", resource)
        when { Vendor::Used(context.input.prompt) };
        "#,
        decls,
    );
    assert!(extension_warnings(&set).is_empty());
}
