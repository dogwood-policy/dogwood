//! A temporal `.dw` case parses and lowers to a `LoweredPolicySet` (hoisting the
//! temporal leaf), and validates cleanly against the augmented schema —
//! all through the public Cedar-parity API.
//!
//! Build a [`ServiceSchema`] + [`PolicySchema`] (action schema + the
//! request/response event schema), then [`LoweredPolicySet::from_str`] to
//! parse + lower, then a [`Validator`] to validate. The public API exposes
//! whether a policy set is self-contained Cedar (no temporal/provider leaves
//! hoisted) but not the count or internals of hoisted leaves, so leaf-count
//! assertions are re-expressed as presence.

use std::path::Path;

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema, Validator};

fn temporal_case() -> (String, String, String) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let dir = root
        .join("tests/docs_as_tests/temporal_cases/documentation_0300_formerly_within_short_window");
    let policy = std::fs::read_to_string(dir.join("policy_1.dw")).unwrap();
    let schema = std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap();
    let event_schema =
        std::fs::read_to_string(root.join("tests/fixtures/request_response.dwschema")).unwrap();
    (policy, schema, event_schema)
}

/// Build the case `ServiceSchema` + `PolicySchema` from the action schema +
/// request/response event schema, with no provider declarations.
fn build_schema(schema_src: &str, event_schema: &str) -> (ServiceSchema, PolicySchema) {
    let service = ServiceSchema::builder()
        .event_schema_str(event_schema)
        .build()
        .expect("service schema builds");
    let policy_schema =
        PolicySchema::from_cedarschema_str(schema_src).expect("policy schema builds");
    (service, policy_schema)
}

#[test]
fn parse_hoists_temporal_leaf() {
    let (src, schema_src, event_schema) = temporal_case();
    let (service, policy_schema) = build_schema(&schema_src, &event_schema);
    let policies =
        LoweredPolicySet::from_str(&src, &service, &policy_schema).expect("parses + lowers");

    // The temporal leaf was recognized and hoisted, so the policy set is not
    // self-contained Cedar. The public API exposes the *presence* of hoisted
    // temporal/provider leaves, not their count or internals — so the old
    // `bundle.temporal.len() == 1`, `bundle.providers.is_empty()`, and
    // per-leaf id/action checks are collapsed into this single presence
    // assertion.
    assert!(
        !policies.is_self_contained_cedar(),
        "a temporal (or provider) leaf should have hoisted out",
    );
}

#[test]
fn validate_temporal_case_is_clean() {
    let (src, schema_src, event_schema) = temporal_case();
    let (service, policy_schema) = build_schema(&schema_src, &event_schema);
    let policies =
        LoweredPolicySet::from_str(&src, &service, &policy_schema).expect("parses + lowers");
    let result = Validator::new().validate(&policies);
    assert!(
        result.validation_passed(),
        "expected clean validation, got: {:?}",
        result
            .validation_errors()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );
}
