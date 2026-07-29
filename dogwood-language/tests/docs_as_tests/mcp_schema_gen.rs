//! MCP → Cedar schema generation, end to end.
//!
//! Confirms `mcp_to_cedar_schema` turns the MCP tool manifest into a
//! Cedar schema, and that a pure-Cedar policy validates against the
//! *generated* schema (not just the committed one).
//!
//! Under the new Cedar-parity API the policy schema is built with
//! `PolicySchema::from_cedarschema_str` paired with `ServiceSchema::defaults()`
//! (default event schema), policies are lowered with
//! `LoweredPolicySet::from_str`, and validation runs through
//! `Validator::new(schema).validate(..)`.

use dogwood_language::mcp_to_cedar_schema;
use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema, Validator};

const MANIFEST: &str = include_str!("../../mcp_tools.json");

#[test]
fn generates_cedar_schema_from_mcp_manifest() {
    let schema = mcp_to_cedar_schema(MANIFEST).expect("generates");

    // The generated schema contains the Drupe template's principals
    // and the tool actions from the manifest.
    assert!(schema.contains("User"), "template principals present");
    assert!(schema.contains("SellShares"), "tool action present");
    assert!(schema.contains("GetStockInfo"), "tool action present");
}

#[test]
fn generated_schema_validates_a_policy() {
    let schema_src = mcp_to_cedar_schema(MANIFEST).expect("generates");

    let policy = r#"
        permit (
            principal,
            action == Drupe::Action::"GetStockInfo",
            resource
        )
        when {
            context.input.stock == "AMZN"
        };
    "#;

    // Pure-Cedar policy: use the DEFAULT event schema so `request` is a
    // decision kind. (The old code passed event schema "" here.)
    let service = ServiceSchema::defaults();
    let policy_schema =
        PolicySchema::from_cedarschema_str(&schema_src).expect("builds against generated schema");
    let policies = LoweredPolicySet::from_str(policy, &service, &policy_schema)
        .expect("parses against generated schema");
    let result = Validator::new().validate(&policies);
    assert!(
        result.validation_passed(),
        "policy should validate against the generated schema, got: {:?}",
        result
            .validation_errors()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );
}
