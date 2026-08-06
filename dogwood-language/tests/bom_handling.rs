//! Tests that a UTF-8 BOM (U+FEFF) at the start of input does not cause
//! parse failures across all user-facing entry points.
//!
//! Windows editors (Notepad, VS Code, PowerShell Out-File) often prepend
//! a BOM. Dogwood strips it at each entry point so users never see a
//! confusing "unexpected token" or "expected value at line 1" error.

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema,
};

const BOM: &str = "\u{FEFF}";

const SCHEMA: &str = r#"namespace Ns {
  entity User;
  entity Res;
  action "Act" appliesTo {
    principal: [User], resource: [Res],
    context: { x: Long }
  };
}"#;

const POLICY: &str = r#"permit (principal, action == Ns::Action::"Act", resource)
when { context.x > 0 };"#;

// ─── PolicySchema::from_cedarschema_str ──────────────────────────────

#[test]
fn cedarschema_with_bom_parses_and_lowers() {
    let bom_schema = format!("{BOM}{SCHEMA}");
    let service = ServiceSchema::defaults();
    let policy_schema = PolicySchema::from_cedarschema_str(&bom_schema).expect("schema parses");
    // If the BOM leaked through, lower() would fail with "invalid token"
    LoweredPolicySet::from_str(POLICY, &service, &policy_schema).expect("policy lowers");
}

#[test]
fn cedarschema_without_bom_still_works() {
    let service = ServiceSchema::defaults();
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema parses");
    LoweredPolicySet::from_str(POLICY, &service, &policy_schema).expect("policy lowers");
}

// ─── ProviderDeclarations::from_json ─────────────────────────────────

const PROVIDERS_JSON: &str = r#"{
  "availableProviders": {
    "Risk::Score": {
      "argumentTypes": [{ "paramType": "string" }],
      "outputType": { "paramType": "long" }
    }
  }
}"#;

#[test]
fn providers_json_with_bom_parses() {
    let bom_json = format!("{BOM}{PROVIDERS_JSON}");
    ProviderDeclarations::from_json(&bom_json).expect("providers parse with BOM");
}

#[test]
fn providers_json_without_bom_still_works() {
    ProviderDeclarations::from_json(PROVIDERS_JSON).expect("providers parse without BOM");
}

// ─── mcp_to_cedar_schema ─────────────────────────────────────────────

const MCP_MANIFEST: &str = include_str!("../mcp_tools.json");

#[test]
fn mcp_manifest_with_bom_generates_schema() {
    use dogwood_language::mcp_to_cedar_schema;
    let bom_manifest = format!("{BOM}{MCP_MANIFEST}");
    mcp_to_cedar_schema(&bom_manifest).expect("MCP manifest parses with BOM");
}

#[test]
fn mcp_manifest_without_bom_still_works() {
    use dogwood_language::mcp_to_cedar_schema;
    mcp_to_cedar_schema(MCP_MANIFEST).expect("MCP manifest parses without BOM");
}
