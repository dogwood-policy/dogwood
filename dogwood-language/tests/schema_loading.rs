//! Tests for the two schema-loading conveniences: generating the action
//! schema (a [`PolicySchema`]) directly from an MCP manifest (feature
//! `mcp-schema`), and loading a reusable macro library (on the
//! [`ServiceSchema`]) that policies can call.

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema, Validator, Value,
};

#[cfg(feature = "mcp-schema")]
const MANIFEST: &str = include_str!("../mcp_tools.json");

// A policy over the MCP-generated `GetStockInfo` action.
#[cfg(feature = "mcp-schema")]
const MCP_POLICY: &str = r#"
permit (
    principal,
    action == Drupe::Action::"GetStockInfo",
    resource
)
when {
    context.input.stock == "AMZN"
};
"#;

#[cfg(feature = "mcp-schema")]
#[test]
fn schema_from_mcp_manifest_shortcut() {
    // PolicySchema::from_mcp_manifest generates the action schema from the MCP
    // manifest (Drupe template); the service schema takes the defaults.
    let service = ServiceSchema::defaults();
    let policy_schema =
        PolicySchema::from_mcp_manifest(MANIFEST).expect("builds from MCP manifest");
    let policies = LoweredPolicySet::from_str(MCP_POLICY, &service, &policy_schema)
        .expect("parses against MCP schema");
    let result = Validator::new().validate(&policies);
    assert!(
        result.validation_passed(),
        "policy should validate against the MCP-generated schema, got: {:?}",
        result
            .validation_errors()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );
}

#[cfg(feature = "mcp-schema")]
#[test]
fn schema_builder_mcp_manifest_composes_with_other_parts() {
    // The MCP-generated action schema composes with a default service schema,
    // and produces an authorizer that decides.
    let service = ServiceSchema::defaults();
    let policy_schema =
        PolicySchema::from_mcp_manifest(MANIFEST).expect("builds from MCP manifest");
    let policies =
        LoweredPolicySet::from_str(MCP_POLICY, &service, &policy_schema).expect("parses");

    // The Drupe template's principals are `User`s, and every tool action's
    // context requires the `system` record.
    let mut authorizer = Authorizer::new(policies);
    let allow = Event::builder("Drupe::Action::GetStockInfo", "request")
        .principal("Drupe::User::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "stock", Value::String("AMZN".to_string()))
        .request_context(
            "system",
            "now",
            Value::extension("datetime", "2024-01-01T00:00:00Z"),
        )
        .request_context("input", "stock", Value::String("AMZN".to_string()))
        .build();
    let deny = Event::builder("Drupe::Action::GetStockInfo", "request")
        .principal("Drupe::User::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "stock", Value::String("MSFT".to_string()))
        .request_context(
            "system",
            "now",
            Value::extension("datetime", "2024-01-01T00:00:00Z"),
        )
        .request_context("input", "stock", Value::String("MSFT".to_string()))
        .build();

    assert_eq!(
        authorizer.is_authorized(&allow).map(|r| r.decision()),
        Some(Decision::Allow),
        "AMZN is permitted",
    );
    assert_eq!(
        authorizer.is_authorized(&deny).map(|r| r.decision()),
        Some(Decision::Deny),
        "MSFT is denied",
    );
}

// ─── MCP generation failures ────────────────────────────────────────
//
// Each failure must surface as `Error::McpSchema` tagged with the Dogwood
// stage that failed. Only the stage prefix is asserted; the remainder is the
// upstream crate's message and is deliberately not pinned.

/// The smallest template the generator accepts: one namespace with an MCP
/// principal and an MCP resource.
#[cfg(feature = "mcp-schema")]
const MIN_TEMPLATE: &str = r#"
namespace T {
    @mcp_principal("User")
    entity User;
    @mcp_resource("Gateway")
    entity Gateway;
}
"#;

/// A single tool with an empty object input.
#[cfg(feature = "mcp-schema")]
const MIN_MANIFEST: &str =
    r#"[{ "name": "Ping", "inputSchema": { "type": "object", "properties": {} } }]"#;

/// The `Error::McpSchema` payload of a generation attempt; panics on success
/// or on any other error variant.
#[cfg(feature = "mcp-schema")]
fn mcp_error(result: Result<PolicySchema, dogwood_language::Error>) -> String {
    match result {
        Err(dogwood_language::Error::McpSchema(msg)) => msg,
        Err(other) => panic!("expected Error::McpSchema, got {other:?}"),
        Ok(_) => panic!("expected MCP schema generation to fail"),
    }
}

#[cfg(feature = "mcp-schema")]
fn assert_stage(msg: &str, stage: &str) {
    assert!(
        msg.starts_with(&format!("{stage}: ")),
        "expected stage `{stage}`, got: {msg}"
    );
}

#[cfg(feature = "mcp-schema")]
#[test]
fn minimal_mcp_fixture_generates() {
    // Control for the failure cases below: the minimal inputs succeed.
    PolicySchema::from_mcp_manifest_with_template(MIN_MANIFEST, MIN_TEMPLATE)
        .expect("minimal manifest + template generate");
}

#[cfg(feature = "mcp-schema")]
#[test]
fn mcp_malformed_manifest_json_is_a_manifest_parse_error() {
    let msg = mcp_error(PolicySchema::from_mcp_manifest(r#"[{ "name": "#));
    assert_stage(&msg, "manifest parse");
}

#[cfg(feature = "mcp-schema")]
#[test]
fn mcp_invalid_template_syntax_is_a_template_parse_error() {
    let msg = mcp_error(PolicySchema::from_mcp_manifest_with_template(
        MIN_MANIFEST,
        "namespace T { entity ",
    ));
    assert_stage(&msg, "template parse");
}

#[cfg(feature = "mcp-schema")]
#[test]
fn mcp_template_without_mcp_annotations_is_a_generator_init_error() {
    // Syntactically valid Cedar, but no `@mcp_principal` / `@mcp_resource`.
    let msg = mcp_error(PolicySchema::from_mcp_manifest_with_template(
        MIN_MANIFEST,
        "namespace T { entity User; entity Gateway; }",
    ));
    assert_stage(&msg, "generator init");
}

#[cfg(feature = "mcp-schema")]
#[test]
fn mcp_unresolved_json_schema_ref_is_an_add_actions_error() {
    // Well-formed JSON whose input property points at an undefined `$defs`.
    let manifest = r##"[{
        "name": "Ping",
        "inputSchema": {
            "type": "object",
            "properties": { "x": { "$ref": "#/$defs/Missing" } }
        }
    }]"##;
    let msg = mcp_error(PolicySchema::from_mcp_manifest_with_template(
        manifest,
        MIN_TEMPLATE,
    ));
    assert_stage(&msg, "add actions");
}

// A reusable macro library and a policy that calls one of its macros without
// declaring it inline.
const MACRO_LIB: &str = r#"
def cedar is_amazon(?s) {
    ?s == "AMZN"
};
"#;

const SCHEMA_SRC: &str = r#"
namespace Drupe {
  type GetStockInfoInput = { stock: String };
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  action "GetStockInfo" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: GetStockInfoInput }
  };
}
"#;

const MACRO_POLICY: &str = r#"
permit (
    principal,
    action == Drupe::Action::"GetStockInfo",
    resource
)
when {
    is_amazon(context.input.stock)
};
"#;

#[test]
fn macros_str_library_is_callable_from_a_policy() {
    // The policy calls `is_amazon` but never defines it — it comes from the
    // macro library loaded via `macros_str` on the service schema.
    let service = ServiceSchema::builder()
        .macros_str(MACRO_LIB)
        .build()
        .expect("service schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA_SRC).expect("action schema");
    let policies = LoweredPolicySet::from_str(MACRO_POLICY, &service, &policy_schema)
        .expect("policy parses, library macro resolves");
    let result = Validator::new().validate(&policies);
    assert!(
        result.validation_passed(),
        "macro-using policy should validate, got: {:?}",
        result
            .validation_errors()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );

    let mut authorizer = Authorizer::new(policies);
    let allow = Event::builder("Drupe::Action::GetStockInfo", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "stock", Value::String("AMZN".to_string()))
        .request_context("input", "stock", Value::String("AMZN".to_string()))
        .build();
    assert_eq!(
        authorizer.is_authorized(&allow).map(|r| r.decision()),
        Some(Decision::Allow),
        "the library macro `is_amazon` should permit AMZN",
    );
}

#[test]
fn policy_def_takes_precedence_over_library_macro() {
    // The policy defines `is_amazon` itself (as an always-false check); its
    // own definition must win over the library's, so AMZN is now denied.
    let policy_with_own_def = r#"
        def cedar is_amazon(?s) {
            ?s == "NEVER"
        };
        permit (
            principal,
            action == Drupe::Action::"GetStockInfo",
            resource
        )
        when {
            is_amazon(context.input.stock)
        };
    "#;
    let service = ServiceSchema::builder()
        .macros_str(MACRO_LIB)
        .build()
        .expect("service schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA_SRC).expect("action schema");
    let policies = LoweredPolicySet::from_str(policy_with_own_def, &service, &policy_schema)
        .expect("policy parses");

    let mut authorizer = Authorizer::new(policies);
    let amzn = Event::builder("Drupe::Action::GetStockInfo", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "stock", Value::String("AMZN".to_string()))
        .request_context("input", "stock", Value::String("AMZN".to_string()))
        .build();
    assert_eq!(
        authorizer.is_authorized(&amzn).map(|r| r.decision()),
        Some(Decision::Deny),
        "the policy's own `is_amazon` (always false) must win over the library's",
    );
}
