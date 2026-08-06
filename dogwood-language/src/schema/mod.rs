//! MCP → Cedar schema generation.
//!
//! A Dogwood schema *is* an MCP tool manifest. The frontend works in
//! Cedar, so the manifest must first be turned into a Cedar schema —
//! that is this module's job, lifting what was previously buried in the
//! test harness into the library's public surface.
//!
//! The generator ([`cedar_policy_mcp_schema_generator`]) layers one
//! Cedar action per MCP tool (with input/output context records derived
//! from the tool's JSON schema) on top of a **template** stub that
//! supplies the principals, resources, and base context
//! (`@mcp_principal` / `@mcp_resource` / `@mcp_context`). We embed the
//! Drupe template as the default; callers with their own stub use
//! [`mcp_to_cedar_schema_with_template`].

use cedar_policy_core::extensions::Extensions;
use cedar_policy_core::validator::RawName;
use cedar_policy_core::validator::json_schema::Fragment;
use cedar_policy_mcp_schema_generator::{SchemaGenerator, SchemaGeneratorConfig};
use mcp_tools_sdk::description::ServerDescription;

/// The default Cedar template stub (Drupe): principals
/// (`OAuthUser` / `IamEntity` / `UnauthenticatedUser`), the `Gateway`
/// resource, the `system` context, and the base MCP action hierarchy.
pub const DRUPE_TEMPLATE: &str = include_str!("../../configuration/mcp-template.cedarschema");

/// The proven generator configuration: include tool outputs, encode
/// numbers as `decimal`, flatten namespaces so action names are
/// unqualified, and deduplicate entity types with equivalent definitions
/// across tools (matching the production setting).
fn default_config() -> SchemaGeneratorConfig {
    SchemaGeneratorConfig::default()
        .include_outputs(true)
        .encode_numbers_as_decimal(true)
        .flatten_namespaces(true)
        .deduplicate_entity_types(true)
}

/// Generate a Cedar schema from an MCP tool manifest, using the
/// embedded Drupe template.
///
/// `manifest_json` is an MCP `tools/list` payload (or a JSON array of
/// tool descriptions). Returns the `.cedarschema` text to pass to
/// [`PolicySchema::from_cedarschema_str`](crate::PolicySchema::from_cedarschema_str)
/// (or use [`PolicySchema::from_mcp_manifest`](crate::PolicySchema::from_mcp_manifest)
/// to do both in one step).
pub fn mcp_to_cedar_schema(manifest_json: &str) -> Result<String, String> {
    mcp_to_cedar_schema_with_template(manifest_json, DRUPE_TEMPLATE)
}

/// Generate a Cedar schema from an MCP tool manifest against a
/// caller-supplied Cedar template stub (in `.cedarschema` text).
pub fn mcp_to_cedar_schema_with_template(
    manifest_json: &str,
    template: &str,
) -> Result<String, String> {
    let manifest_json = manifest_json.strip_prefix('\u{FEFF}').unwrap_or(manifest_json);
    let template = template.strip_prefix('\u{FEFF}').unwrap_or(template);
    let template = Fragment::<RawName>::from_cedarschema_str(template, Extensions::all_available())
        .map_err(|e| format!("template parse: {e}"))?
        .0;

    let server = ServerDescription::from_json_str(manifest_json)
        .map_err(|e| format!("manifest parse: {e}"))?;

    let mut generator = SchemaGenerator::new_with_config(template, default_config())
        .map_err(|e| format!("generator init: {e}"))?;
    generator
        .add_actions_from_server_description(&server)
        .map_err(|e| format!("add actions: {e}"))?;
    generator
        .get_schema()
        .to_cedarschema()
        .map_err(|e| format!("serialize: {e}"))
}
