//! [`PolicySchema`] — the **action schema** half of a Dogwood schema: a Cedar
//! `.cedarschema` (entity types + actions), supplied directly or generated
//! from an MCP tool manifest.
//!
//! This is the input that typically arrives *late* and changes *per customer*,
//! so it is split out from the [`ServiceSchema`](crate::ServiceSchema) (the
//! fixed, service-provided half). [`lower`](crate::policy_set::ParsedPolicySet::lower)
//! takes it as its only extra input beyond the parsed set: lowering augments
//! this schema with the hoisted `context.<id>` fields the policies reference,
//! and derives the event schema against it.
//!
//! Construct one with [`PolicySchema::from_cedarschema_str`] (Cedar text) or
//! [`PolicySchema::from_mcp_manifest`] / [`PolicySchema::from_mcp_manifest_with_template`]
//! (generated from an MCP `tools/list` manifest). The action-schema text is
//! resolved eagerly at construction, so MCP-generation failures surface here
//! rather than at lower time.

use crate::api::Error;

/// The action schema — a Cedar `.cedarschema`, resolved to text at
/// construction (MCP generation, if any, has already run).
///
/// Dogwood's per-customer schema input. Pair it with a
/// [`ServiceSchema`](crate::ServiceSchema) to lower a
/// [`ParsedPolicySet`](crate::policy_set::ParsedPolicySet).
#[derive(Debug, Clone)]
pub struct PolicySchema {
    /// The Cedar action-schema source text (retained because lowering
    /// re-parses it while augmenting, and derives the event schema against it).
    action_schema_src: String,
}

impl PolicySchema {
    /// Build a policy schema from Cedar `.cedarschema` action-schema text.
    ///
    /// Named to mirror `cedar_policy::Schema::from_cedarschema_str`. The text
    /// is not typechecked here — that happens during lowering / validation.
    pub fn from_cedarschema_str(action_schema_src: &str) -> Result<PolicySchema, Error> {
        let action_schema_src = action_schema_src.strip_prefix('\u{FEFF}').unwrap_or(action_schema_src);
        Ok(PolicySchema {
            action_schema_src: action_schema_src.to_string(),
        })
    }

    /// Build a policy schema by generating the action schema from an MCP
    /// `tools/list` manifest, layered on the embedded Drupe template.
    ///
    /// The manifest is turned into Cedar `.cedarschema` text eagerly (a Dogwood
    /// action schema *is* an MCP manifest); a generation failure surfaces as
    /// [`Error::McpSchema`].
    pub fn from_mcp_manifest(manifest_json: &str) -> Result<PolicySchema, Error> {
        let action_schema_src = crate::schema::mcp_to_cedar_schema(manifest_json)
            .map_err(|e| Error::McpSchema(e.to_string()))?;
        Ok(PolicySchema { action_schema_src })
    }

    /// Like [`from_mcp_manifest`](PolicySchema::from_mcp_manifest), but against
    /// a caller-supplied Cedar template stub instead of the embedded Drupe
    /// template.
    pub fn from_mcp_manifest_with_template(
        manifest_json: &str,
        template: &str,
    ) -> Result<PolicySchema, Error> {
        let action_schema_src =
            crate::schema::mcp_to_cedar_schema_with_template(manifest_json, template)
                .map_err(|e| Error::McpSchema(e.to_string()))?;
        Ok(PolicySchema { action_schema_src })
    }

    // ─── crate-internal accessors (used by lowering) ─────────────────

    pub(crate) fn action_schema_src(&self) -> &str {
        &self.action_schema_src
    }
}
