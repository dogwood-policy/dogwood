#![doc = include_str!("../README.md")]

pub mod bounds;
pub mod error;
pub mod fail_closed;
pub mod live;
pub mod ops;
pub mod providers;

pub use error::{Diagnostic, Label, OpError, Severity};
pub use live::{AuthorizerDecision, EntityInput, EntityRef, EventInput, LiveAuthorizer};
pub use ops::{
    CheckParseReport, ExplainReport, LowerArtifacts, PolicySummary, RejectedEvent, ReplayReport,
    SchemaCheckReport, SchemaInputs, TimepointVerdict, ValidateReport, Verdict,
};

/// The frontend this crate drives, re-exported so a binding can name its
/// types (`Value`, `Informalization`, …) without a second, possibly
/// version-skewed dependency on it.
pub use dogwood_language;

/// Build the optional service-schema overrides from three optional strings,
/// applying the [`providers`] `scriptFile` guard first.
///
/// Supplied provider text is parsed here purely to reject a declaration that
/// cannot work from text, and parsed again by [`SchemaInputs`] when it is
/// used. Two parses of a small JSON document, only when providers are
/// supplied at all.
pub fn inputs<'a>(
    event_schema: Option<&'a str>,
    providers: Option<&'a str>,
    macros: Option<&'a str>,
) -> Result<SchemaInputs<'a>, OpError> {
    if let Some(json) = providers {
        providers::parse_declarations(json)?;
    }
    Ok(SchemaInputs {
        event_schema,
        providers,
        macros,
    })
}

/// [`ops::replay_trace`] with the fail-closed rule applied to every verdict,
/// exactly as [`LiveAuthorizer::is_authorized`] applies it (see
/// [`fail_closed`]), so the bindings' `replay` and live paths agree on every
/// event. The CLI's `dogwood replay` reports Cedar's decision as is.
pub fn replay(
    source: &str,
    schema: &SchemaInputs,
    action_schema: &str,
    log: &str,
) -> Result<ReplayReport, OpError> {
    let mut report = ops::replay_trace(source, schema, action_schema, log)?;
    for v in &mut report.verdicts {
        fail_closed::fail_closed(&mut v.verdict, &mut v.determining_rules, &v.errors);
    }
    Ok(report)
}

/// [`ops::check_providers`] with the [`providers`] `scriptFile` guard run
/// first, so a well-formed but unresolvable declaration fails rather than
/// reporting `ok: true`.
pub fn check_providers(json: &str) -> Result<SchemaCheckReport, OpError> {
    providers::parse_declarations(json)?;
    ops::check_providers(json)
}

/// [`ops::generate_mcp_schema`] with the manifest bounded first: it comes from
/// a third-party MCP server, and its parser recurses per nesting level with no
/// cap of its own.
#[cfg(feature = "mcp-schema")]
pub fn mcp_to_cedar_schema(manifest_json: &str) -> Result<String, OpError> {
    bounds::check_json_text(
        "manifest",
        manifest_json,
        bounds::MAX_MANIFEST_BYTES,
        bounds::MAX_MANIFEST_DEPTH,
    )
    .map_err(OpError::message)?;
    ops::generate_mcp_schema(manifest_json)
}
