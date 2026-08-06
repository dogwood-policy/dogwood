//! The core policy operations behind each command: `check-parse`, `validate`,
//! `lower`, and `replay`. Each is one task-oriented function that reads `&str`
//! sources, drives the `dogwood-language` frontend, and returns an owned,
//! serializable report (or an [`OpError`]). The frontend handle types
//! (`ParsedPolicySet`, `LoweredPolicySet`, `Authorizer`, `Response`, `Event`)
//! are constructed and dropped inside these functions, so the rest of the CLI
//! deals only in owned reports — which is also what `--format json` needs.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, ParsedPolicySet, PolicySchema, ProviderDeclarations,
    ServiceSchema, Validator, cedar, mcp_to_cedar_schema, parse_trace,
};
use serde::Serialize;

use crate::error::{Diagnostic, OpError, project};

// ─── schema inputs ───────────────────────────────────────────────────

/// The optional service-schema overrides. A Dogwood schema has two halves: the
/// *action schema* (a Cedar `.cedarschema`) is passed to each op directly as a
/// `&str`, and the *service schema* — the event-schema DSL, provider
/// declarations, and macro library — is optional and defaults to the
/// request/response convention plus the default macros. All-`None` (the
/// [`Default`]) yields [`ServiceSchema::defaults`]. This is the one place the
/// frontend's `ServiceSchema`/`ServiceSchemaBuilder` is touched.
#[derive(Debug, Default, Clone)]
pub struct SchemaInputs<'a> {
    /// Event-schema DSL source (`.dwschema` text). Omit for the default
    /// request/response schema.
    pub event_schema: Option<&'a str>,
    /// Provider declarations as `providers.json` text. Omit for no providers.
    pub providers: Option<&'a str>,
    /// Macro library source. Omit for the default macros.
    pub macros: Option<&'a str>,
}

impl SchemaInputs<'_> {
    /// Assemble the frontend [`ServiceSchema`] these inputs describe. With no
    /// overrides this is [`ServiceSchema::defaults`]; otherwise each supplied
    /// piece is threaded into the builder. Provider JSON is parsed here, so a
    /// malformed `providers.json` surfaces as an [`OpError`] at this point.
    fn build_service_schema(&self) -> Result<ServiceSchema, OpError> {
        // The common case: no overrides → the frontend defaults.
        if self.event_schema.is_none() && self.providers.is_none() && self.macros.is_none() {
            return Ok(ServiceSchema::defaults());
        }

        let mut builder = ServiceSchema::builder();
        if let Some(src) = self.event_schema {
            builder = builder.event_schema_str(src);
        }
        if let Some(json) = self.providers {
            let decls = ProviderDeclarations::from_json(json).map_err(OpError::message)?;
            builder = builder.providers(decls);
        }
        if let Some(src) = self.macros {
            builder = builder.macros_str(src);
        }
        builder
            .build()
            .map_err(|e| OpError::from_diagnostic(&e, None))
    }
}

// ─── check-parse ─────────────────────────────────────────────────────

/// A per-policy summary from a successful parse (pre-lowering, schema-free).
#[derive(Debug, Clone, Serialize)]
pub struct PolicySummary {
    /// Number of `temporal { … }` leaves in the policy.
    pub temporal_count: usize,
    /// Whether the policy uses any temporal clause.
    pub uses_temporal: bool,
    /// Every information-provider invocation, as `Ns::Fn` keys.
    pub provider_invocations: Vec<String>,
    /// Provider invocations naming a provider not declared in the service
    /// schema — a pre-lowering warning surfaced structurally.
    pub undeclared_providers: Vec<String>,
}

/// The result of `check-parse`: the policy set parsed and macro-expanded, with
/// per-policy structural summaries. Syntax and macro errors only — schema-
/// dependent checks (unknown attributes, type errors) are deferred to
/// `validate`.
#[derive(Debug, Clone, Serialize)]
pub struct CheckParseReport {
    pub policy_count: usize,
    pub policies: Vec<PolicySummary>,
}

/// Parse a `.dw` policy set (with macro expansion), reporting only syntax and
/// macro errors. Needs no action schema.
pub fn check_parse(source: &str, schema: &SchemaInputs) -> Result<CheckParseReport, OpError> {
    let service = schema.build_service_schema()?;
    let parsed = ParsedPolicySet::parse(source, &service)
        .map_err(|e| OpError::from_diagnostic(&e, source.to_string()))?;
    Ok(summarize_parsed(&parsed))
}

fn summarize_parsed(parsed: &ParsedPolicySet) -> CheckParseReport {
    let policies = parsed
        .policies()
        .map(|p| PolicySummary {
            temporal_count: p.temporal_count(),
            uses_temporal: p.uses_temporal(),
            provider_invocations: p.provider_invocations().collect(),
            undeclared_providers: p.undeclared_providers().collect(),
        })
        .collect();
    CheckParseReport {
        policy_count: parsed.policy_count(),
        policies,
    }
}

// ─── validate ────────────────────────────────────────────────────────

/// The result of `validate`: whether the policy set type-checks against the
/// schema, plus every finding. A fatal parse/lower error is returned as the
/// `Err` channel instead; this report covers the type-check phase, which
/// accumulates all findings rather than stopping at the first.
#[derive(Debug, Clone, Serialize)]
pub struct ValidateReport {
    /// True iff there are no validation errors (warnings do not fail).
    pub passed: bool,
    /// True iff there are neither errors nor warnings.
    pub passed_without_warnings: bool,
    pub errors: Vec<Diagnostic>,
    pub warnings: Vec<Diagnostic>,
}

/// Parse, lower against the action schema, and type-check. A fatal
/// parse/macro/lowering error is `Err(OpError)`; a successful lower with type
/// findings is `Ok(ValidateReport)`.
pub fn validate_policies(
    source: &str,
    schema: &SchemaInputs,
    action_schema: &str,
) -> Result<ValidateReport, OpError> {
    let lowered = lower_internal(source, schema, action_schema)?;
    let result = Validator::new().validate(&lowered);
    Ok(ValidateReport {
        passed: result.validation_passed(),
        passed_without_warnings: result.validation_passed_without_warnings(),
        errors: result.validation_errors().map(|e| project(e)).collect(),
        warnings: result.validation_warnings().map(|w| project(w)).collect(),
    })
}

// ─── lower ───────────────────────────────────────────────────────────

/// The Cedar artifacts produced by lowering a `.dw` policy set.
#[derive(Debug, Clone, Serialize)]
pub struct LowerArtifacts {
    /// The lowered Cedar policies, rendered to `.cedar` text.
    pub cedar_policies: String,
    /// The augmented Cedar action schema, as `.cedarschema` text.
    pub cedar_schema: String,
    /// The augmented schema in Cedar JSON form.
    pub cedar_schema_json: String,
    /// Whether the exported Cedar fully reproduces the policy semantics.
    /// `false` when temporal/provider fields were hoisted (those need Dogwood
    /// at authorize time — the Cedar alone is not self-sufficient).
    pub self_contained: bool,
    /// The hoisted temporal leaf ids (`context.<id>` slots), for reference.
    pub temporal_fields: Vec<String>,
    /// The hoisted provider field ids (`context.providers.<id>` slots).
    pub provider_fields: Vec<String>,
    /// The event kinds that are decision points.
    pub decision_kinds: Vec<String>,
}

/// Lower a `.dw` policy set to Cedar and return the emitted artifacts (policies
/// + augmented schema in text and Cedar-JSON forms).
pub fn lower_to_cedar(
    source: &str,
    schema: &SchemaInputs,
    action_schema: &str,
) -> Result<LowerArtifacts, OpError> {
    let lowered = lower_internal(source, schema, action_schema)?;
    let err = |e: dogwood_language::Error| OpError::from_diagnostic(&e, source.to_string());
    Ok(LowerArtifacts {
        cedar_policies: lowered.as_cedar().to_string(),
        cedar_schema: lowered.cedar_schema_str().map_err(err)?,
        cedar_schema_json: lowered.cedar_schema_json().map_err(err)?,
        self_contained: lowered.is_self_contained_cedar(),
        temporal_fields: lowered.temporal_fields().map(|f| f.id.clone()).collect(),
        provider_fields: lowered.provider_fields().map(|f| f.id.clone()).collect(),
        decision_kinds: lowered.decision_kinds().map(str::to_string).collect(),
    })
}

// ─── replay ──────────────────────────────────────────────────────────

/// Whether a decision point allowed or denied — the CLI's own verdict type
/// (not cedar's `Decision`, which is not ours to serialize).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Verdict {
    Allow,
    Deny,
}

/// One decision point's verdict, with its determining rules and any evaluation
/// errors. History-only events (which yield no decision) contribute no entry.
#[derive(Debug, Clone, Serialize)]
pub struct TimepointVerdict {
    /// 0-based index of this decision point in the decision stream.
    pub index: usize,
    /// The event's wall-clock timestamp.
    pub timestamp: i64,
    pub verdict: Verdict,
    /// The `.dw` rule indices that determined the decision (empty for an
    /// implicit deny).
    pub determining_rules: Vec<usize>,
    /// Any evaluation errors folded into this decision (a fail-closed deny
    /// carries them here).
    pub errors: Vec<String>,
}

/// The per-timepoint verdict stream from replaying a trace.
#[derive(Debug, Clone, Serialize)]
pub struct ReplayReport {
    pub verdicts: Vec<TimepointVerdict>,
}

/// Lower a `.dw` policy set, then drive a `.log` event trace through a stateful
/// authorizer, returning the per-decision verdict stream (with determining
/// rules and errors — richer than the bool-only `replay_log`).
pub fn replay_trace(
    source: &str,
    schema: &SchemaInputs,
    action_schema: &str,
    log: &str,
) -> Result<ReplayReport, OpError> {
    let lowered = lower_internal(source, schema, action_schema)?;
    let events = parse_trace(log).map_err(|e| OpError::from_diagnostic(&e, log.to_string()))?;

    let mut authorizer = Authorizer::new(lowered);
    let mut verdicts = Vec::new();
    let mut index = 0;
    for event in &events {
        let ts = event.timestamp();
        // A history-only event yields `None` (it updates temporal state but
        // produces no verdict); only decision-kind events emit a line.
        if let Some(response) = authorizer.is_authorized(event) {
            let verdict = match response.decision() {
                Decision::Allow => Verdict::Allow,
                Decision::Deny => Verdict::Deny,
            };
            let determining_rules = response
                .diagnostics()
                .reason()
                .map(|r| r.rule_index)
                .collect();
            let errors = response
                .diagnostics()
                .errors()
                .map(str::to_string)
                .collect();
            verdicts.push(TimepointVerdict {
                index,
                timestamp: ts,
                verdict,
                determining_rules,
                errors,
            });
            index += 1;
        }
    }
    Ok(ReplayReport { verdicts })
}

// ─── shared front-half ───────────────────────────────────────────────

/// Build the service + action schemas and lower the source to a
/// [`LoweredPolicySet`]. The shared front-half of `validate`, `lower`, and
/// `replay`. A fatal parse/macro/lowering/schema error becomes an [`OpError`]
/// carrying the `.dw` source for snippet rendering.
fn lower_internal(
    source: &str,
    schema: &SchemaInputs,
    action_schema: &str,
) -> Result<LoweredPolicySet, OpError> {
    let service = schema.build_service_schema()?;
    let policy_schema = PolicySchema::from_cedarschema_str(action_schema)
        // A bad action schema points at the schema text, not the .dw source.
        .map_err(|e| OpError::from_diagnostic(&e, action_schema.to_string()))?;
    LoweredPolicySet::from_str(source, &service, &policy_schema)
        .map_err(|e| OpError::from_diagnostic(&e, source.to_string()))
}

// ─── schema checks (each schema artifact on its own) ─────────────────

/// The result of a standalone schema check: whether the artifact is
/// well-formed, and any warnings (a valid-but-suspect schema).
#[derive(Debug, Clone, Serialize)]
pub struct SchemaCheckReport {
    /// The artifact kind that was checked (`"action"`, `"event"`, `"providers"`).
    pub kind: String,
    /// True iff the artifact parsed and is well-formed.
    pub ok: bool,
    /// Non-fatal warnings (only the action-schema check surfaces these today).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
}

/// Check a Cedar action schema (`.cedarschema`) in isolation. Uses cedar's own
/// eager parser (which type-checks the schema and reports warnings) — unlike
/// `PolicySchema::from_cedarschema_str`, which defers all checking to lowering.
pub fn check_action_schema(source: &str) -> Result<SchemaCheckReport, OpError> {
    let source = source.strip_prefix('\u{FEFF}').unwrap_or(source);
    match cedar::Schema::from_cedarschema_str(source) {
        Ok((_schema, warnings)) => Ok(SchemaCheckReport {
            kind: "action".to_string(),
            ok: true,
            warnings: warnings.map(|w| w.to_string()).collect(),
        }),
        Err(e) => Err(OpError::from_diagnostic(&e, source.to_string())),
    }
}

/// Check an event-schema DSL file (`.dwschema`) in isolation — that it parses
/// and declares at least one event. Drives `ServiceSchemaBuilder`, which parses
/// (but does not derive) the event schema; derivation needs an action schema
/// and happens at lowering time.
pub fn check_event_schema(source: &str) -> Result<SchemaCheckReport, OpError> {
    ServiceSchema::builder()
        .event_schema_str(source)
        .build()
        .map(|_| SchemaCheckReport {
            kind: "event".to_string(),
            ok: true,
            warnings: Vec::new(),
        })
        .map_err(|e| OpError::from_diagnostic(&e, None))
}

/// Check an information-provider declarations file (`providers.json`) in
/// isolation — that it deserializes and is internally well-formed.
pub fn check_providers(json: &str) -> Result<SchemaCheckReport, OpError> {
    ProviderDeclarations::from_json(json)
        .map(|_| SchemaCheckReport {
            kind: "providers".to_string(),
            ok: true,
            warnings: Vec::new(),
        })
        .map_err(OpError::message)
}

/// Generate a Cedar action schema (`.cedarschema` text) from an MCP `tools/list`
/// manifest, layered on the embedded Drupe template. Returns the generated
/// schema text for the caller to write out.
pub fn generate_mcp_schema(manifest_json: &str) -> Result<String, OpError> {
    mcp_to_cedar_schema(manifest_json).map_err(OpError::message)
}
