//! Immutable, LSP-independent access to the workspace Dogwood frontend.
//!
//! Diagnostic projection and operation sequencing are adapted from
//! `dogwood-ops/src/error.rs` and `dogwood-ops/src/ops.rs`. Local changes add
//! source-kind attribution, serializable equality, and an operational resource
//! envelope; production never invokes the CLI as a subprocess.

use dogwood_language::{
    DEFAULT_MAX_DEPTH, Error as DogwoodError, ParsedPolicySet, PolicySchema, ProviderDeclarations,
    ServiceSchema, Validator,
};
use miette::Diagnostic as MietteDiagnostic;
use serde::{Deserialize, Serialize};

/// Maximum bytes accepted for any one source passed to a recursive frontend.
pub const MAX_FRONTEND_SOURCE_BYTES: usize = 1024 * 1024;

/// Maximum mixed delimiter nesting accepted before invoking a recursive parser.
///
/// Dogwood refuses source nested deeper than [`DEFAULT_MAX_DEPTH`] brackets as
/// a parse error at its default limit, which the LSP parses with, so this
/// preflight admits exactly the bracket nesting Dogwood does.
pub const MAX_FRONTEND_NESTING: usize = DEFAULT_MAX_DEPTH;

/// Maximum non-trivia lexical tokens in one structural expression segment.
///
/// This bounds the preflight's work per segment, not Dogwood's recursion:
/// Dogwood refuses an expression tree deeper than [`DEFAULT_MAX_DEPTH`] as a
/// parse error itself, so a deep chain within this budget (a run of 33 `&&` terms
/// is under 100 tokens) still reaches Dogwood and fails there. Expressions
/// that are wide rather than deep, such as `||` of `&&` groups, may use
/// the whole budget.
///
/// The preflight scanner does not classify Dogwood keywords or operators.
/// Balanced delimiters create child segments and commas separate sibling
/// expressions, so independent clauses, call arguments, and collection
/// elements do not consume one shared budget.
pub const MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS: usize = 512;

/// Maximum recursive unary/member/postfix spine in an expression.
///
/// Generic token count alone permits recursive chains to approach 512 nodes.
/// The scanner therefore tracks structural operand continuations: unary
/// punctuation before an operand and field, call, or index access after one.
/// It does not classify keywords or infix operators. A spine of this many
/// nodes puts its operand at depth [`DEFAULT_MAX_DEPTH`], the deepest tree
/// Dogwood builds at its default limit, so this admits no spine that Dogwood
/// refuses.
pub const MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN: usize = DEFAULT_MAX_DEPTH - 1;

/// The source artifact associated with a finding or operational limit.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SourceKind {
    Policy,
    ActionSchema,
    EventSchema,
    Providers,
    Macros,
}

impl SourceKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Policy => "policy",
            Self::ActionSchema => "action schema",
            Self::EventSchema => "event schema",
            Self::Providers => "providers",
            Self::Macros => "macros",
        }
    }
}

/// Immutable borrowed inputs for a complete Dogwood validation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BundleInput<'a> {
    pub policy: &'a str,
    pub action_schema: &'a str,
    pub event_schema: Option<&'a str>,
    pub providers: Option<&'a str>,
    pub macros: Option<&'a str>,
}

/// Immutable borrowed inputs for schema-independent strict policy parsing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PolicyParseInput<'a> {
    pub policy: &'a str,
    pub event_schema: Option<&'a str>,
    pub providers: Option<&'a str>,
    pub macros: Option<&'a str>,
}

impl<'a> From<&BundleInput<'a>> for PolicyParseInput<'a> {
    fn from(input: &BundleInput<'a>) -> Self {
        Self {
            policy: input.policy,
            event_schema: input.event_schema,
            providers: input.providers,
            macros: input.macros,
        }
    }
}

#[derive(Clone, Copy)]
struct ServiceInputs<'a> {
    event_schema: Option<&'a str>,
    providers: Option<&'a str>,
    macros: Option<&'a str>,
}

impl<'a> From<&BundleInput<'a>> for ServiceInputs<'a> {
    fn from(input: &BundleInput<'a>) -> Self {
        Self {
            event_schema: input.event_schema,
            providers: input.providers,
            macros: input.macros,
        }
    }
}

impl<'a> From<&PolicyParseInput<'a>> for ServiceInputs<'a> {
    fn from(input: &PolicyParseInput<'a>) -> Self {
        Self {
            event_schema: input.event_schema,
            providers: input.providers,
            macros: input.macros,
        }
    }
}

/// A frontend operation's mutually exclusive result channels.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case", tag = "outcome", content = "value")]
pub enum FrontendOutcome<R> {
    /// The operation reached its non-fatal report phase.
    Report(R),
    /// Parsing, schema construction, macro expansion, or lowering failed.
    Fatal(FatalReport),
    /// An input exceeded the pre-parse resource envelope.
    OperationalLimit(OperationalLimitExceeded),
}

/// Which operational resource was rejected.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum OperationalLimitKind {
    SourceBytes,
    StructuralNesting,
    ExpressionChain,
}

/// A non-Dogwood outcome returned before invoking a recursive frontend.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct OperationalLimitExceeded {
    pub source_kind: SourceKind,
    pub kind: OperationalLimitKind,
    pub limit: usize,
    pub observed: usize,
}

/// Severity projected from `miette`; absent upstream severity means error.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Error,
    Warning,
    Advice,
}

impl From<Option<miette::Severity>> for Severity {
    fn from(severity: Option<miette::Severity>) -> Self {
        match severity {
            Some(miette::Severity::Warning) => Self::Warning,
            Some(miette::Severity::Advice) => Self::Advice,
            Some(miette::Severity::Error) | None => Self::Error,
        }
    }
}

/// One exact byte label reported by Dogwood or Cedar.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct DiagnosticLabel {
    pub start: usize,
    pub len: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
}

/// One owned frontend finding.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Finding {
    pub severity: Severity,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    pub message: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub labels: Vec<DiagnosticLabel>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub help: Option<String>,
    /// `true` when at least one label exists, including a zero-width label.
    pub spanned: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_kind: Option<SourceKind>,
}

/// The fatal channel: a primary diagnostic followed by related diagnostics.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct FatalReport {
    pub diagnostic: Box<Finding>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub related: Vec<Finding>,
}

/// The accumulated, non-fatal result of complete bundle validation.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ValidationReport {
    /// `true` when no validation errors were emitted.
    pub passed: bool,
    /// `true` when neither errors nor warnings were emitted.
    pub passed_without_warnings: bool,
    /// Errors in upstream emission order.
    pub errors: Vec<Finding>,
    /// Warnings in upstream emission order.
    pub warnings: Vec<Finding>,
}

/// Owned structural information for one strictly parsed policy.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct PolicySummary {
    pub temporal_count: usize,
    pub uses_temporal: bool,
    pub provider_invocations: Vec<String>,
    pub undeclared_providers: Vec<String>,
}

/// The successful report from schema-independent strict policy parsing.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct PolicyParseReport {
    pub policy_count: usize,
    pub policies: Vec<PolicySummary>,
}

/// The successful report from strict event-schema parsing.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct EventSchemaParseReport {
    pub valid: bool,
}

/// Validate a complete policy bundle with the same phase order as the CLI.
pub fn validate_bundle(input: &BundleInput<'_>) -> FrontendOutcome<ValidationReport> {
    let service = match build_service_schema(ServiceInputs::from(input)) {
        Ok(service) => service,
        Err(failure) => return failure.into_outcome(),
    };
    if let Err(limit) = preflight_source(SourceKind::ActionSchema, input.action_schema) {
        return FrontendOutcome::OperationalLimit(limit);
    }
    let policy_schema = match PolicySchema::from_cedarschema_str(input.action_schema) {
        Ok(schema) => schema,
        Err(error) => {
            return FrontendOutcome::Fatal(fatal_from_diagnostic(
                &error,
                Some(SourceKind::ActionSchema),
            ));
        }
    };
    if let Err(limit) = preflight_source(SourceKind::Policy, input.policy) {
        return FrontendOutcome::OperationalLimit(limit);
    }
    if let Err(limit) = preflight_source(
        SourceKind::Macros,
        input.macros.unwrap_or(dogwood_language::DEFAULT_MACROS),
    ) {
        return FrontendOutcome::OperationalLimit(limit);
    }
    let parsed = match ParsedPolicySet::parse(input.policy, &service) {
        Ok(parsed) => parsed,
        Err(error) => {
            let source_kind = policy_error_source_kind(&error, input.policy, input.macros);
            return FrontendOutcome::Fatal(fatal_from_diagnostic(&error, source_kind));
        }
    };
    let lowered = match parsed.lower(&policy_schema) {
        Ok(lowered) => lowered,
        Err(error) => {
            let source_kind = lower_error_source_kind(&error, input.policy, input.macros);
            return FrontendOutcome::Fatal(fatal_from_diagnostic(&error, source_kind));
        }
    };

    let result = Validator::new().validate(&lowered);
    FrontendOutcome::Report(ValidationReport {
        passed: result.validation_passed(),
        passed_without_warnings: result.validation_passed_without_warnings(),
        errors: result
            .validation_errors()
            .map(|error| project(error, Some(SourceKind::Policy)))
            .collect(),
        warnings: result
            .validation_warnings()
            .map(|warning| project(warning, Some(SourceKind::Policy)))
            .collect(),
    })
}

/// Strictly parse and macro-expand policy source without an action schema.
pub fn parse_policy(input: &PolicyParseInput<'_>) -> FrontendOutcome<PolicyParseReport> {
    let service = match build_service_schema(ServiceInputs::from(input)) {
        Ok(service) => service,
        Err(failure) => return failure.into_outcome(),
    };
    if let Err(limit) = preflight_source(SourceKind::Policy, input.policy) {
        return FrontendOutcome::OperationalLimit(limit);
    }
    if let Err(limit) = preflight_source(
        SourceKind::Macros,
        input.macros.unwrap_or(dogwood_language::DEFAULT_MACROS),
    ) {
        return FrontendOutcome::OperationalLimit(limit);
    }
    let parsed = match ParsedPolicySet::parse(input.policy, &service) {
        Ok(parsed) => parsed,
        Err(error) => {
            let source_kind = policy_error_source_kind(&error, input.policy, input.macros);
            return FrontendOutcome::Fatal(fatal_from_diagnostic(&error, source_kind));
        }
    };

    let policies = parsed
        .policies()
        .map(|policy| PolicySummary {
            temporal_count: policy.temporal_count(),
            uses_temporal: policy.uses_temporal(),
            provider_invocations: policy.provider_invocations().collect(),
            undeclared_providers: policy.undeclared_providers().collect(),
        })
        .collect();
    FrontendOutcome::Report(PolicyParseReport {
        policy_count: parsed.policy_count(),
        policies,
    })
}

/// Strictly parse and check one explicitly supplied event schema.
pub fn parse_event_schema(source: &str) -> FrontendOutcome<EventSchemaParseReport> {
    if let Err(limit) = preflight_source(SourceKind::EventSchema, source) {
        return FrontendOutcome::OperationalLimit(limit);
    }

    match ServiceSchema::builder().event_schema_str(source).build() {
        Ok(_) => FrontendOutcome::Report(EventSchemaParseReport { valid: true }),
        Err(error) => {
            FrontendOutcome::Fatal(fatal_from_diagnostic(&error, Some(SourceKind::EventSchema)))
        }
    }
}

enum FrontendFailure {
    Fatal(FatalReport),
    OperationalLimit(OperationalLimitExceeded),
}

impl FrontendFailure {
    fn into_outcome<R>(self) -> FrontendOutcome<R> {
        match self {
            Self::Fatal(fatal) => FrontendOutcome::Fatal(fatal),
            Self::OperationalLimit(limit) => FrontendOutcome::OperationalLimit(limit),
        }
    }
}

fn build_service_schema(inputs: ServiceInputs<'_>) -> Result<ServiceSchema, FrontendFailure> {
    if inputs.event_schema.is_none() && inputs.providers.is_none() && inputs.macros.is_none() {
        return Ok(ServiceSchema::defaults());
    }

    let mut builder = ServiceSchema::builder();
    if let Some(source) = inputs.event_schema {
        builder = builder.event_schema_str(source);
    }
    if let Some(json) = inputs.providers {
        preflight_source(SourceKind::Providers, json).map_err(FrontendFailure::OperationalLimit)?;
        let providers = ProviderDeclarations::from_json(json).map_err(|message| {
            FrontendFailure::Fatal(fatal_from_message(message, SourceKind::Providers))
        })?;
        builder = builder.providers(providers);
    }
    preflight_source(
        SourceKind::EventSchema,
        inputs
            .event_schema
            .unwrap_or(dogwood_language::DEFAULT_EVENT_SCHEMA),
    )
    .map_err(FrontendFailure::OperationalLimit)?;
    if let Some(source) = inputs.macros {
        builder = builder.macros_str(source);
    }
    builder.build().map_err(|error| {
        FrontendFailure::Fatal(fatal_from_diagnostic(&error, Some(SourceKind::EventSchema)))
    })
}

fn project(diagnostic: &dyn MietteDiagnostic, source_kind: Option<SourceKind>) -> Finding {
    let labels: Vec<DiagnosticLabel> = diagnostic
        .labels()
        .map(|labels| {
            labels
                .map(|label| DiagnosticLabel {
                    start: label.offset(),
                    len: label.len(),
                    message: label.label().map(str::to_owned),
                })
                .collect()
        })
        .unwrap_or_default();
    let spanned = !labels.is_empty();

    Finding {
        severity: diagnostic.severity().into(),
        code: diagnostic.code().map(|code| code.to_string()),
        message: diagnostic.to_string(),
        labels,
        help: diagnostic.help().map(|help| help.to_string()),
        spanned,
        source_kind,
    }
}

fn fatal_from_diagnostic(
    diagnostic: &dyn MietteDiagnostic,
    source_kind: Option<SourceKind>,
) -> FatalReport {
    let related = diagnostic
        .related()
        .map(|related| {
            related
                .map(|diagnostic| project(diagnostic, source_kind))
                .collect()
        })
        .unwrap_or_default();
    FatalReport {
        diagnostic: Box::new(project(diagnostic, source_kind)),
        related,
    }
}

fn fatal_from_message(message: impl Into<String>, source_kind: SourceKind) -> FatalReport {
    FatalReport {
        diagnostic: Box::new(Finding {
            severity: Severity::Error,
            code: None,
            message: message.into(),
            labels: Vec::new(),
            help: None,
            spanned: false,
            source_kind: Some(source_kind),
        }),
        related: Vec::new(),
    }
}

fn policy_error_source_kind(
    error: &DogwoodError,
    policy: &str,
    macros: Option<&str>,
) -> Option<SourceKind> {
    match error {
        DogwoodError::Parse(errors) => errors
            .iter()
            .next()
            .and_then(|error| source_kind_for_text(error.location().source(), policy, macros)),
        DogwoodError::Macro(error) => {
            source_kind_for_text(error.location().source(), policy, macros)
        }
        _ => None,
    }
}

fn lower_error_source_kind(
    error: &DogwoodError,
    policy: &str,
    macros: Option<&str>,
) -> Option<SourceKind> {
    match error {
        DogwoodError::Parse(_) | DogwoodError::Macro(_) => {
            policy_error_source_kind(error, policy, macros)
        }
        DogwoodError::Cedarify(error) => error
            .location()
            .and_then(|location| source_kind_for_text(location.source(), policy, macros)),
        DogwoodError::PolicySet(_) => Some(SourceKind::Policy),
        DogwoodError::CedarSchema(_) => Some(SourceKind::ActionSchema),
        // Event-schema derivation combines event and action schema inputs, so
        // attributing its current spanless error to either one would be a guess.
        DogwoodError::EventSchema(_) => None,
        _ => None,
    }
}

fn source_kind_for_text(
    diagnostic_source: &str,
    policy: &str,
    macros: Option<&str>,
) -> Option<SourceKind> {
    let policy_matches = diagnostic_source == policy;
    let macros_matches = macros.is_some_and(|source| source == diagnostic_source);
    match (policy_matches, macros_matches) {
        (true, false) => Some(SourceKind::Policy),
        (false, true) => Some(SourceKind::Macros),
        _ => None,
    }
}

#[derive(Clone, Copy)]
struct StructuralFrame {
    open: u8,
    expression_tokens: usize,
    recursive_chain_base: usize,
    recursive_chain_nodes: usize,
    max_recursive_chain_nodes: usize,
    operand_complete: bool,
    awaiting_member_atom: bool,
    member_atom: bool,
}

fn preflight_source(source_kind: SourceKind, source: &str) -> Result<(), OperationalLimitExceeded> {
    if source.len() > MAX_FRONTEND_SOURCE_BYTES {
        return Err(OperationalLimitExceeded {
            source_kind,
            kind: OperationalLimitKind::SourceBytes,
            limit: MAX_FRONTEND_SOURCE_BYTES,
            observed: source.len(),
        });
    }

    let bytes = source.as_bytes();
    let mut frames = Vec::with_capacity(MAX_FRONTEND_NESTING);
    let mut cursor = 0;
    let mut in_string = false;
    let mut in_line_comment = false;
    let check_expression_chain = matches!(source_kind, SourceKind::Policy | SourceKind::Macros);

    while cursor < bytes.len() {
        let byte = bytes[cursor];
        if in_line_comment {
            if matches!(byte, b'\r' | b'\n') {
                in_line_comment = false;
            }
            cursor += 1;
            continue;
        }
        if in_string {
            match byte {
                b'\\' => cursor = (cursor + 2).min(bytes.len()),
                b'"' => {
                    in_string = false;
                    cursor += 1;
                }
                _ => cursor += 1,
            }
            continue;
        }

        if byte == b'/' && bytes.get(cursor + 1) == Some(&b'/') {
            in_line_comment = true;
            cursor += 2;
            continue;
        }
        if byte == b'"' {
            if check_expression_chain {
                bump_expression_chain(source_kind, &mut frames)?;
                note_operand_atom(&mut frames);
            }
            in_string = true;
            cursor += 1;
            continue;
        }

        if is_ident_start(byte) {
            cursor += 1;
            while bytes.get(cursor).is_some_and(|byte| is_ident_cont(*byte)) {
                cursor += 1;
            }
            if check_expression_chain {
                bump_expression_chain(source_kind, &mut frames)?;
                note_operand_atom(&mut frames);
            }
            continue;
        }
        if byte.is_ascii_digit() {
            cursor += 1;
            while bytes.get(cursor).is_some_and(u8::is_ascii_digit) {
                cursor += 1;
            }
            if check_expression_chain {
                bump_expression_chain(source_kind, &mut frames)?;
                note_operand_atom(&mut frames);
            }
            continue;
        }

        match byte {
            b'(' | b'[' | b'{' => {
                if check_expression_chain {
                    bump_expression_chain(source_kind, &mut frames)?;
                    note_open_group(source_kind, &mut frames, byte)?;
                }
                let recursive_chain_base =
                    frames.last().map_or(0, |frame| frame.recursive_chain_nodes);
                frames.push(StructuralFrame {
                    open: byte,
                    expression_tokens: 0,
                    recursive_chain_base,
                    recursive_chain_nodes: recursive_chain_base,
                    max_recursive_chain_nodes: recursive_chain_base,
                    operand_complete: false,
                    awaiting_member_atom: false,
                    member_atom: false,
                });
                if frames.len() > MAX_FRONTEND_NESTING {
                    return Err(OperationalLimitExceeded {
                        source_kind,
                        kind: OperationalLimitKind::StructuralNesting,
                        limit: MAX_FRONTEND_NESTING,
                        observed: frames.len(),
                    });
                }
            }
            b')' | b']' | b'}'
                if frames
                    .last()
                    .is_some_and(|frame| matches_pair(frame.open, byte)) =>
            {
                let closed = frames.pop().expect("matched frame exists");
                if let Some(parent) = frames.last_mut() {
                    parent.recursive_chain_nodes = closed.max_recursive_chain_nodes;
                    parent.max_recursive_chain_nodes = parent
                        .max_recursive_chain_nodes
                        .max(closed.max_recursive_chain_nodes);
                }
            }
            b',' if check_expression_chain => {
                if let Some(frame) = frames.last_mut() {
                    frame.expression_tokens = 0;
                    frame.recursive_chain_nodes = frame.recursive_chain_base;
                    frame.operand_complete = false;
                    frame.awaiting_member_atom = false;
                    frame.member_atom = false;
                }
            }
            byte if !byte.is_ascii_whitespace() && check_expression_chain => {
                bump_expression_chain(source_kind, &mut frames)?;
                note_punctuation(source_kind, &mut frames, byte)?;
            }
            _ => {}
        }
        cursor += 1;
    }

    Ok(())
}

fn note_operand_atom(frames: &mut [StructuralFrame]) {
    if let Some(frame) = frames.last_mut() {
        if frame.awaiting_member_atom {
            frame.awaiting_member_atom = false;
            frame.operand_complete = true;
            frame.member_atom = true;
        } else {
            if frame.operand_complete {
                frame.recursive_chain_nodes = frame.recursive_chain_base;
            }
            frame.operand_complete = true;
            frame.member_atom = false;
        }
    }
}

fn note_open_group(
    source_kind: SourceKind,
    frames: &mut [StructuralFrame],
    open: u8,
) -> Result<(), OperationalLimitExceeded> {
    let Some(frame) = frames.last_mut() else {
        return Ok(());
    };

    if frame.operand_complete && matches!(open, b'(' | b'[') {
        // `.method(args)` is one member node: the dot already counted it.
        if open == b'[' || !frame.member_atom {
            advance_recursive_chain(source_kind, frame)?;
        }
    }
    frame.operand_complete = true;
    frame.awaiting_member_atom = false;
    frame.member_atom = false;
    Ok(())
}

fn note_punctuation(
    source_kind: SourceKind,
    frames: &mut [StructuralFrame],
    punctuation: u8,
) -> Result<(), OperationalLimitExceeded> {
    let Some(frame) = frames.last_mut() else {
        return Ok(());
    };

    if punctuation == b'.' && frame.operand_complete {
        advance_recursive_chain(source_kind, frame)?;
        frame.operand_complete = false;
        frame.awaiting_member_atom = true;
        frame.member_atom = false;
    } else if matches!(punctuation, b'!' | b'-') && !frame.operand_complete {
        advance_recursive_chain(source_kind, frame)?;
        frame.awaiting_member_atom = false;
        frame.member_atom = false;
    } else {
        if frame.operand_complete {
            frame.recursive_chain_nodes = frame.recursive_chain_base;
        }
        frame.operand_complete = false;
        frame.awaiting_member_atom = false;
        frame.member_atom = false;
    }
    Ok(())
}

fn advance_recursive_chain(
    source_kind: SourceKind,
    frame: &mut StructuralFrame,
) -> Result<(), OperationalLimitExceeded> {
    frame.recursive_chain_nodes += 1;
    frame.max_recursive_chain_nodes = frame
        .max_recursive_chain_nodes
        .max(frame.recursive_chain_nodes);
    check_linear_run(source_kind, frame.recursive_chain_nodes)
}

fn check_linear_run(
    source_kind: SourceKind,
    observed: usize,
) -> Result<(), OperationalLimitExceeded> {
    if observed > MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN {
        return Err(OperationalLimitExceeded {
            source_kind,
            kind: OperationalLimitKind::ExpressionChain,
            limit: MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN,
            observed,
        });
    }
    Ok(())
}

fn bump_expression_chain(
    source_kind: SourceKind,
    frames: &mut [StructuralFrame],
) -> Result<(), OperationalLimitExceeded> {
    let Some(frame) = frames.last_mut() else {
        return Ok(());
    };
    frame.expression_tokens += 1;
    if frame.expression_tokens > MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS {
        return Err(OperationalLimitExceeded {
            source_kind,
            kind: OperationalLimitKind::ExpressionChain,
            limit: MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS,
            observed: frame.expression_tokens,
        });
    }
    Ok(())
}

fn is_ident_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_'
}

fn is_ident_cont(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn matches_pair(open: u8, close: u8) -> bool {
    matches!((open, close), (b'(', b')') | (b'[', b']') | (b'{', b'}'))
}

#[cfg(test)]
mod tests {
    use std::error::Error;
    use std::fmt;

    use miette::{Diagnostic, LabeledSpan};

    use super::*;

    const ACTION_SCHEMA: &str = r#"
namespace App {
  type ReadInput = { value: String };
  type SystemContext = { now: datetime };

  entity User;
  entity Admin;
  entity Resource;

  action "Read" appliesTo {
    principal: [User],
    resource: [Resource],
    context: { input: ReadInput, system: SystemContext }
  };
}
"#;

    const VALID_POLICY: &str = r#"permit (principal, action == App::Action::"Read", resource);"#;

    const EVENT_SCHEMA: &str = r#"
decision event <A>::attempt {
    ...inputs(A),
    actor: principalType(A),
}
"#;

    fn default_bundle(policy: &str) -> BundleInput<'_> {
        BundleInput {
            policy,
            action_schema: ACTION_SCHEMA,
            event_schema: None,
            providers: None,
            macros: None,
        }
    }

    fn policy_with_body(body: &str) -> String {
        format!("permit (principal, action, resource) when {{ {body} }};")
    }

    fn cedar_macro_with_body(name: &str, body: &str) -> String {
        format!("def cedar {name}() {{ {body} }};")
    }

    /// Nine `||`-separated groups of 19 `true`s joined by `&&`, after
    /// `leading_bangs` `!`s: `511 + leading_bangs` generic tokens, yet under 30
    /// levels deep, so Dogwood accepts it.
    fn wide_boolean(leading_bangs: usize) -> String {
        let group = vec!["true"; 19].join(" && ");
        format!(
            "{}{}",
            "!".repeat(leading_bangs),
            vec![group; 9].join(" || ")
        )
    }

    #[test]
    fn valid_default_bundle_reports_clean_validation() {
        let outcome = validate_bundle(&default_bundle(VALID_POLICY));
        assert_eq!(
            outcome,
            FrontendOutcome::Report(ValidationReport {
                passed: true,
                passed_without_warnings: true,
                errors: Vec::new(),
                warnings: Vec::new(),
            })
        );
    }

    #[test]
    fn valid_bundle_accepts_every_optional_input() {
        let macros = "def cedar always() { true };";
        let policy = r#"permit (principal, action == App::Action::"Read", resource)
when { always() };"#;
        let input = BundleInput {
            policy,
            action_schema: ACTION_SCHEMA,
            event_schema: Some(EVENT_SCHEMA),
            providers: Some(r#"{"availableProviders":{}}"#),
            macros: Some(macros),
        };

        let FrontendOutcome::Report(report) = validate_bundle(&input) else {
            panic!("optional-input bundle should validate");
        };
        assert!(report.passed_without_warnings);
    }

    #[test]
    fn wide_shallow_policy_matches_workspace_frontend_acceptance() {
        let clauses = r#"when { context.input.value == "x" } "#.repeat(16);
        let policy =
            format!(r#"permit (principal, action == App::Action::"Read", resource) {clauses};"#);

        let service = ServiceSchema::defaults();
        let policy_schema =
            PolicySchema::from_cedarschema_str(ACTION_SCHEMA).expect("action schema should load");
        let parsed =
            ParsedPolicySet::parse(&policy, &service).expect("Dogwood frontend should parse");
        let lowered = parsed
            .lower(&policy_schema)
            .expect("Dogwood frontend should lower");
        assert!(
            Validator::new().validate(&lowered).validation_passed(),
            "Dogwood frontend should validate"
        );

        let FrontendOutcome::Report(report) = validate_bundle(&default_bundle(&policy)) else {
            panic!("adapter should accept the Dogwood frontend's valid wide, shallow policy");
        };
        assert!(report.passed_without_warnings);
    }

    #[test]
    fn wide_shallow_collection_elements_have_independent_chain_budgets() {
        let elements = std::iter::repeat_n("context.input.value", 40)
            .collect::<Vec<_>>()
            .join(", ");
        let policy = policy_with_body(&format!(r#"[{elements}].contains("x")"#));

        let service = ServiceSchema::defaults();
        ParsedPolicySet::parse(&policy, &service)
            .expect("Dogwood frontend should accept the wide set expression");

        let FrontendOutcome::Report(report) = validate_bundle(&default_bundle(&policy)) else {
            panic!("adapter should accept independent set elements");
        };
        assert!(report.passed_without_warnings);
    }

    #[test]
    fn validation_errors_remain_non_fatal_owned_findings() {
        let policy = r#"permit (principal, action == App::Action::"Read", resource)
when { context.input.missing == "x" };"#;
        let FrontendOutcome::Report(report) = validate_bundle(&default_bundle(policy)) else {
            panic!("schema-aware errors belong in the report channel");
        };

        assert!(!report.passed);
        assert!(!report.errors.is_empty());
        assert!(
            report
                .errors
                .iter()
                .all(|finding| finding.severity == Severity::Error)
        );
        assert!(
            report
                .errors
                .iter()
                .all(|finding| finding.source_kind == Some(SourceKind::Policy))
        );
    }

    #[test]
    fn validation_warnings_preserve_the_warning_channel() {
        // A string mixing Latin and Cyrillic letters: a warning of Cedar's
        // validator. (An impossible policy is an error of Dogwood's.)
        let policy = r#"permit (principal, action == App::Action::"Read", resource)
when { context.input.value == "pаssword" };"#;
        let FrontendOutcome::Report(report) = validate_bundle(&default_bundle(policy)) else {
            panic!("warning policy should reach validation");
        };

        assert!(report.passed);
        assert!(!report.passed_without_warnings);
        assert!(!report.warnings.is_empty());
        assert!(
            report
                .warnings
                .iter()
                .all(|finding| finding.severity == Severity::Warning)
        );
    }

    #[test]
    fn fatal_policy_parse_preserves_labels_and_source_kind() {
        let input = PolicyParseInput {
            policy: "permitt (principal, action, resource);",
            event_schema: None,
            providers: None,
            macros: None,
        };
        let FrontendOutcome::Fatal(fatal) = parse_policy(&input) else {
            panic!("invalid policy should be fatal");
        };

        assert_eq!(fatal.diagnostic.severity, Severity::Error);
        assert_eq!(fatal.diagnostic.source_kind, Some(SourceKind::Policy));
        assert!(fatal.diagnostic.spanned);
        assert!(!fatal.diagnostic.labels.is_empty());
    }

    #[test]
    fn macro_library_and_invocation_failures_keep_their_distinct_sources() {
        let malformed_library = PolicyParseInput {
            policy: VALID_POLICY,
            event_schema: None,
            providers: None,
            macros: Some("def cedar broken() { };"),
        };
        let FrontendOutcome::Fatal(library_fatal) = parse_policy(&malformed_library) else {
            panic!("malformed macro library should be fatal");
        };
        assert_eq!(
            library_fatal.diagnostic.source_kind,
            Some(SourceKind::Macros)
        );

        let invocation_failure = PolicyParseInput {
            policy: "permit (principal, action, resource) when { identity() };",
            event_schema: None,
            providers: None,
            macros: Some("def cedar identity(?value) { ?value };"),
        };
        let FrontendOutcome::Fatal(invocation_fatal) = parse_policy(&invocation_failure) else {
            panic!("bad policy-authored macro invocation should be fatal");
        };
        assert_eq!(
            invocation_fatal.diagnostic.source_kind,
            Some(SourceKind::Policy)
        );
    }

    #[test]
    fn malformed_providers_are_spanless_and_attributed() {
        let input = PolicyParseInput {
            policy: VALID_POLICY,
            event_schema: None,
            providers: Some("{"),
            macros: None,
        };
        let FrontendOutcome::Fatal(fatal) = parse_policy(&input) else {
            panic!("malformed providers should be fatal");
        };

        assert_eq!(fatal.diagnostic.source_kind, Some(SourceKind::Providers));
        assert!(!fatal.diagnostic.spanned);
        assert!(fatal.diagnostic.labels.is_empty());
    }

    #[test]
    fn provider_failure_precedes_later_event_schema_operational_limit() {
        let nested_event_schema = "(".repeat(MAX_FRONTEND_NESTING + 1);
        let input = PolicyParseInput {
            policy: VALID_POLICY,
            event_schema: Some(&nested_event_schema),
            providers: Some("{"),
            macros: None,
        };
        let FrontendOutcome::Fatal(fatal) = parse_policy(&input) else {
            panic!("provider JSON is parsed before the event schema");
        };

        assert_eq!(fatal.diagnostic.source_kind, Some(SourceKind::Providers));
    }

    #[test]
    fn event_schema_failure_precedes_later_macro_operational_limit() {
        let nested_macros = "(".repeat(MAX_FRONTEND_NESTING + 1);
        let input = PolicyParseInput {
            policy: VALID_POLICY,
            event_schema: Some(""),
            providers: None,
            macros: Some(&nested_macros),
        };
        let FrontendOutcome::Fatal(fatal) = parse_policy(&input) else {
            panic!("the service-schema builder runs before policy and macro parsing");
        };

        assert_eq!(fatal.diagnostic.source_kind, Some(SourceKind::EventSchema));
    }

    #[test]
    fn policy_and_action_preflights_precede_later_macro_preflight() {
        let nested = "(".repeat(MAX_FRONTEND_NESTING + 1);
        let policy_input = PolicyParseInput {
            policy: &nested,
            event_schema: None,
            providers: None,
            macros: Some(&nested),
        };
        let FrontendOutcome::OperationalLimit(policy_limit) = parse_policy(&policy_input) else {
            panic!("policy preflight should precede macro preflight");
        };
        assert_eq!(policy_limit.source_kind, SourceKind::Policy);

        let bundle = BundleInput {
            policy: VALID_POLICY,
            action_schema: &nested,
            event_schema: None,
            providers: None,
            macros: Some(&nested),
        };
        let FrontendOutcome::OperationalLimit(action_limit) = validate_bundle(&bundle) else {
            panic!("action-schema preflight should precede macro preflight");
        };
        assert_eq!(action_limit.source_kind, SourceKind::ActionSchema);
    }

    #[test]
    fn standalone_policy_parse_returns_owned_summary() {
        let input = PolicyParseInput {
            policy: VALID_POLICY,
            event_schema: None,
            providers: None,
            macros: None,
        };
        let FrontendOutcome::Report(report) = parse_policy(&input) else {
            panic!("valid policy should parse");
        };

        assert_eq!(report.policy_count, 1);
        assert_eq!(report.policies.len(), 1);
        assert!(!report.policies[0].uses_temporal);
    }

    #[test]
    fn standalone_event_schema_handles_valid_and_spanless_fatal_forms() {
        assert_eq!(
            parse_event_schema(EVENT_SCHEMA),
            FrontendOutcome::Report(EventSchemaParseReport { valid: true })
        );

        let FrontendOutcome::Fatal(fatal) = parse_event_schema("") else {
            panic!("an explicit empty event schema should be fatal");
        };
        assert_eq!(fatal.diagnostic.source_kind, Some(SourceKind::EventSchema));
        assert!(!fatal.diagnostic.spanned);
        assert!(fatal.diagnostic.labels.is_empty());
    }

    #[test]
    fn exact_source_size_limit_is_accepted_and_next_byte_is_operational() {
        let accepted = " ".repeat(MAX_FRONTEND_SOURCE_BYTES);
        let input = PolicyParseInput {
            policy: &accepted,
            event_schema: None,
            providers: None,
            macros: None,
        };
        assert!(matches!(parse_policy(&input), FrontendOutcome::Report(_)));

        let rejected = " ".repeat(MAX_FRONTEND_SOURCE_BYTES + 1);
        let input = PolicyParseInput {
            policy: &rejected,
            event_schema: None,
            providers: None,
            macros: None,
        };
        assert_eq!(
            parse_policy(&input),
            FrontendOutcome::OperationalLimit(OperationalLimitExceeded {
                source_kind: SourceKind::Policy,
                kind: OperationalLimitKind::SourceBytes,
                limit: MAX_FRONTEND_SOURCE_BYTES,
                observed: MAX_FRONTEND_SOURCE_BYTES + 1,
            })
        );
    }

    #[test]
    fn exact_nesting_limit_is_accepted_and_next_level_is_operational() {
        let accepted_depth = MAX_FRONTEND_NESTING - 1;
        let accepted = format!(
            "permit (principal, action, resource) when {{ {}true{} }};",
            "(".repeat(accepted_depth),
            ")".repeat(accepted_depth)
        );
        let input = PolicyParseInput {
            policy: &accepted,
            event_schema: None,
            providers: None,
            macros: None,
        };
        assert!(matches!(parse_policy(&input), FrontendOutcome::Report(_)));

        let rejected_depth = MAX_FRONTEND_NESTING;
        let rejected = format!(
            "permit (principal, action, resource) when {{ {}true{} }};",
            "(".repeat(rejected_depth),
            ")".repeat(rejected_depth)
        );
        let input = PolicyParseInput {
            policy: &rejected,
            event_schema: None,
            providers: None,
            macros: None,
        };
        assert_eq!(
            parse_policy(&input),
            FrontendOutcome::OperationalLimit(OperationalLimitExceeded {
                source_kind: SourceKind::Policy,
                kind: OperationalLimitKind::StructuralNesting,
                limit: MAX_FRONTEND_NESTING,
                observed: MAX_FRONTEND_NESTING + 1,
            })
        );
    }

    #[test]
    fn recursive_chain_limit_accepts_exact_boundary_and_preflights_next_node() {
        let accepted_mixed = format!(
            "{}context{}{}{}",
            "!".repeat(8),
            " . field".repeat(8),
            r#" [ "field" ]"#.repeat(8),
            " . method ( )".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN - 24),
        );
        let accepted_bodies = [
            format!("{}true", "!".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN)),
            format!(
                "context{}",
                " . field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN)
            ),
            format!(
                "context{}",
                " . method ( )".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN)
            ),
            format!(
                "context{}",
                r#" [ "field" ]"#.repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN)
            ),
            accepted_mixed.clone(),
        ];

        for body in &accepted_bodies {
            let policy = policy_with_body(body);
            let input = PolicyParseInput {
                policy: &policy,
                event_schema: None,
                providers: None,
                macros: None,
            };
            assert!(
                matches!(parse_policy(&input), FrontendOutcome::Report(_)),
                "adapter should accept an exact-boundary chain: {body}"
            );
        }

        let rejected_bodies = [
            format!(
                "{}true",
                "!".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1)
            ),
            format!(
                "context{}",
                " . field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1)
            ),
            format!(
                "context{}",
                " . method ( )".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1)
            ),
            format!(
                "context{}",
                r#" [ "field" ]"#.repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1)
            ),
            format!("{accepted_mixed} . field"),
        ];

        for body in &rejected_bodies {
            let policy = policy_with_body(body);
            ParsedPolicySet::parse(&policy, &ServiceSchema::defaults())
                .expect_err("the operational boundary is Dogwood's depth limit");
            let input = PolicyParseInput {
                policy: &policy,
                event_schema: None,
                providers: None,
                macros: None,
            };
            assert_eq!(
                parse_policy(&input),
                FrontendOutcome::OperationalLimit(OperationalLimitExceeded {
                    source_kind: SourceKind::Policy,
                    kind: OperationalLimitKind::ExpressionChain,
                    limit: MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN,
                    observed: MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1,
                }),
                "adapter should preflight the first over-limit node: {body}"
            );
        }
    }

    #[test]
    fn recursive_chain_budget_tracks_one_nested_path_not_sibling_elements() {
        let accepted_bodies = [
            format!(
                "{}(context{})",
                "!".repeat(16),
                ".field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN - 16)
            ),
            format!(
                "({}context){}",
                "!".repeat(16),
                ".field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN - 16)
            ),
            format!(
                "(({}context){}){}",
                "!".repeat(8),
                ".field".repeat(8),
                ".field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN - 16)
            ),
        ];
        for body in &accepted_bodies {
            let policy = policy_with_body(body);
            let input = PolicyParseInput {
                policy: &policy,
                event_schema: None,
                providers: None,
                macros: None,
            };
            assert!(
                matches!(parse_policy(&input), FrontendOutcome::Report(_)),
                "adapter should accept exactly the limit across nested segments: {body}"
            );
        }

        let sibling = format!(
            "context{}, context{}",
            ".field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN),
            ".field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN)
        );
        // The set literal is one more tree level, so Dogwood refuses these
        // elements; the preflight budget is still per element.
        let siblings = policy_with_body(&format!("[{sibling}]"));
        assert!(
            preflight_source(SourceKind::Policy, &siblings).is_ok(),
            "comma-separated expressions should retain independent chain budgets"
        );

        let rejected_bodies = [
            format!(
                "{}(context{})",
                "!".repeat(16),
                ".field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN - 15)
            ),
            format!(
                "({}context){}",
                "!".repeat(16),
                ".field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN - 15)
            ),
            format!(
                "(({}context){}){}",
                "!".repeat(8),
                ".field".repeat(8),
                ".field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN - 15)
            ),
        ];
        for body in &rejected_bodies {
            let policy = policy_with_body(body);
            ParsedPolicySet::parse(&policy, &ServiceSchema::defaults())
                .expect_err("Dogwood refuses the first over-limit nested node too");
            let input = PolicyParseInput {
                policy: &policy,
                event_schema: None,
                providers: None,
                macros: None,
            };
            assert_eq!(
                parse_policy(&input),
                FrontendOutcome::OperationalLimit(OperationalLimitExceeded {
                    source_kind: SourceKind::Policy,
                    kind: OperationalLimitKind::ExpressionChain,
                    limit: MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN,
                    observed: MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1,
                }),
                "adapter should preflight the first over-limit nested node: {body}"
            );
        }
    }

    #[test]
    fn exact_expression_segment_token_limit_is_accepted_and_next_token_is_operational() {
        let accepted = policy_with_body(&wide_boolean(1));
        assert!(preflight_source(SourceKind::Policy, &accepted).is_ok());
        let input = PolicyParseInput {
            policy: &accepted,
            event_schema: None,
            providers: None,
            macros: None,
        };
        assert!(matches!(parse_policy(&input), FrontendOutcome::Report(_)));

        let rejected = policy_with_body(&wide_boolean(2));
        ParsedPolicySet::parse(&rejected, &ServiceSchema::defaults())
            .expect("the local operational boundary is not a Dogwood validity rule");
        assert_eq!(
            preflight_source(SourceKind::Policy, &rejected),
            Err(OperationalLimitExceeded {
                source_kind: SourceKind::Policy,
                kind: OperationalLimitKind::ExpressionChain,
                limit: MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS,
                observed: MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS + 1,
            })
        );
    }

    #[test]
    fn property_chain_at_dogwoods_depth_limit_is_accepted() {
        // Each `context.input.value == "x"` is four levels deep, and the
        // first sits under one `&&` per later term, so 29 reach `DEFAULT_MAX_DEPTH`.
        let chain = |terms| {
            policy_with_body(
                &std::iter::repeat_n(r#"context.input.value == "x""#, terms)
                    .collect::<Vec<_>>()
                    .join(" && "),
            )
        };
        let policy = chain(DEFAULT_MAX_DEPTH - 3);
        assert!(preflight_source(SourceKind::Policy, &policy).is_ok());
        let FrontendOutcome::Report(report) = validate_bundle(&default_bundle(&policy)) else {
            panic!("a property chain at Dogwood's depth limit should validate");
        };
        assert!(report.passed_without_warnings);

        let policy = chain(DEFAULT_MAX_DEPTH - 2);
        assert!(preflight_source(SourceKind::Policy, &policy).is_ok());
        assert!(matches!(
            validate_bundle(&default_bundle(&policy)),
            FrontendOutcome::Fatal(_)
        ));
    }

    #[test]
    fn generic_expression_chain_limit_covers_shallow_recursive_forms() {
        let nested_if = policy_with_body(&format!("{}true", "if true then true else ".repeat(103)));
        let unary = policy_with_body(&format!("{}true", "!".repeat(513)));
        let member = policy_with_body(&format!("context{}", ".field".repeat(256)));
        let postfix = policy_with_body(&format!("context{}", ".method()".repeat(171)));
        let index = policy_with_body(&format!("context{}", "[0]".repeat(512)));
        let binary = policy_with_body(&wide_boolean(2));
        let division = policy_with_body(&format!("1{}", " / 1".repeat(256)));
        let temporal = format!(
            "permit (principal, action, resource) when temporal {{ {}tp(x) }};",
            "exists (x: Long). ".repeat(171)
        );

        for (shape, source, expected_limit) in [
            ("nested if", nested_if, MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS),
            ("unary chain", unary, MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN),
            ("member chain", member, MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN),
            (
                "postfix chain",
                postfix,
                MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN,
            ),
            ("index chain", index, MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN),
            ("binary chain", binary, MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS),
            (
                "division chain",
                division,
                MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS,
            ),
            (
                "temporal operator chain",
                temporal,
                MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN,
            ),
        ] {
            let Err(limit_error) = preflight_source(SourceKind::Policy, &source) else {
                panic!("{shape} should exceed the expression-chain budget");
            };
            assert_eq!(
                limit_error.kind,
                OperationalLimitKind::ExpressionChain,
                "wrong limit for {shape}"
            );
            assert_eq!(limit_error.limit, expected_limit);
            assert_eq!(limit_error.observed, expected_limit + 1);
        }
    }

    #[test]
    fn expression_chain_budget_is_independent_per_policy_and_macro_body() {
        let body = wide_boolean(1);
        let unit = policy_with_body(&body);
        let source = format!("{unit}\n{unit}");
        assert!(preflight_source(SourceKind::Policy, &source).is_ok());
        let policy_input = PolicyParseInput {
            policy: &source,
            event_schema: None,
            providers: None,
            macros: None,
        };
        let FrontendOutcome::Report(report) = parse_policy(&policy_input) else {
            panic!("independent policies should retain independent chain budgets");
        };
        assert_eq!(report.policy_count, 2);

        let first_macro = cedar_macro_with_body("first", &body);
        let second_macro = cedar_macro_with_body("second", &body);
        let macros = format!("{first_macro}\n{second_macro}");
        assert!(preflight_source(SourceKind::Macros, &macros).is_ok());
        let macro_input = PolicyParseInput {
            policy: VALID_POLICY,
            event_schema: None,
            providers: None,
            macros: Some(&macros),
        };
        assert!(matches!(
            parse_policy(&macro_input),
            FrontendOutcome::Report(_)
        ));

        let oversized_macro = cedar_macro_with_body("oversized", &wide_boolean(2));
        let Err(limit) = preflight_source(SourceKind::Macros, &oversized_macro) else {
            panic!("oversized macro should exceed its expression-chain budget");
        };
        assert_eq!(limit.source_kind, SourceKind::Macros);
        assert_eq!(limit.kind, OperationalLimitKind::ExpressionChain);
    }

    #[test]
    fn malformed_delimiters_cannot_reset_the_expression_chain_budget() {
        let source = policy_with_body(&format!("{}]", wide_boolean(1)));

        assert_eq!(
            preflight_source(SourceKind::Policy, &source),
            Err(OperationalLimitExceeded {
                source_kind: SourceKind::Policy,
                kind: OperationalLimitKind::ExpressionChain,
                limit: MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS,
                observed: MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS + 1,
            })
        );
    }

    #[test]
    fn expression_chain_scan_ignores_strings_comments_and_escaped_quotes() {
        let ignored = "if ! . && || / % ([{ formerly previous since exists "
            .repeat(MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS + 1);
        let source = format!(
            r#"permit (principal, action, resource) when {{
                "escaped \" {ignored}" == "escaped \" {ignored}"
            }};
            // {ignored}
"#
        );

        assert!(preflight_source(SourceKind::Policy, &source).is_ok());
        let input = PolicyParseInput {
            policy: &source,
            event_schema: None,
            providers: None,
            macros: None,
        };
        assert!(matches!(parse_policy(&input), FrontendOutcome::Report(_)));
    }

    #[test]
    fn nesting_scan_ignores_strings_comments_and_escaped_quotes() {
        let ignored = "(".repeat(MAX_FRONTEND_NESTING + 1);
        let source = format!(
            "permit (principal, action, resource) when {{ \
             \"escaped \\\" {ignored}\" == \"escaped \\\" {ignored}\" }}; \
             // {ignored}\n"
        );
        let input = PolicyParseInput {
            policy: &source,
            event_schema: None,
            providers: None,
            macros: None,
        };

        assert!(matches!(parse_policy(&input), FrontendOutcome::Report(_)));
    }

    #[test]
    fn operational_limits_cover_optional_recursive_inputs() {
        let nested = "(".repeat(MAX_FRONTEND_NESTING + 1);
        for (source_kind, input) in [
            (
                SourceKind::EventSchema,
                PolicyParseInput {
                    policy: VALID_POLICY,
                    event_schema: Some(&nested),
                    providers: None,
                    macros: None,
                },
            ),
            (
                SourceKind::Providers,
                PolicyParseInput {
                    policy: VALID_POLICY,
                    event_schema: None,
                    providers: Some(&nested),
                    macros: None,
                },
            ),
            (
                SourceKind::Macros,
                PolicyParseInput {
                    policy: VALID_POLICY,
                    event_schema: None,
                    providers: None,
                    macros: Some(&nested),
                },
            ),
        ] {
            let FrontendOutcome::OperationalLimit(limit) = parse_policy(&input) else {
                panic!("{source_kind:?} should be checked before parsing");
            };
            assert_eq!(limit.source_kind, source_kind);
            assert_eq!(limit.kind, OperationalLimitKind::StructuralNesting);
        }

        let action_schema = "{".repeat(MAX_FRONTEND_NESTING + 1);
        let input = BundleInput {
            policy: VALID_POLICY,
            action_schema: &action_schema,
            event_schema: None,
            providers: None,
            macros: None,
        };
        let FrontendOutcome::OperationalLimit(limit) = validate_bundle(&input) else {
            panic!("action schema should be checked before parsing");
        };
        assert_eq!(limit.source_kind, SourceKind::ActionSchema);
    }

    #[derive(Debug)]
    struct TestDiagnostic {
        message: &'static str,
        severity: Option<miette::Severity>,
        code: Option<&'static str>,
        help: Option<&'static str>,
        labels: Vec<LabeledSpan>,
        related: Vec<TestDiagnostic>,
    }

    impl TestDiagnostic {
        fn new(message: &'static str) -> Self {
            Self {
                message,
                severity: None,
                code: None,
                help: None,
                labels: Vec::new(),
                related: Vec::new(),
            }
        }
    }

    impl fmt::Display for TestDiagnostic {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str(self.message)
        }
    }

    impl Error for TestDiagnostic {}

    impl Diagnostic for TestDiagnostic {
        fn code(&self) -> Option<Box<dyn fmt::Display + '_>> {
            self.code
                .map(|code| Box::new(code) as Box<dyn fmt::Display>)
        }

        fn severity(&self) -> Option<miette::Severity> {
            self.severity
        }

        fn help(&self) -> Option<Box<dyn fmt::Display + '_>> {
            self.help
                .map(|help| Box::new(help) as Box<dyn fmt::Display>)
        }

        fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
            if self.labels.is_empty() {
                None
            } else {
                Some(Box::new(self.labels.clone().into_iter()))
            }
        }

        fn related(&self) -> Option<Box<dyn Iterator<Item = &dyn Diagnostic> + '_>> {
            if self.related.is_empty() {
                None
            } else {
                Some(Box::new(
                    self.related
                        .iter()
                        .map(|diagnostic| diagnostic as &dyn Diagnostic),
                ))
            }
        }
    }

    #[test]
    fn projection_is_deterministic_and_preserves_metadata_and_label_order() {
        let diagnostic = TestDiagnostic {
            message: "primary diagnostic",
            severity: Some(miette::Severity::Warning),
            code: Some("dogwood::test::001"),
            help: Some("apply the suggested correction"),
            labels: vec![
                LabeledSpan::new(Some("first emitted".to_string()), 9, 2),
                LabeledSpan::new(None, 1, 0),
            ],
            related: Vec::new(),
        };
        let expected = Finding {
            severity: Severity::Warning,
            code: Some("dogwood::test::001".to_string()),
            message: "primary diagnostic".to_string(),
            labels: vec![
                DiagnosticLabel {
                    start: 9,
                    len: 2,
                    message: Some("first emitted".to_string()),
                },
                DiagnosticLabel {
                    start: 1,
                    len: 0,
                    message: None,
                },
            ],
            help: Some("apply the suggested correction".to_string()),
            spanned: true,
            source_kind: Some(SourceKind::Policy),
        };

        let first = project(&diagnostic, Some(SourceKind::Policy));
        let second = project(&diagnostic, Some(SourceKind::Policy));
        assert_eq!(first, expected);
        assert_eq!(second, expected);
        assert_eq!(
            serde_json::to_string(&first).expect("finding should serialize"),
            r#"{"severity":"warning","code":"dogwood::test::001","message":"primary diagnostic","labels":[{"start":9,"len":2,"message":"first emitted"},{"start":1,"len":0}],"help":"apply the suggested correction","spanned":true,"source_kind":"policy"}"#
        );
    }

    #[test]
    fn fatal_projection_preserves_related_diagnostic_order() {
        let diagnostic = TestDiagnostic {
            message: "primary",
            severity: None,
            code: Some("primary-code"),
            help: None,
            labels: Vec::new(),
            related: vec![
                TestDiagnostic {
                    message: "first related",
                    severity: Some(miette::Severity::Advice),
                    code: Some("related-1"),
                    help: Some("first help"),
                    labels: vec![LabeledSpan::new(Some("first label".to_string()), 4, 3)],
                    related: Vec::new(),
                },
                TestDiagnostic {
                    message: "second related",
                    severity: Some(miette::Severity::Warning),
                    code: Some("related-2"),
                    help: Some("second help"),
                    labels: vec![LabeledSpan::new(Some("second label".to_string()), 1, 2)],
                    related: Vec::new(),
                },
            ],
        };

        let fatal = fatal_from_diagnostic(&diagnostic, Some(SourceKind::Macros));
        assert_eq!(fatal.diagnostic.code.as_deref(), Some("primary-code"));
        assert_eq!(
            fatal
                .related
                .iter()
                .map(|finding| finding.message.as_str())
                .collect::<Vec<_>>(),
            vec!["first related", "second related"]
        );
        assert_eq!(
            fatal
                .related
                .iter()
                .map(|finding| finding.code.as_deref())
                .collect::<Vec<_>>(),
            vec![Some("related-1"), Some("related-2")]
        );
        assert_eq!(
            fatal.related[0].labels,
            vec![DiagnosticLabel {
                start: 4,
                len: 3,
                message: Some("first label".to_string()),
            }]
        );
        assert_eq!(fatal.related[0].help.as_deref(), Some("first help"));
        assert_eq!(fatal.related[1].help.as_deref(), Some("second help"));
        assert!(
            fatal
                .related
                .iter()
                .all(|finding| finding.source_kind == Some(SourceKind::Macros))
        );
    }

    #[test]
    fn projection_preserves_zero_width_and_spanless_diagnostics() {
        let zero_width = TestDiagnostic {
            message: "zero width",
            severity: None,
            code: None,
            help: None,
            labels: vec![LabeledSpan::new(Some("cursor".to_string()), 7, 0)],
            related: Vec::new(),
        };
        let projected = project(&zero_width, Some(SourceKind::Policy));
        assert!(projected.spanned);
        assert_eq!(
            projected.labels,
            vec![DiagnosticLabel {
                start: 7,
                len: 0,
                message: Some("cursor".to_string()),
            }]
        );

        let spanless = project(&TestDiagnostic::new("spanless"), None);
        assert!(!spanless.spanned);
        assert!(spanless.labels.is_empty());
    }
}
