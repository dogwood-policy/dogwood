//! The core schema-aware validator: [`validate_impl`], behind
//! [`Validator::validate`](crate::Validator::validate).
//!
//! Given the already-lowered artifacts (a [`Lowered`]) and their augmented
//! schema, it runs every check and accumulates findings
//! into a [`ValidationResult`]:
//!
//! 1. Cedar's schema-aware validator on the lowered policies. Provider
//!    output/projection mismatches surface here, against the enriched schema.
//!    Cedar's own warnings are carried through verbatim.
//! 2. Each dialect's checks (temporal, provider), called by name — the
//!    lowered artifacts are concrete about the dialect set, so there is no
//!    registry.
//!
//! A `Lowered` is proof that parse / macro-expansion / lowering already
//! succeeded (those fatal failures surface as [`crate::Error`] from
//! [`ParsedPolicySet::lower`](crate::policy_set::ParsedPolicySet::lower)), so
//! this stage never produces a syntax/lowering error — only validation
//! findings.
//!
//! Every finding carries a [`SourceSpan`] rebased to the original `.dw`
//! source **and** the source itself (from `lowered.dw_src`), so it
//! self-renders: `miette::Report::new(finding)` underlines the offending
//! source with no `with_source_code`. The lowering builds loc-bearing Cedar
//! `ast` (every node carries a `.dw` source location), so a Cedar diagnostic's
//! own label span already points at the offending sub-expression; when a
//! diagnostic carries no label we fall back to the originating rule's `.dw`
//! span from `lowered.rule_spans`, mapped from the lowered policy id via
//! `lowered.rule_ids`.

use cedar_policy::{Schema, ValidationMode, Validator as CedarValidator};
use miette::{Diagnostic, SourceSpan};

use crate::api::Lowered;
use crate::error::{Span, ValidationError, ValidationResult, ValidationWarning};
use crate::extension::dialect::{DogwoodDialect, ValidationCtx};
use crate::extension::provider::validate::ProviderDialect;
use crate::extension::temporal::validate::TemporalDialect;

/// A one-byte span at the start of the source, used when a Cedar diagnostic
/// has no mappable `.dw` location (an unmappable policy id).
const START_SPAN: Span = Span { start: 0, end: 1 };

/// Validate the lowered artifacts against their augmented schema, returning
/// every finding. An empty error channel means the policy set is valid.
pub(crate) fn validate_impl(lowered: &Lowered) -> ValidationResult {
    let mut errors: Vec<ValidationError> = Vec::new();
    let mut warnings: Vec<ValidationWarning> = Vec::new();

    let schema = &lowered.augmented_schema;

    // 1. Cedar schema-aware validation (errors + warnings).
    validate_cedar_side(lowered, schema, &mut errors, &mut warnings);

    // 2. Dialect checks — called by name (the lowered artifacts are concrete
    // about the dialect set). Each dialect's `run` partitions its findings
    // into the two channels.
    let ctx = ValidationCtx {
        schema,
        event_schema: &lowered.event_schema,
        dw_src: &lowered.dw_src,
    };
    for (errs, warns) in [
        TemporalDialect.run(&lowered.temporal, &ctx),
        ProviderDialect.run(&lowered.providers, &ctx),
    ] {
        errors.extend(errs);
        warnings.extend(warns);
    }

    ValidationResult::new(errors, warnings)
}

fn validate_cedar_side(
    lowered: &Lowered,
    schema: &Schema,
    errors: &mut Vec<ValidationError>,
    warnings: &mut Vec<ValidationWarning>,
) {
    if lowered.policies.is_empty() {
        return;
    }
    let result =
        CedarValidator::new(schema.clone()).validate(&lowered.policies, ValidationMode::default());
    for error in result.validation_errors() {
        // The lowered policies now carry `.dw` source locations on every
        // node (see `cedarify::to_ast`), so a Cedar diagnostic's own label
        // span points at the precise offending `.dw` sub-expression. Prefer
        // it; fall back to the whole-rule span only when the diagnostic
        // carries no label at all.
        let (label, offset, len) = miette_span_for_diagnostic(error);
        let span = if has_label(error) {
            SourceSpan::new(offset.into(), len)
        } else {
            let policy_id = error.policy_id().to_string();
            rule_span_for(&policy_id, &lowered.rule_ids, &lowered.rule_spans)
        };
        let help = error.help().as_deref().map(ToString::to_string);
        errors.push(ValidationError::Cedar {
            message: error.to_string(),
            span,
            label,
            help,
            src: lowered.dw_src.clone(),
            // Preserve the underlying Cedar diagnostic so a renderer can
            // surface its full chain (code, nested labels).
            source: Some(std::sync::Arc::new(error.clone())),
        });
    }
    // Carry Cedar's own warnings through verbatim — a caller validating a
    // plain Cedar policy through us must not lose what Cedar would report.
    for warning in result.validation_warnings() {
        warnings.push(ValidationWarning::Cedar(warning.clone()));
    }
}

/// The `.dw` span to report a Cedar diagnostic against: the originating
/// Dogwood rule's span, found by mapping the lowered policy id back through
/// `rule_ids`. Falls back to the start of the source if unmappable.
fn rule_span_for(policy_id: &str, rule_ids: &[String], rule_spans: &[Span]) -> SourceSpan {
    rule_ids
        .iter()
        .position(|id| id == policy_id)
        .and_then(|i| rule_spans.get(i))
        .copied()
        .unwrap_or(START_SPAN)
        .into()
}

/// Does this diagnostic carry at least one labeled span? When it does, that
/// label's byte range is a `.dw`-accurate source location (the lowered
/// policies carry `.dw` `Loc`s), so we prefer it over the whole-rule span.
fn has_label(d: &dyn Diagnostic) -> bool {
    d.labels().is_some_and(|mut ls| ls.next().is_some())
}

/// Pull the primary label + `(start, len)` byte range out of any
/// `miette::Diagnostic`. If it carries no labels, returns `(None, 0, 1)`.
fn miette_span_for_diagnostic(d: &dyn Diagnostic) -> (Option<String>, usize, usize) {
    if let Some(mut labels) = d.labels()
        && let Some(labeled) = labels.next()
    {
        let message = labeled.label().map(ToString::to_string);
        let inner = labeled.inner();
        return (message, inner.offset(), inner.len().max(1));
    }
    (None, 0, 1)
}
