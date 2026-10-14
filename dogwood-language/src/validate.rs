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
//! source **and** the text of its rule (from `lowered.rule_locs`, found by
//! mapping the lowered policy id through `lowered.rule_ids`), so it
//! self-renders: `miette::Report::new(finding)` underlines the offending
//! source with no `with_source_code`. The lowering builds loc-bearing Cedar
//! `ast` (every node carries a `.dw` source location), so a Cedar diagnostic's
//! own label span already points at the offending sub-expression; when a
//! diagnostic carries no label we fall back to the originating rule's whole
//! `.dw` span.

use std::ops::Range;
use std::sync::Arc;

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
    let mut run_dialect = |findings: (Vec<ValidationError>, Vec<ValidationWarning>)| {
        errors.extend(findings.0);
        warnings.extend(findings.1);
    };
    for (range, dw_src) in source_runs(&lowered.temporal_rules, lowered) {
        let ctx = ValidationCtx {
            schema,
            event_schema: &lowered.event_schema,
            dw_src,
        };
        run_dialect(TemporalDialect.run(&lowered.temporal[range], &ctx));
    }
    for (range, dw_src) in source_runs(&lowered.provider_rules, lowered) {
        let ctx = ValidationCtx {
            schema,
            event_schema: &lowered.event_schema,
            dw_src,
        };
        run_dialect(ProviderDialect.run(&lowered.providers[range], &ctx));
    }

    // EXPERIMENTAL-ARITHMETIC: with the feature on, arithmetic operands are
    // accepted. Warn once per policy set, anchored at the first temporal
    // leaf that uses them.
    #[cfg(feature = "experimental-arithmetic")]
    'arith: for (range, dw_src) in source_runs(&lowered.temporal_rules, lowered) {
        for leaf in &lowered.temporal[range] {
            if crate::extension::temporal::check::condition_has_arith(&leaf.condition.condition) {
                warnings.push(ValidationWarning::Extension {
                    code: "temporal",
                    message: "arithmetic operators are experimental and may change in a \
                              future release"
                        .to_string(),
                    span: leaf.condition.span.into(),
                    label: None,
                    help: None,
                    src: std::sync::Arc::clone(dw_src),
                    source: None,
                });
                break 'arith;
            }
        }
    }

    ValidationResult::new(errors, warnings)
}

/// Split leaves into maximal runs whose rules share one source text.
fn source_runs<'a>(
    leaf_rules: &[usize],
    lowered: &'a Lowered,
) -> Vec<(Range<usize>, &'a Arc<str>)> {
    let mut runs: Vec<(Range<usize>, usize, usize)> = Vec::new();
    for (j, &k) in leaf_rules.iter().enumerate() {
        let source = lowered.rule_sources[k];
        match runs.last_mut() {
            Some((range, run_source, _)) if *run_source == source => range.end = j + 1,
            _ => runs.push((j..j + 1, source, k)),
        }
    }
    runs.into_iter()
        .map(|(range, _, k)| (range, lowered.rule_locs[k].src()))
        .collect()
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
        let (span, src) = match rule_loc_for(error.policy_id().as_ref(), lowered) {
            Some((_, src)) if has_label(error) => (SourceSpan::new(offset.into(), len), src),
            Some(rule) => rule,
            // No `.dw` text to index, so any label offsets are dropped.
            None => (START_SPAN.into(), Arc::from("")),
        };
        let help = error.help().as_deref().map(ToString::to_string);
        // Cedar names a provider enum by its exported name; the policy wrote
        // the declared one.
        let declared = |text: String| declared_enum_names(&text, &lowered.enum_names);
        errors.push(ValidationError::Cedar {
            message: declared(error.to_string()),
            span,
            label: label.map(declared),
            help: help.map(declared),
            src,
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

/// The whole span and source text of the rule `policy_id` was lowered from.
fn rule_loc_for(policy_id: &str, lowered: &Lowered) -> Option<(SourceSpan, Arc<str>)> {
    let k = lowered.rule_ids.iter().position(|id| id == policy_id)?;
    let loc = &lowered.rule_locs[k];
    Some((loc.span(), loc.src().clone()))
}

/// `text` with each exported provider enum name replaced by its declared
/// name (`Drupe::GuardDuty_Severity` -> `GuardDuty::Severity`). `names` maps
/// declared to exported names. Only whole names are replaced: an occurrence
/// inside a longer name (`Other::GuardDuty_Severity` for a root-namespace
/// `GuardDuty_Severity`) is left alone.
pub(crate) fn declared_enum_names(
    text: &str,
    names: &std::collections::BTreeMap<String, String>,
) -> String {
    let is_name_char = |c: char| c.is_alphanumeric() || c == '_' || c == ':';
    let mut out = text.to_string();
    // Longest first, so `A::B_C` is not rewritten through `B_C`.
    let mut pairs: Vec<(&String, &String)> = names.iter().collect();
    pairs.sort_by_key(|(_, exported)| std::cmp::Reverse(exported.len()));
    for (declared, exported) in pairs {
        let mut result = String::with_capacity(out.len());
        let mut rest = out.as_str();
        while let Some(i) = rest.find(exported.as_str()) {
            let before = rest[..i].chars().next_back();
            let after = rest[i + exported.len()..].chars().next();
            // `::` may follow (`…_Score::"LOW"`), a name character may not.
            let after_ok = match after {
                None => true,
                Some(':') => rest[i + exported.len()..].starts_with("::"),
                Some(c) => !is_name_char(c),
            };
            result.push_str(&rest[..i]);
            if before.is_none_or(|c| !is_name_char(c)) && after_ok {
                result.push_str(declared);
            } else {
                result.push_str(exported);
            }
            rest = &rest[i + exported.len()..];
        }
        result.push_str(rest);
        out = result;
    }
    out
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

#[cfg(test)]
mod tests {
    use super::declared_enum_names;
    use std::collections::BTreeMap;

    #[test]
    fn exported_enum_names_are_shown_by_their_declared_name() {
        let names = BTreeMap::from([(
            "MyGuardrails::Score".to_string(),
            "Drupe::MyGuardrails_Score".to_string(),
        )]);
        assert_eq!(
            declared_enum_names(
                "entity `Drupe::MyGuardrails_Score::\"LWO\"` is of an enumerated entity type; \
                 the types String and Drupe::MyGuardrails_Score are not compatible",
                &names
            ),
            "entity `MyGuardrails::Score::\"LWO\"` is of an enumerated entity type; \
             the types String and MyGuardrails::Score are not compatible"
        );
    }

    #[test]
    fn only_whole_names_are_replaced() {
        // Home namespace is the root: the exported name is bare.
        let names = BTreeMap::from([(
            "MyGuardrails::Score".to_string(),
            "MyGuardrails_Score".to_string(),
        )]);
        assert_eq!(
            declared_enum_names(
                "MyGuardrails_Score, Other::MyGuardrails_Score, MyGuardrails_Scores",
                &names
            ),
            "MyGuardrails::Score, Other::MyGuardrails_Score, MyGuardrails_Scores"
        );
    }
}
