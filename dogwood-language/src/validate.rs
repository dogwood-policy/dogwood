//! The core schema-aware validator: [`validate_impl`], behind
//! [`Validator::validate`](crate::Validator::validate).
//!
//! Given the already-lowered artifacts (a [`Lowered`]) and their augmented
//! schema, it runs every check and accumulates findings
//! into a [`ValidationResult`]:
//!
//! 1. Cedar's schema-aware validator on the lowered policies. Provider
//!    output/projection mismatches surface here, against the enriched schema.
//!    Cedar's own warnings are carried through verbatim, except
//!    `InvalidActionApplication` and `ImpossiblePolicy`, which Dogwood reports
//!    as errors.
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
    #[cfg(test)]
    crate::api::stage_probe::enter("validate");
    let mut errors: Vec<ValidationError> = Vec::new();
    let mut warnings: Vec<ValidationWarning> = Vec::new();

    let schema = &lowered.augmented_schema;

    // 1. Cedar schema-aware validation (errors + warnings), and the
    //    well-formedness of the schema.
    validate_cedar_side(lowered, schema, &mut errors, &mut warnings);
    validate_schema(lowered, &mut errors);

    // The Cedar part reads the request context only through attributes that
    // are not hoisted: lowering adds each leaf's value to the context, so a
    // read of the whole context, or of a hoisted attribute, would not mean what
    // the authored rule says. Lowering recorded each such read. A policy set
    // with no leaf leaves every context as the request's, so it may read one
    // whole, as in Cedar; a hoisted name is reserved even then, since a request
    // may not supply it.
    let has_leaves = !lowered.temporal.is_empty() || !lowered.providers.is_empty();
    for read in &lowered.context_reads {
        if read.whole && !has_leaves {
            continue;
        }
        errors.push(ValidationError::Extension {
            code: "context",
            message: read.message.clone(),
            span: read.span.into(),
            label: None,
            help: None,
            src: Arc::clone(lowered.rule_locs[read.rule].src()),
            source: None,
        });
    }

    // 2. Dialect checks — called by name (the lowered artifacts are concrete
    // about the dialect set). Each dialect's `run` partitions its findings
    // into the two channels. A temporal leaf is checked with the facts its
    // position in its rule establishes.
    let leaf_facts = temporal_leaf_facts(lowered);
    let mut run_dialect = |findings: (Vec<ValidationError>, Vec<ValidationWarning>)| {
        errors.extend(findings.0);
        warnings.extend(findings.1);
    };
    for (range, dw_src) in source_runs(&lowered.temporal_rules, lowered) {
        let ctx = ValidationCtx {
            schema,
            event_schema: &lowered.event_schema,
            dw_src,
            leaf_facts: &leaf_facts,
        };
        run_dialect(TemporalDialect.run(&lowered.temporal[range], &ctx));
    }
    for (range, dw_src) in source_runs(&lowered.provider_rules, lowered) {
        let ctx = ValidationCtx {
            schema,
            event_schema: &lowered.event_schema,
            dw_src,
            leaf_facts: &leaf_facts,
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

/// The facts each hoisted temporal leaf's position establishes, by leaf id: the
/// `has` tests its lowered rule makes before Cedar evaluates `context.<id>`.
fn temporal_leaf_facts(
    lowered: &Lowered,
) -> std::collections::BTreeMap<String, Vec<crate::extension::temporal::facts::Guard>> {
    let ids: std::collections::BTreeSet<&str> =
        lowered.temporal.iter().map(|f| f.id.as_str()).collect();
    let mut out = std::collections::BTreeMap::new();
    for &k in lowered
        .temporal_rules
        .iter()
        .collect::<std::collections::BTreeSet<_>>()
    {
        let id = cedar_policy::PolicyId::new(&lowered.rule_ids[k]);
        let Some(policy) = lowered.policies.policy(&id) else {
            continue;
        };
        let policy: &cedar_policy_core::ast::Policy = policy.as_ref();
        if let Some(condition) = policy.non_scope_constraints() {
            out.extend(crate::extension::temporal::facts::leaf_facts(
                condition,
                &|attr| ids.contains(attr),
            ));
        }
    }
    out
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
        push_cedar_error(lowered, error, error.policy_id().as_ref(), errors);
    }
    // Carry Cedar's own warnings through verbatim — a caller validating a
    // plain Cedar policy through us must not lose what Cedar would report —
    // except an impossible policy, which is an error: its condition is false for
    // every request its scope admits, so it never applies, and a `forbid`
    // written that way protects nothing. Cedar's Rust validator calls it a
    // warning; the formal specification rejects it, as cedar-lean's validator
    // does.
    for warning in result.validation_warnings() {
        // Cedar 4.14 demoted `InvalidActionApplication` (no applicable action)
        // to a warning. Keep it an error: the temporal dialect relies on Cedar
        // rejecting a scope with no request environment.
        if let cedar_policy::ValidationWarning::InvalidActionApplication(_) = warning {
            push_cedar_error(lowered, warning, warning.policy_id().as_ref(), errors);
            continue;
        }
        if !matches!(warning, cedar_policy::ValidationWarning::ImpossiblePolicy(_)) {
            warnings.push(ValidationWarning::Cedar(warning.clone()));
            continue;
        }
        let (label, offset, len) = miette_span_for_diagnostic(warning);
        let (span, src) = match rule_loc_for(warning.policy_id().as_ref(), lowered) {
            Some((_, src)) if has_label(warning) => (SourceSpan::new(offset.into(), len), src),
            Some(rule) => rule,
            None => (START_SPAN.into(), Arc::from("")),
        };
        errors.push(ValidationError::Cedar {
            message: warning.to_string(),
            span,
            label,
            help: Some(
                "no request the rule's scope admits satisfies its condition, so the rule never \
                 applies; check the scope's principal and resource types against the action's \
                 `appliesTo`, and the condition"
                    .to_string(),
            ),
            src,
            source: Some(std::sync::Arc::new(warning.clone())),
        });
    }
}

/// The schema's well-formedness as the formal specification defines it
/// (`Schema.standardAncestors`, which `PolicySet.Valid` requires), beyond
/// what Cedar's schema construction checks: every ancestor of an entity type
/// is a standard entity type. Cedar allows an enumerated one
/// (`entity User in [Application]` with `entity Application enum […]`), and
/// so does cedar-lean's `Schema.validateWellFormed` from `v4.14.0` on; Dogwood
/// keeps the rule. A finding has code `schema`, and no position in the policy
/// source.
fn validate_schema(lowered: &Lowered, errors: &mut Vec<ValidationError>) {
    use cedar_policy_core::validator::{ValidatorEntityTypeKind, ValidatorSchema};
    let schema: &ValidatorSchema = lowered.augmented_schema.as_ref();
    let mut ancestors: Vec<(String, Vec<String>)> = schema
        .entity_types()
        .filter(|ety| matches!(ety.kind, ValidatorEntityTypeKind::Enum(_)))
        .filter(|ety| !ety.descendants.is_empty())
        .map(|ety| {
            let mut descendants: Vec<String> =
                ety.descendants.iter().map(|d| format!("`{d}`")).collect();
            descendants.sort();
            (ety.name().to_string(), descendants)
        })
        .collect();
    ancestors.sort();
    let src = lowered
        .rule_locs
        .first()
        .map_or_else(|| Arc::from(""), |loc| Arc::clone(loc.src()));
    for (name, descendants) in ancestors {
        errors.push(ValidationError::Extension {
            code: "schema",
            message: format!(
                "the enumerated entity type `{name}` is an ancestor of {}; Dogwood requires \
                 every ancestor of an entity type to be a standard entity type, as the formal \
                 specification's schema well-formedness does, though Cedar allows an \
                 enumerated one",
                descendants.join(", ")
            ),
            span: SourceSpan::new(0.into(), 0),
            label: None,
            help: Some(format!(
                "declare `{name}` without `enum`, or take it out of the `in` lists of the \
                 entity types"
            )),
            src: Arc::clone(&src),
            source: None,
        });
    }
}

/// Rebase a Cedar diagnostic onto its `.dw` source and push it as a
/// [`ValidationError::Cedar`].
fn push_cedar_error<D>(
    lowered: &Lowered,
    error: &D,
    policy_id: &str,
    errors: &mut Vec<ValidationError>,
) where
    D: Diagnostic + Clone + Send + Sync + 'static,
{
    // The lowered policies now carry `.dw` source locations on every
    // node (see `cedarify::to_ast`), so a Cedar diagnostic's own label
    // span points at the precise offending `.dw` sub-expression. Prefer
    // it; fall back to the whole-rule span only when the diagnostic
    // carries no label at all.
    let (label, offset, len) = miette_span_for_diagnostic(error);
    let (span, src) = match rule_loc_for(policy_id, lowered) {
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

/// The whole span and source text of the rule `policy_id` was lowered from.
fn rule_loc_for(policy_id: &str, lowered: &Lowered) -> Option<(SourceSpan, Arc<str>)> {
    let k = lowered.rule_index.get(policy_id).copied()?;
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
