//! Schema-aware validation of a parsed `temporal { … }` leaf.
//!
//! Temporal leaf validation (re-bound to this crate's native temporal AST).
//! Covers three check groups:
//!
//! * **schema compliance** — every predicate names a declared action, every
//!   named argument is a declared input field, every entity literal names a
//!   declared entity type (honoring enum eids), and every `context.input.X`
//!   path resolves against the scoped action's input record;
//! * **time-point dependence** — every monitoring scope has a body that can
//!   vary across timepoints;
//! * **type checking** — comparison operands agree and predicate arguments
//!   match their declared field types.
//!
//! The aggregation free-variable binding check lives natively in `check.rs`
//! (run at parse time); the macro reserved-name / within-interval checks
//! live in `crate::macros`. Range-restriction free-var/dead-binder analysis,
//! the ad-hoc structural restrictions, scope-alias typing, and entity
//! subtyping are not ported.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::{
    AggExpr, AggExprKind, BinderSlot, CmpOp, Condition, ConditionKind, Interval, Predicate, Term,
    WithinSpec,
};
use super::schema_info::{ActionHandle, SchemaInfo};
use crate::error::{Span, ValidationError};

/// A single temporal validation finding, located in the temporal block body
/// (the validator rebases it into the `.dw` source). `span` is `None` when
/// the finding has no narrower location than the whole leaf.
#[derive(Debug, Clone)]
pub struct LeafError {
    pub message: String,
    pub span: Option<Span>,
}

/// Validate one parsed temporal leaf against the schema projection.
///
/// `info` is derived from the (augmented) Cedar schema. `target_actions` is the
/// set of actions the leaf's rule scope RESOLVES to — not the actions it names: a
/// group is expanded to its transitive members, and an unconstrained scope to every
/// action. The leaf is evaluated for each of them, so both `context.<path>`
/// resolution and operand typing run against every one, and a condition wrong for
/// any single action is wrong. This mirrors Cedar, which validates a policy in every
/// request environment its scope admits.
///
/// Returns every schema-compliance error found; an empty vec means the leaf
/// is consistent with the schema.
pub fn validate_leaf(
    leaf: &super::Temporal,
    info: &SchemaInfo,
    target_actions: &[crate::api::ActionRef],
    narrow: ScopeNarrowing<'_>,
) -> Vec<LeafError> {
    // Predicate event / field-name validation is owned by the event-schema
    // checker (`event_schema::validate::validate_condition`, run alongside
    // this in the dialect's `validate`) — it knows event kinds and the
    // canonical `input.<field>` path model. The checks below are the ones
    // unique to the temporal dialect: entity types, `context.input` paths on
    // the request, time-point dependence, and operand/argument typing.
    let mut errs = Vec::new();
    check_entity_types(&leaf.condition, info, &mut errs);
    check_context_fields(&leaf.condition, info, target_actions, narrow, &mut errs);
    check_tp_dependence(&leaf.condition, &mut errs);
    check_types(&leaf.condition, info, target_actions, narrow, &mut errs);
    check_sum_summands(&leaf.condition, &mut errs);
    errs
}

// ─── DogwoodDialect impl ────────────────────────────────────────────

use crate::api::TemporalField;
use crate::extension::dialect::{DogwoodDialect, Rendered, ValidationCtx};

/// One temporal validation finding: a defect in a temporal leaf, with its
/// span already rebased into the `.dw` source.
pub struct TemporalFinding {
    pub message: String,
    pub span: Span,
}

/// The temporal dialect. Owns its leaf type — the public [`TemporalField`],
/// which carries the parsed condition and its `ActionScope`. `validate` calls
/// it by name.
pub struct TemporalDialect;

impl DogwoodDialect for TemporalDialect {
    type Leaf = TemporalField;
    type Finding = TemporalFinding;

    fn marker(&self) -> &'static str {
        "temporal"
    }

    fn validate(&self, leaves: &[TemporalField], ctx: &ValidationCtx<'_>) -> Vec<TemporalFinding> {
        if leaves.is_empty() {
            return Vec::new();
        }
        // The temporal checks need Cedar's typed view of the augmented schema.
        // `cedar_policy::Schema` is a transparent newtype over a
        // `ValidatorSchema`, so build the projection from `as_ref()` — no
        // re-parse of a schema source string.
        let info = SchemaInfo::from_validator_schema(ctx.schema.as_ref());
        let max_window = ctx.event_schema.max_window();
        let mut findings = Vec::new();
        for field in leaves {
            // The leaf's inner spans are relative to the `temporal { … }`
            // block body; `field.condition.span.start` is that body's offset
            // in the `.dw` source.
            let base = field.condition.span.start;

            // Event-schema names check: every predicate must name a declared
            // event kind and mention only fields declared on it (the canonical
            // `input.<field>` path convention). This is the authority on event
            // *field names* — the dialect's own checks below no longer do that.
            // The check has no narrower span than the leaf, so report at the
            // block body.
            if let Err(message) = crate::event_schema::validate::validate_condition(
                &field.condition.condition,
                ctx.event_schema,
            ) {
                findings.push(TemporalFinding {
                    message,
                    span: field.condition.span,
                });
            }

            // Window checks: every `within` window in the leaf must be
            // positive, in-range (no i64 overflow), and at most the event
            // schema's `max_window` cap. Each violation is rebased from the
            // block body into the `.dw` source.
            for e in check_windows(&field.condition.condition, max_window) {
                findings.push(TemporalFinding {
                    message: e.message,
                    span: match e.span {
                        Some(s) => s.rebased(base),
                        None => field.condition.span,
                    },
                });
            }

            // An unconstrained `action` scope is checked against EVERY action, because
            // the rule can fire on every action. Leaving it unchecked was fail-open in
            // the way this dialect is uniquely exposed to: a `context.<path>` inside a
            // temporal leaf lives in the hoisted AST and is never lowered to a
            // Cedar-visible expression, so if this check skips it, NOTHING validates it
            // and the rule silently monitors nothing at run time.
            //
            // History, because the exception looked deliberate: an earlier fix
            // (`9015f268`) had to stop a FALSE rejection where a scope was recorded as
            // `None` and `None` was read as "every declared action" — so a rule scoped
            // `action in [A, B]` was checked against actions it could never fire on.
            // The follow-up (`32de2889`) split that `None` into `List` and
            // `Unconstrained`, fixed the list case, and left an unconstrained scope "to
            // Cedar as before" — which its own reasoning rules out, Cedar being unable
            // to see inside the leaf. With the two cases now distinguished, checking a
            // genuinely unconstrained scope against every action cannot reproduce that
            // false rejection: the rule really does reach all of them.
            let narrow = ScopeNarrowing {
                principal: Some(&field.principal),
                resource: Some(&field.resource),
            };
            for e in validate_leaf(&field.condition, &info, &field.target_actions, narrow) {
                let span = match e.span {
                    Some(s) => s.rebased(base),
                    // No narrower location than the leaf: the block body.
                    None => field.condition.span,
                };
                findings.push(TemporalFinding {
                    message: e.message,
                    span,
                });
            }
        }
        findings
    }

    fn render(&self, finding: TemporalFinding, src: &std::sync::Arc<str>) -> Rendered {
        let help = derive_temporal_help(&finding.message);
        Rendered::Error(ValidationError::Extension {
            code: self.marker(),
            message: finding.message,
            span: finding.span.into(),
            label: None,
            help,
            src: src.clone(),
            source: None,
        })
    }
}

/// Derive actionable help text from a temporal validation finding's message.
/// The help text appears as miette's `help:` annotation below the diagnostic
/// and is separate from the primary message — it tells the user what to *do*.
fn derive_temporal_help(message: &str) -> Option<String> {
    // ─── Type-check findings ────────────────────────────────────────
    if message.contains("comparison requires numeric operands") {
        return Some(
            "ordering comparisons (<, <=, >, >=) require both operands to be \
             Long or decimal; use == or != for non-numeric equality"
                .to_string(),
        );
    }
    if message.contains("equality requires both sides to have the same type") {
        return Some(
            "== and != compare values of the same type; check that both sides \
             resolve to the same schema type (e.g. both String, both Long)"
                .to_string(),
        );
    }
    if message.starts_with("argument `") && message.contains("expects") {
        return Some(
            "predicate field types are inferred from the event schema; check \
             that the value matches the declared type for this field"
                .to_string(),
        );
    }
    if message.starts_with("cannot sum `") {
        return Some(
            "only `Long` fields can be summed; use `count for (…)` to tally \
             matching rows, or sum a `Long`-typed field. This matches Cedar, \
             whose +, -, * operate only on Long."
                .to_string(),
        );
    }

    // ─── Entity-type findings ───────────────────────────────────────
    if message.starts_with("unknown entity type") {
        return Some(
            "entity types must be declared in the Cedar schema; check the \
             spelling and namespace"
                .to_string(),
        );
    }
    if message.contains("is an enum entity type") && message.contains("not one of its permitted") {
        return Some(
            "enum entity types restrict their ids to a fixed set declared in \
             the schema; use one of the permitted values"
                .to_string(),
        );
    }

    // ─── Context-path findings ──────────────────────────────────────
    if message.contains("must be of the form `context.input.<field>`") {
        return Some(
            "temporal conditions access context fields as `context.input.<field>`; \
             output fields are accessed via a resolved-predicate binding"
                .to_string(),
        );
    }
    if message.contains("has no input field") {
        return Some(
            "check the field name against the action's input type declaration \
             in the Cedar schema"
                .to_string(),
        );
    }
    if message.contains("record has no field") {
        return Some(
            "the path traverses into a record type that does not declare this \
             field; check the nested record structure in the schema"
                .to_string(),
        );
    }
    if message.contains("accesses a field of a non-record type") {
        return Some(
            "dot-access (`.field`) is only valid on record types; the preceding \
             segment resolves to a scalar or entity, not a record"
                .to_string(),
        );
    }

    // ─── Max-window findings ────────────────────────────────────────
    if message.contains("exceeds the maximum allowed window") {
        return Some(
            "every temporal `within` window is capped by the event schema's \
             `max_window` (default 24h); either shorten this window or raise \
             the cap with a `max_window = <interval>` directive at the top of \
             the event schema"
                .to_string(),
        );
    }

    if message.contains("a `tp` variable must be declared `Timepoint`") {
        return Some(
            "`tp(t)` binds `t` to the current timepoint index; declare the \
             binder as `Timepoint` (`exists (t: Timepoint)` or `for (t: \
             Timepoint)`), and use a separate variable for data fields"
                .to_string(),
        );
    }

    // ─── Timepoint-dependence findings ──────────────────────────────
    if message.contains("does not vary with the current timepoint") {
        return Some(
            "every temporal conjunct must reference at least one event \
             (predicate match, `formerly`, `previous`, or `tp`); a conjunct \
             that depends only on `context` is a static guard and belongs in \
             a Cedar `when { … }` clause instead"
                .to_string(),
        );
    }

    // ─── Event-schema findings (from event_schema::validate) ────────
    if message.contains("does not name a declared event") {
        return Some(
            "check the action name and event kind; event kinds are typically \
             `request` or `response` and derive from the schema"
                .to_string(),
        );
    }
    if message.contains("mentions field") && message.contains("which is not declared") {
        return Some(
            "check the field name against the event schema; the declared fields \
             are listed in the error above"
                .to_string(),
        );
    }

    // ─── check.rs findings (these pass through as temporal findings) ─
    if message.contains("not range-restricted") && message.contains("exists") {
        return Some(
            "an `exists` variable must appear in a positive predicate field \
             binding, `tp(var)`, or `(agg) == var` within the body"
                .to_string(),
        );
    }
    if message.contains("not range-restricted by a preceding conjunct") {
        return Some(
            "filters (ordering comparisons and negations) require their \
             variables to be bound by an earlier conjunct in the same `&&` \
             chain; reorder so the binding predicate comes first"
                .to_string(),
        );
    }
    if message.contains("aggregate") && message.contains("immediate operand") {
        return Some(
            "aggregates (`sum`/`count`) can only appear directly as one side \
             of a comparison (e.g. `(count …) == n`), not nested inside other \
             terms or passed as predicate arguments"
                .to_string(),
        );
    }
    if message.contains("not in its `for` domain") {
        return Some(
            "the `sum` bound variable must be declared in the `for` list so \
             its values are collected for aggregation"
                .to_string(),
        );
    }
    if message.contains("used in the aggregation body but is bound by neither") {
        return Some(
            "every free variable in a `where` body must be bound by the `for` \
             list or an enclosing `exists`; add it to `for`"
                .to_string(),
        );
    }

    None
}

// ─── Type checking ──────────────────────────────────────────────────
//
// A variable-type environment is built from the scoped action's input
// fields plus every binder's **declared** type — each `exists (x: T)` and
// aggregation `for (v: T)` carries a mandatory annotation, so a bound
// variable's type is read from its declaration, never reverse-inferred
// from a use site. The condition is then walked to report mismatched
// comparison operands and predicate arguments; because a bound variable's
// env entry is its declared type, those same checks enforce that every use
// *respects the annotation* (e.g. `exists (x: Long). … x == "s"` is now a
// type error, not silently reconciled). Types are the "rich" strings of
// [`super::schema_info::FieldType`] (`"int"`, `"string"`, `"decimal"`,
// `"boolean"`, `"timepoint"`, `"entity:X"`, `"array<T>"`, `"object"`).
// Type inference for temporal terms, re-bound to the native AST.
// Entity subtyping is not modeled (the projection carries no ancestor
// closure), so entity comparisons require equal tags or an untagged side —
// a conservative subset.

fn check_types(
    c: &Condition,
    info: &SchemaInfo,
    target_actions: &[crate::api::ActionRef],
    narrow: ScopeNarrowing<'_>,
    errs: &mut Vec<LeafError>,
) {
    // Type inference seeds from ONE action's signature, so the condition is
    // checked once per action its scope resolves to — the same set
    // `check_context_fields` resolves paths against. A field may be typed
    // differently by two of them (`amount` a `Long` on one action and a `String`
    // on another), and the leaf is evaluated for each, so a comparison wrong for
    // ANY of them is wrong: this mirrors Cedar, which validates a policy in every
    // request environment its scope admits and fails if the body fails in one.
    //
    // Seeding from a single concrete action was why a non-`==` scope was checked
    // at all: `ActionScope::concrete()` returns `None` for a list or an
    // unconstrained scope, nothing seeded, and because every comparison check is
    // guarded on both operands having a type, ALL of them were skipped. That was
    // fail-open in the direction this dialect is uniquely exposed to — a
    // mis-typed comparison is permanently false, so the condition never holds and
    // a `forbid` never fires — and Cedar cannot catch it, the leaf being an opaque
    // `context.<id>` boolean.
    //
    // The same finding is reported once however many actions produce it, so a
    // wide scope does not multiply one mistake into one error per action.
    let mut seen: std::collections::BTreeSet<(String, Option<usize>)> = Default::default();
    for action in target_actions {
        let mut per_action = Vec::new();
        check_types_for_action(c, info, action, narrow, &mut per_action);
        for e in per_action {
            if seen.insert((e.message.clone(), e.span.map(|s| s.start))) {
                errs.push(e);
            }
        }
    }
}

fn check_types_for_action(
    c: &Condition,
    info: &SchemaInfo,
    action: &crate::api::ActionRef,
    narrow: ScopeNarrowing<'_>,
    errs: &mut Vec<LeafError>,
) {
    let rule_sig = info.action(action.namespace.as_deref(), &action.id);
    // An action for which the rule's principal/resource scope admits no request
    // environment is one the rule can never be evaluated on, so holding its types
    // against the condition is a false rejection. Cedar filters whole triples.
    if let Some(sig) = rule_sig.as_ref()
        && !sig.admits_any_env(narrow.principal, narrow.resource)
    {
        return;
    }
    let env = build_type_env(c, info, rule_sig.as_ref());

    walk(c, &mut |node| match &node.kind {
        ConditionKind::Predicate(p) => {
            let ns = predicate_namespace(p);
            if let Some(sig) = info.action(ns.as_deref(), &p.action) {
                for na in &p.args {
                    // Resolve the predicate field's declared type by its FULL
                    // dotted path (`input.mode`, `output.status`) — the same
                    // walk the comparison path uses for `context.input.mode`
                    // (see `context_field_type`). The field name `na.name` is a
                    // dotted string (`"input.mode"`); resolving it segment by
                    // segment against the predicate action's context record is
                    // what makes the type check fire. A flat lookup of the
                    // whole dotted string never matched, so field-pattern
                    // arguments used to go entirely un-type-checked and a
                    // mis-typed literal validated cleanly (then silently never
                    // matched a real event at runtime).
                    if let Some(expected) = predicate_field_type(&na.field_path(), &sig) {
                        check_arg_type(
                            &na.value,
                            &expected,
                            &p.action,
                            &na.name,
                            &env,
                            rule_sig.as_ref(),
                            narrow,
                            p.span,
                            errs,
                        );
                    }
                }
            }
        }
        // `tp(x)` binds `x` to the current TIMEPOINT index, so the binder's
        // declared type must be `Timepoint`. Any other declaration conflates
        // a timepoint with a data value: every use of `x` against a data
        // field can never match, so the whole condition is permanently false
        // — a validated dead guard (fail-open by vacuity on a `forbid`). A
        // sigil slot has no concrete name yet; expansion re-validates.
        ConditionKind::Tp {
            var: BinderSlot::Name(name),
        } => {
            if let Some(ty) = env.get(name)
                && ty != "timepoint"
            {
                errs.push(LeafError {
                    message: format!(
                        "`tp({name})` binds `{name}` to the current timepoint, \
                         but `{name}` is declared `{}`; a `tp` variable must be \
                         declared `Timepoint`",
                        display_type(ty)
                    ),
                    span: Some(node.span),
                });
            }
        }
        ConditionKind::Comparison { op, left, right } => {
            let (lt, rt) = (
                term_type(left, &env, rule_sig.as_ref(), narrow),
                term_type(right, &env, rule_sig.as_ref(), narrow),
            );
            if let (Some(l), Some(r)) = (lt, rt) {
                let numeric = matches!(op, CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge);
                if numeric && !(is_numeric(&l) && is_numeric(&r)) {
                    errs.push(LeafError {
                        message: format!(
                            "comparison requires numeric operands on both sides, got `{}` and `{}`",
                            display_type(&l),
                            display_type(&r)
                        ),
                        span: Some(node.span),
                    });
                } else if !numeric && !types_compatible(&l, &r) {
                    errs.push(LeafError {
                        message: format!(
                            "equality requires both sides to have the same type, got `{}` and `{}`",
                            display_type(&l),
                            display_type(&r)
                        ),
                        span: Some(node.span),
                    });
                }
            }
        }
        _ => {}
    });
}

// ─── Aggregation summand typing ──────────────────────────────────────
//
// A `sum <v> for (<v>: T), … . where …` adds together the values of its
// summand `<v>`. Only a `Long` summand is meaningful: Dogwood arithmetic (like
// Cedar's `+`/`-`/`*`) operates only on `Long`, decimals are not summable, and
// timepoints are ordinal positions rather than quantities. A non-`Long`
// summand is otherwise silently accepted — `term_type(Term::Agg)` reports the
// whole aggregate as `int` regardless of what is summed, and the summand is a
// *use* (not a declaration site), so `check_types`'s operand/argument checks
// never see its declared type.
//
// The summand is a bare variable. `check_aggregation` (in `check.rs`, run at
// parse time) already requires it to be one of this aggregation's own `for`
// binders, so by the time typing runs the summand is guaranteed to be a `for`
// binder. This check nonetheless resolves the summand's type from the full set
// of declared binders in scope (enclosing `exists` + every `for` list) as
// defense-in-depth: `validate_leaf` is `pub` (though the `extension` module is
// `pub(crate)`, so only within this crate), and an in-crate caller that
// constructed a `Temporal` directly — bypassing `Temporal::parse` and hence the
// parse-time check — would still get the summand typed correctly here rather
// than silently skipped. A timepoint in the `for (…)` binders is fine (it
// controls per-timepoint row distinctness); only the *summand* is constrained.
fn check_sum_summands(c: &Condition, errs: &mut Vec<LeafError>) {
    // Every declared binder's type (enclosing `exists` + every aggregation
    // `for` element), by name — the same set `build_type_env` harvests, kept
    // as the source-syntax `Type` for the diagnostic.
    let binder_types = collect_declared_binder_types(c);
    walk(c, &mut |node| {
        for_each_term(node, &mut |t| {
            let Term::Agg(agg) = t else { return };
            let AggExprKind::Sum { bound_var, .. } = &agg.kind else {
                return;
            };
            // A summand still carrying a macro sigil has no concrete name;
            // expansion re-runs validation on the substituted form.
            let BinderSlot::Name(summand) = bound_var else {
                return;
            };
            // The summand is guaranteed to be bound in scope (see
            // `check_aggregation`); an unresolved name means a sibling defect
            // already reported by that check, so skip rather than double-report.
            let Some(ty) = binder_types.get(summand) else {
                return;
            };
            if let Some(message) = sum_summand_type_error(summand, ty) {
                errs.push(LeafError {
                    message,
                    span: Some(agg.span),
                });
            }
        });
    });
}

/// Collect every declared binder's source-syntax [`Type`](super::ast::Type) by
/// name: each `exists (x: T)` and every aggregation `for (v: T)` element.
/// Mirrors [`collect_declared_binders`] (which keeps rich-type strings for the
/// operand checks) but retains the `Type` for summand diagnostics; innermost
/// binder wins on a name clash, matching that function's lexical approximation.
fn collect_declared_binder_types(c: &Condition) -> BTreeMap<String, super::ast::Type> {
    let mut map = BTreeMap::new();
    let record = |binder: &super::ast::TypedBinder, map: &mut BTreeMap<_, _>| {
        if let BinderSlot::Name(name) = &binder.slot {
            map.insert(name.clone(), binder.ty.clone());
        }
    };
    walk(c, &mut |node| match &node.kind {
        ConditionKind::Exists { var, .. } => record(var, &mut map),
        ConditionKind::Comparison { left, right, .. } => {
            for operand in [left, right] {
                if let Term::Agg(agg) = operand {
                    match &agg.kind {
                        AggExprKind::Sum { for_vars, .. } | AggExprKind::Count { for_vars, .. } => {
                            for v in for_vars {
                                record(v, &mut map);
                            }
                        }
                        AggExprKind::Call(_) => {}
                    }
                }
            }
        }
        _ => {}
    });
    map
}

/// The error message for a non-`Long` aggregation summand, or `None` if the
/// summand type is `Long` (the only summable type). Each message names the
/// summand and its declared type, with a type-specific reason.
fn sum_summand_type_error(summand: &str, ty: &super::ast::Type) -> Option<String> {
    use super::ast::Type;
    match ty {
        // `Long` is the only summable type.
        Type::Named(path) if path.last().map(String::as_str) == Some("Long") => None,
        Type::Timepoint => Some(format!(
            "cannot sum `{summand}`: sum requires a `Long` summand, but `{summand}` is \
             `Timepoint`. Timepoints are ordinal positions, not quantities — use a Timepoint \
             in the `for (…)` binders to keep per-timepoint rows, not as the value being summed."
        )),
        Type::Named(path)
            if matches!(path.last().map(String::as_str), Some("decimal" | "Decimal")) =>
        {
            Some(format!(
                "cannot sum `{summand}`: sum requires a `Long` summand, but `{summand}` is \
                 `Decimal`. Dogwood arithmetic operates only on `Long` values, not decimals."
            ))
        }
        Type::Named(_) => Some(format!(
            "cannot sum `{summand}`: sum requires a `Long` summand, but `{summand}` is `{}`.",
            ty.render()
        )),
    }
}

// Each parameter carries distinct context the type check needs (the term, its
// expected/declared types, the scoped action, the env, and the span to report
// against); bundling them into a struct would not clarify the call sites.
#[allow(clippy::too_many_arguments)]
fn check_arg_type(
    arg: &Term,
    expected: &str,
    action: &str,
    param: &str,
    env: &BTreeMap<String, String>,
    rule_sig: Option<&ActionHandle>,
    narrow: ScopeNarrowing<'_>,
    pred_span: Span,
    errs: &mut Vec<LeafError>,
) {
    if let Some(got) = term_type(arg, env, rule_sig, narrow)
        && !param_accepts(expected, &got)
    {
        errs.push(LeafError {
            message: format!(
                "argument `{param}` of `{action}` expects `{}` but got `{}`",
                display_type(expected),
                display_type(&got)
            ),
            span: Some(pred_span),
        });
    }
}

/// Build a variable-name → rich-type environment: the scoped action's
/// input fields, plus every bound variable typed by its **declared**
/// annotation.
///
/// A temporal variable is only ever introduced by a binder that carries a
/// mandatory type annotation — `exists (x: T)` and each aggregation
/// `for (v: T)` element (the grammar has no un-annotated binder form). So a
/// bound variable's type is read straight from its declaration rather than
/// reverse-inferred from a use site. This makes the annotation authoritative:
/// the walk in [`check_types`] then verifies that every *use* (predicate
/// arg, comparison operand) is consistent with the declared type, instead of
/// letting the first use silently define it.
fn build_type_env(
    c: &Condition,
    _info: &SchemaInfo,
    rule_sig: Option<&ActionHandle>,
) -> BTreeMap<String, String> {
    let mut env = BTreeMap::new();
    // Seed the scoped action's input field names with their types (a bare
    // `field` reference in the leaf resolves to the rule action's input).
    if let Some(sig) = rule_sig {
        for name in sig.input_field_names() {
            if let Some(ty) = sig.input_field_type(&name) {
                env.insert(name, ty);
            }
        }
    }
    // Every declaration-site binder types its variable by annotation.
    collect_declared_binders(c, &mut env);
    env
}

/// Walk the condition and record each declaration-site binder's variable
/// with the rich type of its **declared** annotation: `exists (x: T)` and
/// every aggregation `for (v: T)` element. A binder still carrying a macro
/// sigil (unresolved `?p`/`$b`) has no concrete name yet, so it is skipped —
/// expansion re-runs validation on the substituted form.
fn collect_declared_binders(c: &Condition, env: &mut BTreeMap<String, String>) {
    let record = |binder: &super::ast::TypedBinder, env: &mut BTreeMap<String, String>| {
        if let super::ast::BinderSlot::Name(name) = &binder.slot {
            // A binder's declared type is authoritative; if the same name is
            // introduced by nested binders, the innermost (last-walked) wins,
            // matching lexical scoping for the shapes the language admits.
            env.insert(name.clone(), rich_type_of_annotation(&binder.ty));
        }
    };
    walk(c, &mut |node| match &node.kind {
        ConditionKind::Exists { var, .. } => record(var, env),
        ConditionKind::Comparison { left, right, .. } => {
            for operand in [left, right] {
                if let Term::Agg(agg) = operand {
                    match &agg.kind {
                        AggExprKind::Sum { for_vars, .. } | AggExprKind::Count { for_vars, .. } => {
                            for v in for_vars {
                                record(v, env);
                            }
                        }
                        AggExprKind::Call(_) => {}
                    }
                }
            }
        }
        _ => {}
    });
}

/// Map a binder's declared [`Type`](super::ast::Type) annotation to the
/// "rich" type string the checks compare against. `Timepoint` is its own
/// tag (distinct from `int`, so a timepoint variable is not silently
/// comparable to an integer); a named type maps through the same vocabulary
/// as a schema field: the numeric/string/decimal/boolean scalars, or an
/// `entity:<Name>` for anything else (a declared entity type).
fn rich_type_of_annotation(ty: &super::ast::Type) -> String {
    use super::ast::Type;
    match ty {
        Type::Timepoint => "timepoint".to_string(),
        Type::Named(path) => {
            let last = path.last().map(String::as_str).unwrap_or_default();
            match last {
                "Long" => "int".to_string(),
                "String" => "string".to_string(),
                "Bool" | "Boolean" => "boolean".to_string(),
                "decimal" | "Decimal" => "decimal".to_string(),
                // Any other named type is a declared entity type; tag it with
                // its simple name so entity comparisons check by tag.
                other => format!("entity:{other}"),
            }
        }
    }
}

/// The rich type of a term, or `None` if it can't be classified (a free
/// variable, wildcard, or an unresolved path).
fn term_type(
    t: &Term,
    env: &BTreeMap<String, String>,
    rule_sig: Option<&ActionHandle>,
    narrow: ScopeNarrowing<'_>,
) -> Option<String> {
    match t {
        Term::Var(v) => env.get(v).cloned(),
        Term::Integer(_) => Some("int".to_string()),
        Term::Decimal(_) => Some("decimal".to_string()),
        Term::String(_) => Some("string".to_string()),
        Term::Bool(_) => Some("boolean".to_string()),
        Term::Entity { ty, .. } => Some(format!("entity:{}", simple_name(ty))),
        Term::Array(elems) => Some(array_literal_type(elems)),
        Term::ContextField(path) => context_field_type(path, rule_sig),
        Term::ScopeField(path) => scope_field_type(path, rule_sig, narrow),
        // An aggregate (`count`/`sum`) yields a `Long`; typed as int so a
        // comparison against it (`(count …) == n`, `sum … > k`) checks like
        // any numeric operand.
        Term::Agg(_) => Some("int".to_string()),
        Term::Wildcard | Term::ParamRef(_) | Term::BinderRef(_) => None,
    }
}

/// Type of a `context.…` path: walk the scoped action's full declared context
/// record (via the schema handle, which reads Cedar's own typed context), so
/// `context.input.x`, `context.system.now`, etc. all resolve. A `principal` /
/// `resource` head is an ordinary context field (Cedar semantics), not the
/// scope — the scope entities are typed by [`scope_field_type`].
fn context_field_type(path: &[String], rule_sig: Option<&ActionHandle>) -> Option<String> {
    match rule_sig?.resolve_context_path(path) {
        super::schema_info::PathResolution::Resolved(ty) => Some(ty),
        _ => None,
    }
}

/// The declared rich type of a predicate field pattern's argument, resolved by
/// its full dotted path (`input.mode`, `output.status`, `system.now`) against
/// the *predicate's* action context record — the counterpart to
/// [`context_field_type`], which resolves the *rule's* `context.…` operands.
/// Returns `None` when the path does not fully resolve (an undeclared or
/// non-record segment), which the event-schema names check already reports; a
/// path that resolves to a group rather than a leaf yields that group's rich
/// type (`"object"`), which `check_arg_type` compares like any other.
fn predicate_field_type(path: &[String], sig: &ActionHandle) -> Option<String> {
    match sig.resolve_context_path(path) {
        super::schema_info::PathResolution::Resolved(ty) => Some(ty),
        _ => None,
    }
}

/// Type of a `principal` / `resource` scope term. A bare root types to the
/// scoped action's principal / resource entity type; an attribute tail
/// (`principal.dept`) is left untyped (the coarse projection carries no entity
/// attribute types — attribute paths resolve at eval time, matching the
/// provider-arg surface).
/// The rule's per-axis scope narrowing, threaded to wherever a scope path resolves.
#[derive(Clone, Copy, Default)]
pub(crate) struct ScopeNarrowing<'a> {
    pub principal: Option<&'a crate::api::ScopeConstraint>,
    pub resource: Option<&'a crate::api::ScopeConstraint>,
}

impl<'a> ScopeNarrowing<'a> {
    fn for_root(&self, root: &str) -> Option<&'a crate::api::ScopeConstraint> {
        match root {
            "principal" => self.principal,
            "resource" => self.resource,
            _ => None,
        }
    }
}

fn scope_field_type(
    path: &[String],
    rule_sig: Option<&ActionHandle>,
    narrow: ScopeNarrowing<'_>,
) -> Option<String> {
    let sig = rule_sig?;
    match path {
        // Narrowed by the rule's scope: `principal is W::Staff` under a multi-type
        // action leaves one candidate, so the root types tagged rather than untagged.
        [root] if root == "principal" => sig.principal_type_narrowed(narrow.principal),
        [root] if root == "resource" => sig.resource_type_narrowed(narrow.resource),
        // An attribute tail resolves against the scope entity's declared
        // attributes. Typing this is what makes a comparison against a scope
        // attribute checkable at all: `check_types` skips any comparison with an
        // untyped side, so while this returned `None` a mis-typed comparison
        // against `principal.<attr>` validated cleanly and then silently never
        // matched at runtime — and for an aggregation summand it did worse than
        // never match, since `sum` skips a non-integer value while `count`
        // counts it, so a `forbid` cap could never fire.
        [root, tail @ ..] if !tail.is_empty() && (root == "principal" || root == "resource") => {
            sig.scope_attribute_type(root, tail, narrow.for_root(root))
        }
        _ => None,
    }
}

/// The simple (last-segment) name of a possibly-qualified type name.
fn simple_name(qualified: &str) -> &str {
    qualified
        .rsplit_once("::")
        .map(|(_, r)| r)
        .unwrap_or(qualified)
}

/// Classify an array literal's element type: empty is bare `array`,
/// homogeneous is `array<T>`, heterogeneous or unclassifiable is `array<?>`.
fn array_literal_type(elems: &[Term]) -> String {
    if elems.is_empty() {
        return "array".to_string();
    }
    let empty = BTreeMap::new();
    // No action signature in hand here, so no scope path can type anyway.
    let mut tys = elems
        .iter()
        .map(|e| term_type(e, &empty, None, ScopeNarrowing::default()));
    let Some(Some(first)) = tys.next() else {
        return "array<?>".to_string();
    };
    if elems
        .iter()
        .any(|e| term_type(e, &empty, None, ScopeNarrowing::default()).is_none())
    {
        return "array<?>".to_string();
    }
    if tys
        .flatten()
        .all(|t| t == first || (is_numeric(&t) && is_numeric(&first)))
    {
        format!("array<{first}>")
    } else {
        "array<?>".to_string()
    }
}

fn is_numeric(t: &str) -> bool {
    t == "int"
}

fn array_element(t: &str) -> Option<&str> {
    t.strip_prefix("array<").and_then(|r| r.strip_suffix('>'))
}

fn split_entity(t: &str) -> (&str, Option<&str>) {
    match t.split_once(':') {
        Some(("entity", tag)) => ("entity", Some(tag)),
        _ => (t, None),
    }
}

/// Is `actual` acceptable where `expected` is declared? Equal types and a
/// `null` actual always pass; entities accept an untagged side or equal
/// tags (no ancestor closure is modeled); arrays match element-wise; a
/// bare `array` pairs with any `array<T>`.
fn param_accepts(expected: &str, actual: &str) -> bool {
    if expected == actual || actual == "null" {
        return true;
    }
    // UNLIKE `types_compatible`, a field pattern DOES require equal entity tags. The
    // expected type here comes from a DECLARED field, which has exactly one entity type,
    // so no multi-typed operand can arise on this path and rejecting restricts nothing
    // legitimate. (An earlier comment here claimed the opposite; the relaxation it
    // described was reverted — see the commit that restored this branch.)
    //
    // KNOWN FAIL-OPEN GAP: `_ => true` accepts an UNTAGGED side unconditionally, so a
    // pattern binding a `Manager`-declared field to a bare `principal` is accepted
    // whenever the action permits several principal types and the root therefore types as
    // plain `entity`. Cedar flags its analogue at every arity. Two of the three producers
    // of untagged `entity` are genuinely UNKNOWN types (`schema_info.rs:507`, `:509` —
    // no type info, and Cedar's `AnyEntity`) where accepting is correct; only the
    // multi-type scope root at `schema_info.rs:142` discards a known candidate set.
    //
    // Closing it is NOT a per-action disjointness test, which is the tempting shape since
    // `check_types_for_action` already runs per action. Measured, Cedar makes no complaint
    // when a comparison is dead under one reached action and live under another
    // (`err=0 warn=0`), and warns only when it is dead under every reached action
    // (`err=0 warn=1`). A per-action check would reject the first shape. The rule must
    // therefore test the UNION of candidates across all reached actions, which needs a
    // cross-action conjunction this function cannot express from two strings.
    let (eb, et) = split_entity(expected);
    let (ab, at) = split_entity(actual);
    if eb == "entity" && ab == "entity" {
        return match (et, at) {
            (Some(x), Some(y)) => x == y,
            _ => true,
        };
    }
    if let (Some(e), Some(a)) = (array_element(expected), array_element(actual)) {
        if e == "?" || a == "?" {
            return false;
        }
        return param_accepts(e, a);
    }
    (expected == "array" && actual.starts_with("array<"))
        || (actual == "array" && expected.starts_with("array<"))
}

/// Are two operand types comparable with `==`? Symmetric variant of
/// [`param_accepts`] with numeric widening.
fn types_compatible(a: &str, b: &str) -> bool {
    if a == b || a == "null" || b == "null" || (is_numeric(a) && is_numeric(b)) {
        return true;
    }
    // Two ENTITY operands are comparable whatever their entity types. Comparing
    // differently-typed entities is well-typed: always false, its negation always true.
    // Cedar agrees, and so do all three engines at run time (see
    // `tests/entity_equality_verdicts.rs` and the compiler's differential).
    //
    // Not an error here, because an operand may be MULTI-TYPED and a comparison against
    // one of its possible types is the discriminating idiom —
    // `a == Ns::T1::"x" || a == Ns::T2::"y"` — where each disjunct is wrong only in
    // isolation. The dialect has no `||` yet, but a condition or macro reused across
    // actions via `action in [...]` reaches the same shape today.
    //
    // The right end state is a WARNING, matching Cedar's `policy is impossible`. Cedar
    // cannot supply one here — the leaf is an opaque `context.<id>` boolean its
    // typechecker never enters — so this is SILENT for now, deliberately: erroring would
    // cement a restriction that a future temporal impossibility analysis should lift, and
    // that analysis is the place for this diagnostic.
    //
    // Field patterns are NOT relaxed. `param_accepts` receives its expected type from a
    // DECLARED field, which has exactly one entity type, so no multi-typed operand can
    // arise there and rejecting restricts nothing legitimate.
    let (ab, _) = split_entity(a);
    let (bb, _) = split_entity(b);
    if ab == "entity" && bb == "entity" {
        return true;
    }
    if let (Some(ae), Some(be)) = (array_element(a), array_element(b)) {
        if ae == "?" || be == "?" {
            return false;
        }
        return types_compatible(ae, be);
    }
    (a == "array" && b.starts_with("array<")) || (b == "array" && a.starts_with("array<"))
}

/// User-facing rendering: strip the `entity:` tag prefix and show
/// `array<?>` as "mixed-type array".
fn display_type(ty: &str) -> String {
    if ty == "array<?>" {
        return "mixed-type array".to_string();
    }
    if let Some(inner) = array_element(ty) {
        return format!("array<{}>", display_type(inner));
    }
    match ty.split_once(':') {
        Some(("entity", tag)) => tag.to_string(),
        _ => ty.to_string(),
    }
}

// ─── Time-point dependence ──────────────────────────────────────────
//
// A subexpression is *tp-dependent* if its value can vary between
// timepoints that share the same `context`. Atoms that vary per
// timepoint are predicate matches and `tp(_)`; everything else builds
// up from those plus tp-independent terms (`context.*`, literals). A
// monitoring scope (temporal operator, since side, aggregation body /
// result, and each top-level conjunct) is degenerate — and rejected —
// if its immediate body is not tp-dependent. Re-bound to the native AST.

fn check_tp_dependence(c: &Condition, errs: &mut Vec<LeafError>) {
    let mut env: BTreeSet<String> = BTreeSet::new();
    collect_rule_wide_tp_binders(c, &mut env);
    for conj in conjuncts(c) {
        if !is_tp_dep(conj, &env, errs) {
            errs.push(LeafError {
                message: "this `when`/`unless` conjunct does not vary with the current \
                          timepoint; it monitors nothing"
                    .to_string(),
                span: Some(conj.span),
            });
        }
    }
}

/// Flatten the top-level `&&` chain into its conjuncts. Any other node
/// (a `!` negation, a temporal operator, …) is itself one conjunct.
fn conjuncts(c: &Condition) -> Vec<&Condition> {
    let mut out = Vec::new();
    fn rec<'a>(c: &'a Condition, out: &mut Vec<&'a Condition>) {
        if let ConditionKind::And { left, right } = &c.kind {
            rec(left, out);
            rec(right, out);
        } else {
            out.push(c);
        }
    }
    rec(c, &mut out);
    out
}

fn is_tp_dep(c: &Condition, env: &BTreeSet<String>, errs: &mut Vec<LeafError>) -> bool {
    match &c.kind {
        // A predicate match / `tp` binds to an event at the current
        // timepoint — tp-dependent by construction.
        ConditionKind::Predicate(_) | ConditionKind::Tp { .. } => true,

        ConditionKind::Comparison { left, right, .. } => {
            // An aggregate operand's `where` body must itself be
            // tp-dependent (a degenerate body monitors nothing); check each.
            for operand in [left, right] {
                if let Term::Agg(agg) = operand {
                    check_agg_tp_dependence(agg, env, errs);
                }
            }
            term_is_tp_dep(left, env) || term_is_tp_dep(right, env)
        }

        // `!a` varies with the timepoint iff `a` does.
        ConditionKind::Not { inner } => is_tp_dep(inner, env, errs),

        ConditionKind::And { left, right } => {
            let ld = is_tp_dep(left, env, errs);
            let rd = is_tp_dep(right, env, errs);
            ld || rd
        }

        // Internal-only disjunction (pin-relativization): a disjunction
        // varies with the timepoint only when *both* branches do — a
        // timepoint-constant branch would make the whole disjunction hold
        // (or fail) uniformly whenever that branch does, degenerating the
        // monitoring scope. (The rewrite only emits predicate branches,
        // which are tp-dependent by construction; this is defensive.)
        ConditionKind::Or { left, right } => {
            let ld = is_tp_dep(left, env, errs);
            let rd = is_tp_dep(right, env, errs);
            ld && rd
        }

        ConditionKind::Formerly { body, .. } | ConditionKind::Previous { body, .. } => {
            if !is_tp_dep(body, env, errs) {
                errs.push(degenerate(body.span, "this temporal operator's body"));
            }
            true
        }

        ConditionKind::Since { left, right, .. } => {
            if !is_tp_dep(left, env, errs) {
                errs.push(degenerate(left.span, "the left side of `since`"));
            }
            if !is_tp_dep(right, env, errs) {
                errs.push(degenerate(right.span, "the right side of `since`"));
            }
            true
        }

        ConditionKind::Exists { var, body } => {
            // `exists (x: T). φ` binds `x` over `φ`; the body must vary with
            // the timepoint (an aggregate operand inside it is checked via
            // `term_is_tp_dep`/`check_agg_tp_dependence` when the comparison
            // is walked). Add `x` to the env so a conjunct using it reads as
            // tp-dependent.
            let mut cont_env = env.clone();
            cont_env.insert(var.name().to_string());
            if !is_tp_dep(body, &cont_env, errs) {
                errs.push(degenerate(body.span, "the body of the `exists`"));
            }
            true
        }

        // A refinement is folded onto its base predicate by macro
        // expansion before validation; if one survives, its tp-dependence
        // is its base's.
        ConditionKind::Refine { base, .. } => is_tp_dep(base, env, errs),

        // An unresolved macro call / sigil is opaque to this check
        // (expansion validates the substituted form).
        ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => true,
    }
}

fn check_agg_tp_dependence(value: &AggExpr, env: &BTreeSet<String>, errs: &mut Vec<LeafError>) {
    match &value.kind {
        AggExprKind::Sum {
            bound_var, body, ..
        } => {
            let mut body_env = env.clone();
            if let BinderSlot::Name(n) = bound_var {
                body_env.insert(n.clone());
            }
            if !is_tp_dep(body, &body_env, errs) {
                errs.push(degenerate(body.span, "the `where` body of the aggregation"));
            }
        }
        AggExprKind::Count { body, .. } => {
            if !is_tp_dep(body, env, errs) {
                errs.push(degenerate(body.span, "the `where` body of the aggregation"));
            }
        }
        AggExprKind::Call(_) => {}
    }
}

fn degenerate(span: Span, what: &str) -> LeafError {
    LeafError {
        message: format!("{what} does not vary with the current timepoint; it monitors nothing"),
        span: Some(span),
    }
}

/// Names the rule binds rule-wide to tp-varying values: predicate args in
/// *positive* position that are not confined to a sub-scope. A variable
/// bound only in a negated position (inside a `!` negation, e.g. the left of
/// `!left since …`) or only inside an aggregation `for` domain (the
/// `where` body of a `sum`/`count`) does not bind for the surrounding
/// scope, so it must not be harvested here — otherwise a degenerate conjunct
/// that merely reuses that name would read as tp-dependent. The walk
/// therefore skips both negated subtrees and aggregation bodies.
fn collect_rule_wide_tp_binders(c: &Condition, out: &mut BTreeSet<String>) {
    walk_positive(c, &mut |node| {
        let ConditionKind::Predicate(p) = &node.kind else {
            return;
        };
        for na in &p.args {
            if let Term::Var(name) = &na.value {
                out.insert(name.clone());
            }
        }
    });
}

fn term_is_tp_dep(t: &Term, env: &BTreeSet<String>) -> bool {
    match t {
        Term::Var(name) => env.contains(name),
        Term::Array(items) => items.iter().any(|x| term_is_tp_dep(x, env)),
        // An aggregate is computed over the trace up to the current
        // timepoint, so its value varies with the timepoint — tp-dependent
        // by construction (like a predicate match).
        Term::Agg(_) => true,
        Term::Entity { .. }
        | Term::Integer(_)
        | Term::Decimal(_)
        | Term::String(_)
        | Term::Bool(_)
        | Term::ContextField(_)
        // A scope field (`principal.dept`) is a fixed current-request value —
        // the same at every timepoint the operator scans — so, like a context
        // field, it is not time-point dependent.
        | Term::ScopeField(_)
        | Term::Wildcard
        | Term::ParamRef(_)
        | Term::BinderRef(_) => false,
    }
}

/// Walk every node of a condition, invoking `f` on each.
fn walk(c: &Condition, f: &mut impl FnMut(&Condition)) {
    f(c);
    descend(c, f, false);
}

/// Walk only the nodes that bind for the surrounding scope: the same
/// traversal as [`walk`] except it does not descend into sub-scopes — the
/// inner of a `!` negation (including the `!left` form of `!left since …`)
/// or an aggregation body (the `where` body of a `sum`/`count`, whose
/// binders are its `for` domain). Used to collect binders that bind for the
/// surrounding scope; an occurrence confined to a sub-scope does not.
fn walk_positive(c: &Condition, f: &mut impl FnMut(&Condition)) {
    f(c);
    descend(c, f, true);
}

/// Shared descent for [`walk`] / [`walk_positive`]. When `positive_only`,
/// sub-scopes that do not bind for the surrounding scope are not entered —
/// the inner of a `!` negation and the aggregation body of a `let` — while
/// everything else (including the aggregation `in` body) is visited
/// identically.
fn descend(c: &Condition, f: &mut impl FnMut(&Condition), positive_only: bool) {
    let recurse = |g: &Condition, f: &mut _| {
        if positive_only {
            walk_positive(g, f)
        } else {
            walk(g, f)
        }
    };
    match &c.kind {
        ConditionKind::And { left, right } => {
            recurse(left, f);
            recurse(right, f);
        }
        // Internal-only disjunction: both branches are positive positions
        // (a disjunction preserves polarity), so both are descended in
        // both traversal modes.
        ConditionKind::Or { left, right } => {
            recurse(left, f);
            recurse(right, f);
        }
        ConditionKind::Not { inner } => {
            // The inner of `!` is a negated position — skip it under
            // positive-only traversal, visit it otherwise.
            if !positive_only {
                walk(inner, f);
            }
        }
        ConditionKind::Since { left, right, .. } => {
            // The negative form is `!left since …`, where the left operand
            // is itself a `Not` (handled by the arm above). Both operands
            // are descended positively here.
            recurse(left, f);
            recurse(right, f);
        }
        ConditionKind::Formerly { body, .. } | ConditionKind::Previous { body, .. } => {
            recurse(body, f);
        }
        ConditionKind::Exists { body, .. } => {
            // `exists (x). φ` binds `x` over its whole body; the body is an
            // ordinary sub-condition (no separate `for`-domain sub-scope),
            // so it is visited in both traversal modes.
            recurse(body, f);
        }
        ConditionKind::Comparison { left, right, .. } => {
            // An aggregate operand opens its own scope: its `for`-domain
            // binders bind only the `where` body, not the enclosing rule.
            // Under positive-only traversal (rule-wide binder harvesting) do
            // not descend into it, or a body-local predicate-arg var would be
            // harvested as a rule-wide binder and a sibling conjunct reusing
            // that name would falsely read as tp-dependent. The full `walk`
            // still visits the aggregate bodies so their predicates/terms are
            // checked.
            if !positive_only {
                for operand in [left, right] {
                    if let Term::Agg(agg) = operand {
                        match &agg.kind {
                            AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => {
                                recurse(body, f);
                            }
                            AggExprKind::Call(_) => {}
                        }
                    }
                }
            }
        }
        ConditionKind::Refine { base, .. } => {
            recurse(base, f);
        }
        ConditionKind::Predicate(_)
        | ConditionKind::Tp { .. }
        | ConditionKind::Call(_)
        | ConditionKind::SigilRef { .. } => {}
    }
}

/// A predicate's real namespace is its qualified path minus the trailing
/// `Action` segment the grammar requires (`App::Action::"Read"` parses to
/// namespace `["App", "Action"]`, action `"Read"`).
fn predicate_namespace(p: &Predicate) -> Option<String> {
    let segs: &[String] = match p.namespace.last() {
        Some(last) if is_action_ref(last) => &p.namespace[..p.namespace.len() - 1],
        _ => &p.namespace,
    };
    if segs.is_empty() {
        None
    } else {
        Some(segs.join("::"))
    }
}

/// Validate every `within` window in the leaf. Three checks, per operator
/// (`formerly` / `previous` / `since`), each located at the operator's node:
///
///   1. **Positive** — the window amount must be `> 0`. The grammar admits a
///      leading `-` and a zero amount, but a non-positive window makes the
///      closed-window test unsatisfiable, so a guard built on it matches
///      *nothing* — silently neutralizing a `forbid` (a fail-open). Reject it.
///   2. **In range** — `amount * unit.seconds()` must not overflow i64.
///      An overflowing window would (with saturating `seconds()`) mean
///      "effectively unbounded" and, worse, could evade the cap check below;
///      reject it explicitly rather than let it saturate silently.
///   3. **Within the cap** — the window must be `<=` the event schema's
///      `max_window`.
///
/// The whole condition tree is walked, so a `within` nested inside an
/// aggregation `where` body is checked too. Post-expansion every window is
/// [`WithinSpec::Concrete`]; a residual `ParamRef` (only possible on an
/// unexpanded macro body) is skipped.
fn check_windows(c: &Condition, max_window: Interval) -> Vec<LeafError> {
    // The cap itself is schema-supplied and already validated (`max_window`
    // parsing rejects a zero window); `seconds()` saturates, so this is safe.
    let cap = max_window.seconds();
    let mut errs = Vec::new();
    walk(c, &mut |node| {
        let within = match &node.kind {
            ConditionKind::Formerly { within, .. }
            | ConditionKind::Previous { within, .. }
            | ConditionKind::Since { within, .. } => within,
            _ => return,
        };
        let WithinSpec::Concrete(interval) = within else {
            return;
        };
        // 1. Non-positive window → unsatisfiable → fail-open guard.
        if interval.amount <= 0 {
            errs.push(LeafError {
                message: format!(
                    "temporal window `{}` must be positive; a zero or negative window \
                     matches no events, silently disabling this guard",
                    interval.render(),
                ),
                span: Some(node.span),
            });
            return;
        }
        // 2. Overflowing window → reject rather than saturate silently.
        let Some(secs) = interval.checked_seconds() else {
            errs.push(LeafError {
                message: format!(
                    "temporal window `{}` is too large; its length in seconds overflows \
                     a 64-bit integer. Use a smaller window.",
                    interval.render(),
                ),
                span: Some(node.span),
            });
            return;
        };
        // 3. Over the cap.
        if secs > cap {
            errs.push(LeafError {
                message: format!(
                    "temporal window `{}` exceeds the maximum allowed window `{}` \
                     set by the event schema's `max_window`; shorten this window to \
                     at most `{}`, or raise `max_window` in the event schema",
                    interval.render(),
                    max_window.render(),
                    max_window.render(),
                ),
                span: Some(node.span),
            });
        }
    });
    errs
}

fn check_entity_types(c: &Condition, info: &SchemaInfo, errs: &mut Vec<LeafError>) {
    walk(c, &mut |node| {
        let node_span = node.span;
        for_each_term(node, &mut |t| {
            if let Term::Entity { ty, id } = t {
                let (ns_opt, simple) = split_qualified(ty);
                // An action UID (`Ns::Action::"X"`) parses to a
                // `Term::Entity` whose last qualified segment is `Action`.
                // Cedar reserves `Action` as an entity-type name, so it can
                // never be a *declared* entity type; the lookup below would
                // only ever emit a spurious "unknown entity type" for it
                // (the hoisted leaf is not seen by Cedar's validator). Skip.
                if is_action_ref(ty) {
                    return;
                }
                match info.entity_type(ns_opt.as_deref(), simple) {
                    Some(entry) => {
                        if let Some(eids) = entry.enum_eids()
                            && !eids.iter().any(|e| e == id)
                        {
                            errs.push(LeafError {
                                message: format!(
                                    "`{ty}` is an enum entity type; `\"{id}\"` is not one of its \
                                     permitted ids ({})",
                                    enum_choices(&eids)
                                ),
                                span: Some(node_span),
                            });
                        }
                    }
                    None => errs.push(LeafError {
                        message: format!(
                            "unknown entity type `{ty}`; {}",
                            known_entities_help(info)
                        ),
                        span: Some(node_span),
                    }),
                }
            }
        });
    });
}

fn check_context_fields(
    c: &Condition,
    info: &SchemaInfo,
    target_actions: &[crate::api::ActionRef],
    narrow: ScopeNarrowing<'_>,
    errs: &mut Vec<LeafError>,
) {
    // A hoisted leaf attaches to every action its scope RESOLVES to, which is not
    // the same as the actions it names: `action in [Group]` resolves to the group's
    // transitive members, because that is what Cedar validates the policy against.
    // Resolving against the group itself would read a context record it does not
    // have (a pure group declares no `appliesTo`).
    //
    // `target_actions` is that resolved set, computed once during lowering by the
    // same expansion the schema augmentation grafts the hoisted field with — so
    // validation cannot disagree with augmentation about where the field lives.
    //
    // Resolve each `context.<path>` against every such action's context record: a
    // field must be declared on all of them, since the leaf is evaluated for each.
    // An unconstrained `action` scope resolves to every action.
    for action in target_actions {
        let Some(sig) = info.action(action.namespace.as_deref(), &action.id) else {
            // A pinned action isn't in the projection; Cedar's own validator
            // owns the unknown-action diagnostic.
            continue;
        };
        // Skip an action for which the rule's principal/resource scope admits no
        // request environment: the rule can never be evaluated on it, so its context
        // record must not be held against the condition. See `admits_any_env`.
        if !sig.admits_any_env(narrow.principal, narrow.resource) {
            continue;
        }
        walk(c, &mut |node| {
            let node_span = node.span;
            for_each_term(node, &mut |t| {
                // A bare `principal` / `resource` root and its `.id` / `.type`
                // projections always resolve, so they need no check. An ATTRIBUTE
                // tail does: the entity's declared attributes say whether it
                // exists and what it is, so an unresolvable tail is a policy that
                // can never match rather than one deferred to eval time. Leaving
                // it unchecked is fail-open — silent for most comparisons, and for
                // an aggregation summand worse, since `sum` skips a non-integer
                // value while `count` counts it, so a `forbid` cap could never
                // fire.
                match t {
                    Term::ContextField(path) => check_one_context_path(path, &sig, node_span, errs),
                    Term::ScopeField(path) => {
                        check_one_scope_path(path, &sig, narrow, node_span, errs)
                    }
                    _ => {}
                }
            });
        });
    }
}

/// Check a `context.<path>` against the scoped action's **full** declared
/// context record (Cedar's `context` variable). Any declared context field —
/// `input`, `system`, `output`, or one literally named `principal` — resolves;
/// an undeclared head or a bad nested segment is an error. (This is the Cedar
/// model: `context.principal` is a plain field access, valid iff `principal` is
/// a declared context field; the request scope is reached via the bare
/// `principal` / `resource` roots, which need no static check here — see the
/// `Term::ScopeField` note at the call site.)
fn check_one_context_path(
    path: &[String],
    sig: &ActionHandle,
    node_span: Span,
    errs: &mut Vec<LeafError>,
) {
    let Some(head) = path.first() else { return };
    use super::schema_info::PathResolution;
    match sig.resolve_context_path(path) {
        PathResolution::Resolved(_) => {}
        PathResolution::HeadMissing => errs.push(LeafError {
            message: format!(
                "action `{}` has no context field `{head}` for `context.{head}`",
                sig.predicate_ref()
            ),
            span: Some(node_span),
        }),
        PathResolution::NestedMissing(seg) => errs.push(LeafError {
            message: format!(
                "record has no field `{seg}` in `context.{}` path",
                path.join(".")
            ),
            span: Some(node_span),
        }),
        PathResolution::NonRecord(seg) => errs.push(LeafError {
            message: format!("`{seg}` accesses a field of a non-record type"),
            span: Some(node_span),
        }),
    }
}

/// Check a `principal.<path>` / `resource.<path>` attribute tail against the
/// declared attributes of every entity type the scope permits.
///
/// A bare root always resolves and never reaches here. A `.id` / `.type` projection
/// resolves too — as a string, so a comparison against one is type-checked like any
/// other rather than waved through. Rejecting an
/// unresolvable tail rather than ignoring it is the point: the comparison it feeds
/// can never match, so the condition is permanently false, and a permanently false
/// `forbid` is a cap that never fires.
fn check_one_scope_path(
    path: &[String],
    sig: &ActionHandle,
    narrow: ScopeNarrowing<'_>,
    node_span: Span,
    errs: &mut Vec<LeafError>,
) {
    let [root, tail @ ..] = path else { return };
    if tail.is_empty() || !(root == "principal" || root == "resource") {
        return;
    }
    let rendered = format!("{root}.{}", tail.join("."));
    use super::schema_info::ScopePath;
    match sig.resolve_scope_path(root, tail, narrow.for_root(root)) {
        ScopePath::Resolved(_) | ScopePath::Unknown => {}
        ScopePath::Missing { entities, segment } => errs.push(LeafError {
            message: format!(
                "`{rendered}` does not resolve for every entity the rule's `{root}` may \
                 be: `{}` declares no attribute `{segment}`, so for those requests the \
                 comparison can never match and the condition is permanently false. \
                 Narrow the rule's scope (`{root} is <type>`) if only some types are \
                 meant.",
                entities.join("`, `")
            ),
            span: Some(node_span),
        }),
        ScopePath::NonRecord { segment } => errs.push(LeafError {
            message: format!("`{segment}` accesses a field of a non-record type in `{rendered}`"),
            span: Some(node_span),
        }),
        ScopePath::Ambiguous { types } => errs.push(LeafError {
            message: format!(
                "`{rendered}` has a different type on each entity the action's \
                 `{root}` may be (`{}`), so the condition cannot be checked against \
                 one type; it is evaluated whichever entity the request carries",
                types.join("`, `")
            ),
            span: Some(node_span),
        }),
    }
}

/// Visit every [`Term`] directly carried by a condition node (predicate
/// args, comparison operands). Nested terms inside arrays are visited too.
fn for_each_term(node: &Condition, f: &mut impl FnMut(&Term)) {
    let mut visit = |t: &Term| visit_term(t, f);
    match &node.kind {
        ConditionKind::Predicate(p) => {
            for a in &p.args {
                visit(&a.value);
            }
        }
        ConditionKind::Comparison { left, right, .. } => {
            visit(left);
            visit(right);
        }
        _ => {}
    }
}

fn visit_term(t: &Term, f: &mut impl FnMut(&Term)) {
    f(t);
    if let Term::Array(items) = t {
        for it in items {
            visit_term(it, f);
        }
    }
}

/// Split a qualified entity type path `A::B::Type` into `(Some("A::B"),
/// "Type")`, or `(None, "Type")` for a bare name.
/// Whether a qualified type name denotes an action reference: its last
/// `::`-segment is the reserved `Action` type the grammar requires on an
/// action UID (`Ns::Action::"X"`). Cedar reserves `Action` as an entity-type
/// name, so this never collides with a declared entity type.
fn is_action_ref(ty: &str) -> bool {
    split_qualified(ty).1 == "Action"
}

fn split_qualified(qualified: &str) -> (Option<String>, &str) {
    match qualified.rsplit_once("::") {
        Some((left, right)) => (Some(left.to_string()), right),
        None => (None, qualified),
    }
}

fn enum_choices(eids: &[String]) -> String {
    if eids.is_empty() {
        "(none)".to_string()
    } else {
        eids.iter()
            .map(|e| format!("\"{e}\""))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn known_entities_help(info: &SchemaInfo) -> String {
    let known = info.known_entity_refs();
    if known.is_empty() {
        "the schema declares no entity types".to_string()
    } else {
        format!("known entity types: {}", known.join(", "))
    }
}
