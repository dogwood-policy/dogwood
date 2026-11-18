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
    TimeUnit, WithinSpec,
};
use super::schema_info::{
    ActionHandle, ArrayElem, PathResolution, RichType, SchemaInfo, UNSUPPORTED_EXTENSION,
};
use crate::conformance::CType;
use crate::error::{Span, ValidationError};
use crate::event_schema::derive::DerivedEventSchema;
use cedar_policy_core::ast::EntityType;

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
    events: Option<&DerivedEventSchema>,
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
    check_wildcard_operands(&leaf.condition, &mut errs);
    check_entity_types(&leaf.condition, info, &mut errs);
    check_decimal_literals(&leaf.condition, &mut errs);
    check_context_fields(&leaf.condition, info, target_actions, narrow, &mut errs);
    check_tp_dependence(&leaf.condition, &mut errs);
    check_types(&leaf.condition, info, events, target_actions, narrow, &mut errs);
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
        let max_horizon = ctx.event_schema.max_horizon();
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
            for e in check_windows(&field.condition.condition, max_window, max_horizon) {
                findings.push(TemporalFinding {
                    message: e.message,
                    span: match e.span {
                        Some(s) => s.rebased(base),
                        None => field.condition.span,
                    },
                });
            }

            // Horizon check: how far back the leaf looks in total — the largest
            // sum of the windows along one chain of operators — must be at
            // most the event schema's `max_horizon`, when it declares one, so
            // that no event older than `max_horizon` can matter to an accepted
            // policy.
            if let Some(message) = max_horizon
                .and_then(|cap| check_horizon(&field.condition.condition, cap))
            {
                findings.push(TemporalFinding {
                    message,
                    span: field.condition.span,
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
            let facts = ctx
                .leaf_facts
                .get(&field.id)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            let errors = validate_leaf(
                &field.condition,
                &info,
                Some(ctx.event_schema),
                &field.target_actions,
                narrow,
            )
                .into_iter()
                .chain(super::validity::check_leaf(
                    field,
                    &info,
                    ctx.event_schema,
                    facts,
                ));
            for e in errors {
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
    if message.contains("exceeds the maximum allowed window") && message.contains("`max_horizon`") {
        return Some(
            "when the event schema declares `max_horizon`, `max_window` defaults to it \
             and may not exceed it, so a longer window needs a larger `max_horizon`"
                .to_string(),
        );
    }
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
// fields plus every binder's **declared** type, where the binder is in scope
// (`walk_typed`) — each `exists (x: T)` and aggregation `for (v: T)` carries a
// mandatory annotation, so a bound variable's type is read from its
// declaration, never reverse-inferred from a use site. The condition is then
// walked to report mismatched
// comparison operands and predicate arguments; because a bound variable's
// env entry is its declared type, those same checks enforce that every use
// *respects the annotation* (e.g. `exists (x: Long). … x == "s"` is now a
// type error, not silently reconciled). Types are values of
// [`super::schema_info::RichType`] (`Long`, `String`, `Decimal`,
// `Extension(..)` for a `datetime` / `duration` / `ipaddr` path, which no
// temporal term may have (`check_unsupported_operand`), `Bool`,
// `Timepoint`, `Entity(..)`, `Array(..)`, `Record`), compared via its
// `accepts` / `compatible` / `is_numeric` methods.
// Type inference for temporal terms, re-bound to the native AST.
// Entity subtyping is not modeled (the projection carries no ancestor
// closure), so an entity compares with an entity of its own type; two entities
// of different types compare only by an equality that binds no variable.

/// One request environment a rule decides: an action its scope resolves to,
/// and a principal type and a resource type the action admits and the rule's
/// scope narrows to. Cedar validates a policy once per such environment, and
/// so do the type checks: in each, `principal` and `resource` have one entity
/// type, and their attributes the types that entity type declares.
#[derive(Clone, Copy)]
struct RequestEnv<'e> {
    sig: &'e ActionHandle<'e>,
    principal: &'e EntityType,
    resource: &'e EntityType,
}

fn check_types(
    c: &Condition,
    info: &SchemaInfo,
    events: Option<&DerivedEventSchema>,
    target_actions: &[crate::api::ActionRef],
    narrow: ScopeNarrowing<'_>,
    errs: &mut Vec<LeafError>,
) {
    // The condition is checked once per request environment its rule decides:
    // every action its scope resolves to — the same set `check_context_fields`
    // resolves paths against — and every principal and resource type the action
    // admits and the scope narrows to. A field may be typed differently by two
    // of them (`amount` a `Long` on one action and a `String` on another), and
    // the leaf is evaluated for each, so a comparison wrong for ANY of them is
    // wrong: this mirrors Cedar, which validates a policy in every request
    // environment its scope admits and fails if the body fails in one. Typing
    // once per action instead, with a scope root of several types as an untagged
    // entity, let `principal` stand for an entity of a type the comparison or
    // field cannot hold.
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
    // The same finding is reported once however many environments produce it, so
    // a wide scope does not multiply one mistake into one error per environment.
    let mut seen: std::collections::BTreeSet<(String, Option<usize>)> = Default::default();
    for action in target_actions {
        // An action the projection lacks is one lowering could not graft onto;
        // Cedar's own validator owns the unknown-action diagnostic.
        let Some(sig) = info.action(action.namespace.as_deref(), &action.id) else {
            continue;
        };
        // An environment the rule's principal/resource scope does not admit is one
        // the rule is never evaluated in, so holding its types against the
        // condition would be a false rejection. Cedar filters whole triples.
        let principals = sig.admitted_types("principal", narrow.principal);
        let resources = sig.admitted_types("resource", narrow.resource);
        for &principal in &principals {
            for &resource in &resources {
                let req = RequestEnv {
                    sig: &sig,
                    principal,
                    resource,
                };
                let mut per_env = Vec::new();
                check_types_in_env(c, info, events, req, &mut per_env);
                for e in per_env {
                    if seen.insert((e.message.clone(), e.span.map(|s| s.start))) {
                        errs.push(e);
                    }
                }
            }
        }
    }
}

fn check_types_in_env(
    c: &Condition,
    info: &SchemaInfo,
    events: Option<&DerivedEventSchema>,
    req: RequestEnv<'_>,
    errs: &mut Vec<LeafError>,
) {
    let mut env = build_type_env(info, Some(req.sig));

    walk_typed(c, info.validator_schema(), &mut env, &mut |node, env| match &node.kind {
        ConditionKind::Predicate(p) => check_predicate_args(p, info, events, env, req, errs),
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
                && *ty != RichType::Timepoint
            {
                errs.push(LeafError {
                    message: format!(
                        "`tp({name})` binds `{name}` to the current timepoint, \
                         but `{name}` is declared `{}`; a `tp` variable must be \
                         declared `Timepoint`",
                        ty.display()
                    ),
                    span: Some(node.span),
                });
            }
        }
        ConditionKind::Comparison { op, left, right } => {
            for operand in [left, right] {
                if matches!(operand, Term::Arith { .. }) {
                    check_arith_atoms(operand, env, req, node.span, errs);
                }
            }
            let (lt, rt) = (
                term_type(left, env, Some(req)),
                term_type(right, env, Some(req)),
            );
            // `|`, not `||`: each unsupported operand is reported.
            let unsupported = check_unsupported_operand(left, lt.as_ref(), node.span, errs)
                | check_unsupported_operand(right, rt.as_ref(), node.span, errs);
            if unsupported {
                // The comparison is not typed further: the operand's finding
                // stands for it, as in the specification (`Term.check?`).
            } else if let (Some(l), Some(r)) = (lt, rt) {
                let numeric = matches!(op, CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge);
                // An `==` or `!=` with a bare variable on one side and a term that
                // is not a variable and holds no wildcard on the other (`x == t`,
                // the shape of an equality that can bind `x`) needs equal types.
                // The test is syntactic, like the specification's (`eqRestricted?`,
                // `EqCompatible`): it applies whether or not `x` is already bound.
                let binding = super::check::eq_restricted_var(left, right).is_some();
                if numeric && !(l.is_numeric() && r.is_numeric()) {
                    errs.push(LeafError {
                        message: format!(
                            "comparison requires numeric operands on both sides, got `{}` and `{}`",
                            l.display(),
                            r.display()
                        ),
                        span: Some(node.span),
                    });
                } else if !numeric && !l.compatible(&r, binding) {
                    errs.push(LeafError {
                        message: format!(
                            "equality requires both sides to have the same type, got `{}` and `{}`",
                            l.display(),
                            r.display()
                        ),
                        span: Some(node.span),
                    });
                }
            }
        }
        _ => {}
    });
}

/// Type a predicate's arguments against the fields of its event. A field of the
/// spliced `input` / `output` group has the type the predicate action's context
/// declares at its path; any other field (`callerPrincipal`, `requestId`, …)
/// the type the event schema declares. A variable argument of such a field is
/// typed by `validity::check_binding_fields`, and a wildcard matches anything.
fn check_predicate_args(
    p: &Predicate,
    info: &SchemaInfo,
    events: Option<&DerivedEventSchema>,
    env: &BTreeMap<String, RichType>,
    req: RequestEnv<'_>,
    errs: &mut Vec<LeafError>,
) {
    let ns = predicate_namespace(p);
    let pred_sig = info.action(ns.as_deref(), &p.action);
    let fields = events
        .and_then(|e| e.get(&p.namespace, &p.action, &p.kind))
        .map(|event| crate::conformance::event_fields(event, info.validator_schema()))
        .unwrap_or_default();
    for na in &p.args {
        // Resolve the predicate field's declared type by its FULL dotted path
        // (`input.mode`, `output.status`) — the same walk the comparison path
        // uses for `context.input.mode`. A flat lookup of the whole dotted
        // string never matched, so field-pattern arguments used to go entirely
        // un-type-checked and a mis-typed literal validated cleanly (then
        // silently never matched a real event at runtime).
        let path = na.field_path();
        // A variable, a wildcard and a macro slot are not request-side paths, so
        // `check_unsupported_operand` reports nothing for them.
        if check_unsupported_operand(
            &na.value,
            term_type(&na.value, env, Some(req)).as_ref(),
            p.span,
            errs,
        ) {
            continue;
        }
        let spliced = matches!(path.first().map(String::as_str), Some("input" | "output"));
        if spliced
            && let Some(expected) = pred_sig
                .as_ref()
                .and_then(|sig| predicate_field_type(&path, sig))
        {
            check_arg_type(&na.value, &expected, &p.action, &na.name, env, req, p.span, errs);
            continue;
        }
        if matches!(
            na.value,
            Term::Var(_) | Term::Wildcard | Term::ParamRef(_) | Term::BinderRef(_)
        ) {
            continue;
        }
        let Some((_, field_ty, _)) = fields.iter().find(|(f, _, _)| *f == path) else {
            continue;
        };
        let Some(got) = term_type(&na.value, env, Some(req)) else {
            continue;
        };
        let held = rich_ctype(&got)
            .is_some_and(|value| super::validity::accepts(field_ty, &value));
        if !held {
            let action = cedar_policy_core::ast::Eid::new(p.action.as_str()).escaped();
            errs.push(LeafError {
                message: format!(
                    "argument `{}` of `{action}` expects `{}` but got `{}`",
                    na.name,
                    field_ty.render(),
                    got.display()
                ),
                span: Some(p.span),
            });
        }
    }
}

/// The value type a rich type names, in the event schema's vocabulary: `None`
/// for a timepoint, which no field holds, and for an array literal's
/// unclassified element.
fn rich_ctype(t: &RichType) -> Option<CType> {
    Some(match t {
        RichType::Long => CType::Long,
        RichType::String => CType::String,
        RichType::Bool => CType::Bool,
        RichType::Decimal => CType::Decimal,
        RichType::Extension(name) => CType::Extension(name.clone()),
        RichType::Array(ArrayElem::Of(inner)) => CType::Set(Box::new(rich_ctype(inner)?)),
        RichType::Array(_) | RichType::Timepoint => return None,
        RichType::Record(attrs) => CType::Record {
            attrs: attrs
                .iter()
                .map(|(name, required, ty)| Some((name.clone(), (rich_ctype(ty)?, *required))))
                .collect::<Option<_>>()?,
            open: false,
        },
        RichType::Entity(Some(name)) => CType::Entity(vec![name.clone()]),
        RichType::Entity(None) => CType::AnyEntity,
        RichType::Never => CType::Never,
    })
}

/// Report a request-side path whose type is, or holds, one of Cedar's
/// extension types other than `decimal` (`datetime`, `duration`, `ipaddr`):
/// temporal conditions do not support them, as a comparison operand, an atom
/// of one, or a predicate argument (the specification's
/// `CedarType.temporalSupported`). Whether it reported one.
fn check_unsupported_operand(
    t: &Term,
    ty: Option<&RichType>,
    span: Span,
    errs: &mut Vec<LeafError>,
) -> bool {
    let Some(ty) = ty.filter(|ty| ty.holds_unsupported_extension()) else {
        return false;
    };
    let path = match t {
        Term::ContextField(p) => crate::field_path::join_under("context", p),
        Term::ScopeField(p) => crate::field_path::join(p),
        _ => return false,
    };
    errs.push(LeafError {
        message: format!(
            "`{path}` has the type `{}`; {UNSUPPORTED_EXTENSION}",
            ty.display()
        ),
        span: Some(span),
    });
    true
}

/// The all-`Long` atom rule for a compound arithmetic operand: every leaf
/// must type as `Long`. Decimals stay equality-only; strings, booleans,
/// entities, and arrays cannot be operated on; a wildcard is unresolvable
/// (a silently-false guard). A macro sigil leaf is opaque, and an
/// unresolvable variable is owned by the closedness check.
fn check_arith_atoms(
    t: &Term,
    env: &BTreeMap<String, RichType>,
    req: RequestEnv<'_>,
    span: Span,
    errs: &mut Vec<LeafError>,
) {
    match t {
        Term::Arith { left, right, .. } => {
            check_arith_atoms(left, env, req, span, errs);
            check_arith_atoms(right, env, req, span, errs);
        }
        Term::Wildcard => errs.push(LeafError {
            message: "a wildcard (`*` / `_`) cannot appear inside an arithmetic \
                      expression; it resolves to no value, so the whole guard \
                      would be silently false"
                .to_string(),
            span: Some(span),
        }),
        Term::ParamRef(_) | Term::BinderRef(_) => {}
        atom => match term_type(atom, env, Some(req)) {
            Some(RichType::Long) | None => {}
            Some(other) if check_unsupported_operand(atom, Some(&other), span, errs) => {}
            Some(other) => errs.push(LeafError {
                message: format!(
                    "arithmetic operates only on `Long` values, but this \
                     operand has type `{}`",
                    other.display()
                ),
                span: Some(span),
            }),
        },
    }
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
            let AggExprKind::Sum {
                bound_var,
                for_vars,
                ..
            } = &agg.kind
            else {
                return;
            };
            // A summand still carrying a macro sigil has no concrete name;
            // expansion re-runs validation on the substituted form.
            let BinderSlot::Name(summand) = bound_var else {
                return;
            };
            // The summand is a binder of the aggregation's own `for` list (see
            // `check_aggregation`), which scopes over the body; only an
            // in-crate caller that skipped the parse-time check reaches the
            // fallback. An unresolved name means a sibling defect already
            // reported by that check, so skip rather than double-report.
            let own = for_vars.iter().find(|v| match &v.slot {
                BinderSlot::Name(name) => name == summand,
                _ => false,
            });
            let Some(ty) = own.map(|v| &v.ty).or_else(|| binder_types.get(summand)) else {
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
/// name: each `exists (x: T)` and every aggregation `for (v: T)` element. The
/// fallback of [`check_sum_summands`] for a summand outside its own `for`
/// list; the innermost binder wins on a name clash, a lexical approximation.
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
                operand.for_each_operand_agg(&mut |agg| match &agg.kind {
                    AggExprKind::Sum { for_vars, .. } | AggExprKind::Count { for_vars, .. } => {
                        for v in for_vars {
                            record(v, &mut map);
                        }
                    }
                    AggExprKind::Call(_) => {}
                });
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
// expected/declared types, the request environment, the variable types, and the
// span to report against); bundling them into a struct would not clarify the
// call sites.
#[allow(clippy::too_many_arguments)]
fn check_arg_type(
    arg: &Term,
    expected: &RichType,
    action: &str,
    param: &str,
    env: &BTreeMap<String, RichType>,
    req: RequestEnv<'_>,
    pred_span: Span,
    errs: &mut Vec<LeafError>,
) {
    if let Some(got) = term_type(arg, env, Some(req))
        && !expected.accepts(&got)
    {
        let action = cedar_policy_core::ast::Eid::new(action).escaped();
        errs.push(LeafError {
            message: format!(
                "argument `{param}` of `{action}` expects `{}` but got `{}`",
                expected.display(),
                got.display()
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
    _info: &SchemaInfo,
    rule_sig: Option<&ActionHandle>,
) -> BTreeMap<String, RichType> {
    let mut env = BTreeMap::new();
    // Seed the scoped action's input field names with their types (a bare
    // `field` reference in the leaf resolves to the rule action's input).
    // Every declaration-site binder then types its variable by annotation,
    // where it is in scope (`walk_typed`).
    if let Some(sig) = rule_sig {
        for name in sig.input_field_names() {
            if let Some(ty) = sig.input_field_type(&name) {
                env.insert(name, ty);
            }
        }
    }
    env
}

/// Walk every node of a condition, as [`walk`] does, with the variable types
/// in scope at the node: `env`, overridden by each enclosing binder's declared
/// type, the innermost last. A binder scopes over its own body only: an
/// `exists` over its body, and an aggregation's `for` list over its `where`
/// body. So a name that an aggregation's `for` list rebinds has its enclosing
/// type again outside the aggregation.
fn walk_typed(
    c: &Condition,
    schema: &cedar_policy_core::validator::ValidatorSchema,
    env: &mut BTreeMap<String, RichType>,
    f: &mut impl FnMut(&Condition, &BTreeMap<String, RichType>),
) {
    /// Bind `binders` in `env` for the duration of `body`. The body of an
    /// ill-formed binder list (an undeclared type, a repeated name) is not
    /// typed: the binder's finding stands for it, as in the specification.
    fn scoped(
        binders: &[super::ast::TypedBinder],
        schema: &cedar_policy_core::validator::ValidatorSchema,
        env: &mut BTreeMap<String, RichType>,
        body: &mut dyn FnMut(&mut BTreeMap<String, RichType>),
    ) {
        if !super::validity::binders_typed(binders, schema) {
            return;
        }
        let mut saved = Vec::new();
        for b in binders {
            if let BinderSlot::Name(name) = &b.slot {
                saved.push((
                    name.clone(),
                    env.insert(name.clone(), rich_type_of_annotation(&b.ty)),
                ));
            }
        }
        body(env);
        for (name, old) in saved.into_iter().rev() {
            match old {
                Some(ty) => env.insert(name, ty),
                None => env.remove(&name),
            };
        }
    }

    f(c, env);
    match &c.kind {
        ConditionKind::And { left, right }
        | ConditionKind::Or { left, right }
        | ConditionKind::Since { left, right, .. } => {
            walk_typed(left, schema, env, f);
            walk_typed(right, schema, env, f);
        }
        ConditionKind::Not { inner }
        | ConditionKind::Formerly { body: inner, .. }
        | ConditionKind::Previous { body: inner, .. } => walk_typed(inner, schema, env, f),
        ConditionKind::Exists { var, body } => {
            scoped(std::slice::from_ref(var), schema, env, &mut |env| {
                walk_typed(body, schema, env, f)
            });
        }
        ConditionKind::Comparison { left, right, .. } => {
            let mut aggs = Vec::new();
            for operand in [left, right] {
                operand.for_each_operand_agg(&mut |agg| aggs.push(agg));
            }
            for agg in aggs {
                if let AggExprKind::Sum { for_vars, body, .. }
                | AggExprKind::Count { for_vars, body } = &agg.kind
                {
                    scoped(for_vars, schema, env, &mut |env| {
                        walk_typed(body, schema, env, f)
                    });
                }
            }
        }
        ConditionKind::Refine { base, .. } => walk_typed(base, schema, env, f),
        ConditionKind::Predicate(_)
        | ConditionKind::Tp { .. }
        | ConditionKind::Call(_)
        | ConditionKind::SigilRef { .. } => {}
    }
}

/// Map a binder's declared [`Type`](super::ast::Type) annotation to the
/// "rich" type string the checks compare against. `Timepoint` is its own
/// tag (distinct from `int`, so a timepoint variable is not silently
/// comparable to an integer); a named type maps through the same vocabulary
/// as a schema field: the numeric/string/decimal/boolean scalars, or an
/// `entity:<Name>` for anything else (a declared entity type).
fn rich_type_of_annotation(ty: &super::ast::Type) -> RichType {
    use super::ast::Type;
    match ty {
        Type::Timepoint => RichType::Timepoint,
        Type::Named(path) => {
            let last = path.last().map(String::as_str).unwrap_or_default();
            match last {
                "Long" => RichType::Long,
                "String" => RichType::String,
                "Bool" | "Boolean" => RichType::Bool,
                "decimal" | "Decimal" => RichType::Decimal,
                // Any other named type is an entity type, by its qualified name
                // as written (`validity::check_binder_types` requires it to be
                // declared).
                _ => RichType::Entity(Some(path.join("::"))),
            }
        }
    }
}

/// The rich type of a term in the request environment `req`, or `None` if it
/// can't be classified (a free variable, wildcard, or an unresolved path). With
/// no environment, a request-side term has no type.
fn term_type(
    t: &Term,
    env: &BTreeMap<String, RichType>,
    req: Option<RequestEnv<'_>>,
) -> Option<RichType> {
    match t {
        Term::Var(v) => env.get(v).cloned(),
        Term::Integer(_) => Some(RichType::Long),
        Term::Decimal(_) => Some(RichType::Decimal),
        Term::String(_) => Some(RichType::String),
        Term::Bool(_) => Some(RichType::Bool),
        Term::Entity { ty, .. } => Some(RichType::Entity(Some(ty.clone()))),
        Term::Array(elems) => Some(array_literal_type(elems)),
        // Walk the action's full declared context record (via the schema
        // handle, which reads Cedar's own typed context), so `context.input.x`,
        // `context.system.now`, etc. all resolve. A `principal` / `resource`
        // head is an ordinary context field (Cedar semantics), not the scope.
        Term::ContextField(path) => match req?.sig.resolve_context_path(path) {
            PathResolution::Resolved(ty) => Some(ty),
            _ => None,
        },
        Term::ScopeField(path) => scope_field_type(path, req?),
        // An aggregate (`count`/`sum`) yields a `Long`; typed as Long so a
        // comparison against it (`(count …) == n`, `sum … > k`) checks like
        // any numeric operand.
        Term::Agg(_) => Some(RichType::Long),
        // A compound arithmetic expression is Long-valued by construction
        // (its all-Long-atoms rule is checked separately).
        Term::Arith { .. } => Some(RichType::Long),
        Term::Wildcard | Term::ParamRef(_) | Term::BinderRef(_) => None,
    }
}

/// The declared rich type of a predicate field pattern's argument, resolved by
/// its full dotted path (`input.mode`, `output.status`, `system.now`) against
/// the *predicate's* action context record. Returns `None` when the path does
/// not fully resolve (an undeclared or non-record segment), which the
/// event-schema names check already reports; a path that resolves to a group
/// rather than a leaf yields that group's record type, which `check_arg_type`
/// compares like any other.
fn predicate_field_type(path: &[String], sig: &ActionHandle) -> Option<RichType> {
    match sig.resolve_context_path(path) {
        PathResolution::Resolved(ty) => Some(ty),
        _ => None,
    }
}

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

/// Type of a `principal` / `resource` scope term in one request environment. A
/// bare root types to the environment's principal / resource entity type, and
/// an attribute tail (`.id` and `.type` included) to the type that entity type
/// declares at it.
///
/// Typing an attribute tail is what makes a comparison against a scope
/// attribute checkable at all: `check_types` skips any comparison with an
/// untyped side, so while this returned `None` a mis-typed comparison against
/// `principal.<attr>` validated cleanly and then silently never matched at
/// runtime — and for an aggregation summand it did worse than never match,
/// since `sum` skips a non-integer value while `count` counts it, so a `forbid`
/// cap could never fire.
fn scope_field_type(path: &[String], req: RequestEnv<'_>) -> Option<RichType> {
    let (root, tail) = path.split_first()?;
    let ety = match root.as_str() {
        "principal" => req.principal,
        "resource" => req.resource,
        _ => return None,
    };
    if tail.is_empty() {
        return Some(RichType::Entity(Some(ety.to_string())));
    }
    req.sig.scope_attribute_type_of(ety, tail)
}

/// Classify an array literal's element type: empty is a bare array (element
/// unknown), homogeneous is `array<T>`, heterogeneous or unclassifiable is the
/// mixed element.
fn array_literal_type(elems: &[Term]) -> RichType {
    if elems.is_empty() {
        return RichType::Array(ArrayElem::Unknown);
    }
    let empty = BTreeMap::new();
    // No action signature in hand here, so no scope path can type anyway.
    let mut tys = elems
        .iter()
        .map(|e| term_type(e, &empty, None));
    let Some(Some(first)) = tys.next() else {
        return RichType::Array(ArrayElem::Mixed);
    };
    if elems
        .iter()
        .any(|e| term_type(e, &empty, None).is_none())
    {
        return RichType::Array(ArrayElem::Mixed);
    }
    if tys
        .flatten()
        .all(|t| t == first || (t.is_numeric() && first.is_numeric()))
    {
        RichType::Array(ArrayElem::Of(Box::new(first)))
    } else {
        RichType::Array(ArrayElem::Mixed)
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
            // tp-dependent (a degenerate body monitors nothing); check each,
            // whether the aggregate is the operand or an atom of a compound
            // operand.
            for operand in [left, right] {
                operand.for_each_operand_agg(&mut |agg| check_agg_tp_dependence(agg, env, errs));
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
        // A compound expression varies with the timepoint iff one of its
        // operands does; a compound of only literals and context fields
        // stays timepoint-independent and is rejected like any other.
        Term::Arith { left, right, .. } => {
            term_is_tp_dep(left, env) || term_is_tp_dep(right, env)
        }
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
                let mut bodies = Vec::new();
                for operand in [left, right] {
                    operand.for_each_operand_agg(&mut |agg| match &agg.kind {
                        AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => {
                            bodies.push(body.as_ref());
                        }
                        AggExprKind::Call(_) => {}
                    });
                }
                for body in bodies {
                    recurse(body, f);
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

/// How far back, in seconds, `c` can look from the timepoint it is evaluated
/// at: the specification's `Formula.horizon`, at one tick per second. A
/// `formerly` / `previous` adds its window to its body's horizon, and `since`
/// its window to the larger of its two sides'; a conjunction, disjunction,
/// negation or `exists` takes the largest of its parts', and a comparison the
/// largest of its aggregate operands' bodies'. A predicate or `tp` looks back
/// nothing, and a non-positive window counts as zero (it is rejected on its
/// own). The arithmetic is exact: each window's length fits an `i128`, and a
/// sum of as many of them as a source can nest does too.
pub(crate) fn horizon_seconds(c: &Condition) -> i128 {
    fn window(w: &WithinSpec) -> i128 {
        match w {
            WithinSpec::Concrete(i) => (i128::from(i.amount) * i128::from(i.unit.seconds())).max(0),
            // A residual parameter (only on an unexpanded macro body).
            _ => 0,
        }
    }
    fn term(t: &Term) -> i128 {
        match t {
            Term::Agg(agg) => match &agg.kind {
                AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => {
                    horizon_seconds(body)
                }
                // An unexpanded aggregate macro call (none post-expansion).
                AggExprKind::Call(_) => 0,
            },
            Term::Arith { left, right, .. } => term(left).max(term(right)),
            _ => 0,
        }
    }
    match &c.kind {
        ConditionKind::And { left, right } | ConditionKind::Or { left, right } => {
            horizon_seconds(left).max(horizon_seconds(right))
        }
        ConditionKind::Not { inner } => horizon_seconds(inner),
        ConditionKind::Exists { body, .. } => horizon_seconds(body),
        ConditionKind::Formerly { within, body } | ConditionKind::Previous { within, body } => {
            window(within).saturating_add(horizon_seconds(body))
        }
        ConditionKind::Since {
            left,
            within,
            right,
        } => window(within).saturating_add(horizon_seconds(left).max(horizon_seconds(right))),
        ConditionKind::Comparison { left, right, .. } => term(left).max(term(right)),
        ConditionKind::Predicate(_)
        | ConditionKind::Tp { .. }
        | ConditionKind::Call(_)
        | ConditionKind::SigilRef { .. }
        | ConditionKind::Refine { .. } => 0,
    }
}

/// Render a number of seconds as an interval, in `unit` when it divides evenly,
/// and in seconds otherwise.
fn render_seconds(secs: i128, unit: TimeUnit) -> String {
    let per = i128::from(unit.seconds());
    if per > 0 && secs % per == 0 {
        format!("{}{}", secs / per, unit.token())
    } else {
        format!("{secs}s")
    }
}

/// The finding for a leaf whose horizon exceeds the event schema's
/// `max_horizon`, if it does.
fn check_horizon(c: &Condition, max_horizon: Interval) -> Option<String> {
    let horizon = horizon_seconds(c);
    let cap = i128::from(max_horizon.seconds());
    (horizon > cap).then(|| {
        format!(
            "temporal condition looks back up to `{}` (the largest sum of the `within` windows \
             along one chain of nested `formerly`, `previous` and `since` operators), which \
             exceeds the event schema's `max_horizon` of `{}`; shorten or un-nest its \
             windows, or raise `max_horizon` in the event schema (events older than \
             `max_horizon` are never consulted)",
            render_seconds(horizon, max_horizon.unit),
            max_horizon.render(),
        )
    })
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
///      `max_window`. A `max_window` may not exceed a declared `max_horizon`,
///      so for a window longer than `max_horizon` the finding says to raise
///      `max_horizon`.
///
/// The whole condition tree is walked, so a `within` nested inside an
/// aggregation `where` body is checked too. Post-expansion every window is
/// [`WithinSpec::Concrete`]; a residual `ParamRef` (only possible on an
/// unexpanded macro body) is skipped.
fn check_windows(
    c: &Condition,
    max_window: Interval,
    max_horizon: Option<Interval>,
) -> Vec<LeafError> {
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
            let message = match max_horizon {
                Some(h) if secs > h.seconds() => format!(
                    "temporal window `{}` exceeds the maximum allowed window `{}`; \
                     shorten this window to at most `{}`, or raise the event schema's \
                     `max_horizon` of `{}` (and its `max_window`, if it declares one)",
                    interval.render(),
                    max_window.render(),
                    max_window.render(),
                    h.render(),
                ),
                _ => format!(
                    "temporal window `{}` exceeds the maximum allowed window `{}` \
                     set by the event schema's `max_window`; shorten this window to \
                     at most `{}`, or raise `max_window` in the event schema",
                    interval.render(),
                    max_window.render(),
                    max_window.render(),
                ),
            };
            errs.push(LeafError {
                message,
                span: Some(node.span),
            });
        }
    });
    errs
}

/// A wildcard is a pattern for a predicate argument only. As a comparison
/// operand it resolves to no value, so the comparison is always false, and its
/// negation always true: a guard that silently never fires. A wildcard inside a
/// compound operand is reported by `check_arith_atoms`.
fn check_wildcard_operands(c: &Condition, errs: &mut Vec<LeafError>) {
    walk(c, &mut |node| {
        if let ConditionKind::Comparison { left, right, .. } = &node.kind
            && (matches!(left, Term::Wildcard) || matches!(right, Term::Wildcard))
        {
            errs.push(LeafError {
                message: "a wildcard (`*` / `_`) cannot be a comparison operand; it resolves \
                          to no value, so the comparison is always false, and its negation \
                          always true"
                    .to_string(),
                span: Some(node.span),
            });
        }
    });
}

/// Every `decimal("…")` literal is a decimal Cedar accepts. One that is not
/// denotes no value, so a comparison with it never holds.
fn check_decimal_literals(c: &Condition, errs: &mut Vec<LeafError>) {
    walk(c, &mut |node| {
        let node_span = node.span;
        for_each_term(node, &mut |t| {
            if let Term::Decimal(text) = t
                && crate::interpreter::value::cedar_decimal_value(text).is_none()
            {
                errs.push(LeafError {
                    message: format!(
                        "`decimal({text:?})` does not parse as a `decimal`: Cedar's decimals \
                         have digits on both sides of a point, at most four after it, and fit \
                         a 64-bit integer at that scale"
                    ),
                    span: Some(node_span),
                });
            }
        });
    });
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
                // never be a *declared* entity type: it must name a declared
                // action instead. (The hoisted leaf is not seen by Cedar's
                // validator, so nothing else resolves it.)
                if is_action_ref(ty) {
                    if info.action(ns_opt.as_deref(), id).is_none() {
                        let id = cedar_policy_core::ast::Eid::new(id.as_str()).escaped();
                        errs.push(LeafError {
                            message: format!(
                                "`{ty}::\"{id}\"` is not a declared action; an action literal \
                                 names an action the schema declares"
                            ),
                            span: Some(node_span),
                        });
                    }
                    return;
                }
                match info.entity_type(ns_opt.as_deref(), simple) {
                    Some(entry) => {
                        if let Some(eids) = entry.enum_eids()
                            && !eids.iter().any(|e| e == id)
                        {
                            let id = cedar_policy_core::ast::Eid::new(id.as_str()).escaped();
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
                // A bare `principal` / `resource` root always resolves, so it
                // needs no check. An ATTRIBUTE tail does: the entity's declared
                // attributes say whether it exists and what it is, so an
                // unresolvable tail is a policy that
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
                "record has no field `{seg}` in `{}` path",
                crate::field_path::join_under("context", path)
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
/// A bare root always resolves and never reaches here. `id` and `type` are
/// attributes like any other, as in Cedar. Rejecting an
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
    let rendered = crate::field_path::join_under(root, tail);
    use super::schema_info::ScopePath;
    match sig.resolve_scope_path(root, tail, narrow.for_root(root)) {
        // A path of a different type on each entity type the scope admits is typed in
        // each request environment, as Cedar types it (`check_types`): a use well typed in
        // every one is valid, and one wrong in some is rejected there.
        ScopePath::Resolved | ScopePath::Unknown | ScopePath::Ambiguous { .. } => {}
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
    match t {
        Term::Array(items) => {
            for it in items {
                visit_term(it, f);
            }
        }
        Term::Arith { left, right, .. } => {
            visit_term(left, f);
            visit_term(right, f);
        }
        _ => {}
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
            .map(|e| {
                let eid = cedar_policy_core::ast::Eid::new(e.as_str()).escaped();
                format!("\"{eid}\"")
            })
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

#[cfg(test)]
mod tests {
    //! Unit tests for the compound-operand (arithmetic) all-`Long` sort
    //! rule, on a directly constructed leaf against a small fixture schema.

    use super::*;
    use crate::api::ActionRef;
    use crate::error::Span;
    use crate::extension::temporal::parse::parse_condition;

    // ── The horizon (`horizon_seconds`), node by node ──────────────────

    const LOGIN: &str = r#"Drupe::Action::"Pay"::request{input.amount: 1}"#;

    fn h(src: &str) -> i128 {
        horizon_seconds(&parse_condition(src).expect("condition parses"))
    }

    fn agg_term(src: &str) -> Term {
        let condition = parse_condition(src).expect("comparison parses");
        match &condition.kind {
            ConditionKind::Comparison { left, .. } => left.clone(),
            other => panic!("not a comparison: {other:?}"),
        }
    }

    #[test]
    fn horizon_adds_nested_windows() {
        assert_eq!(h(&format!("formerly within 2h (formerly within 3h {LOGIN})")), 5 * 3600);
        assert_eq!(h(&format!("previous within 2h (formerly within 3h {LOGIN})")), 5 * 3600);
    }

    #[test]
    fn horizon_since_adds_its_window_to_the_larger_side() {
        let src = format!(
            "(formerly within 1h {LOGIN}) since within 2h (formerly within 4h {LOGIN})"
        );
        assert_eq!(h(&src), 6 * 3600);
        let src = format!(
            "(formerly within 5h {LOGIN}) since within 2h (formerly within 4h {LOGIN})"
        );
        assert_eq!(h(&src), 7 * 3600);
    }

    #[test]
    fn horizon_takes_the_larger_conjunct_and_sees_through_negation_and_exists() {
        let src = format!("(formerly within 2h {LOGIN}) && !(formerly within 3h {LOGIN})");
        assert_eq!(h(&src), 3 * 3600);
        let src = format!(
            r#"exists (n: Long). (formerly within 4h Drupe::Action::"Pay"::request{{input.amount: n}})"#
        );
        assert_eq!(h(&src), 4 * 3600);
    }

    #[test]
    fn horizon_of_a_disjunction_is_the_larger_side() {
        // `||` is internal (pin relativization builds it), so build it directly.
        let left = parse_condition(&format!("formerly within 2h {LOGIN}")).unwrap();
        let right = parse_condition(&format!("formerly within 7h {LOGIN}")).unwrap();
        let or = Condition {
            span: Span::new(0, 0),
            kind: ConditionKind::Or {
                left: Box::new(left),
                right: Box::new(right),
            },
        };
        assert_eq!(horizon_seconds(&or), 7 * 3600);
    }

    #[test]
    fn horizon_of_an_aggregate_is_its_body() {
        let src = format!(
            "(count for (t: Timepoint). where (formerly within 3h ({LOGIN} && tp(t)))) > 0"
        );
        assert_eq!(h(&src), 3 * 3600);
    }

    #[test]
    fn horizon_of_an_arithmetic_operand_is_its_larger_aggregate() {
        // Arithmetic needs the `experimental-arithmetic` feature to parse, so build
        // `(count … 3h …) + (count … 5h …) > 0` from two parsed aggregates.
        let a = agg_term(&format!(
            "(count for (t: Timepoint). where (formerly within 3h ({LOGIN} && tp(t)))) > 0"
        ));
        let b = agg_term(&format!(
            "(count for (t: Timepoint). where (formerly within 5h ({LOGIN} && tp(t)))) > 0"
        ));
        let cmp = Condition {
            span: Span::new(0, 0),
            kind: ConditionKind::Comparison {
                op: CmpOp::Gt,
                left: Term::Arith {
                    op: super::super::ast::ArithOp::Add,
                    left: Box::new(a),
                    right: Box::new(b),
                },
                right: Term::Integer(0),
            },
        };
        assert_eq!(horizon_seconds(&cmp), 5 * 3600);
    }

    #[test]
    fn horizon_counts_a_non_positive_window_as_zero() {
        assert_eq!(h(&format!("formerly within 2h (formerly within 0h {LOGIN})")), 2 * 3600);
        assert_eq!(h(&format!("formerly within 2h (formerly within -5h {LOGIN})")), 2 * 3600);
    }

    #[test]
    fn horizon_of_a_predicate_or_tp_is_zero() {
        assert_eq!(h(LOGIN), 0);
    }

    const SCHEMA: &str = r#"
namespace Drupe {
  type PayInput = { amount: Long, note: String };
  type PayOutput = { };
  type SystemContext = { now: datetime };
  entity Gateway = { limit: Long };
  entity OAuthUser = { id: String };
  action "Pay" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: PayInput, output?: PayOutput, system: SystemContext }
  };
}
"#;

    /// Validate a temporal body against the fixture schema, scoped to
    /// `Drupe::Action::"Pay"`, and return every error message.
    fn errors(body: &str) -> Vec<String> {
        let condition =
            parse_condition(body).unwrap_or_else(|e| panic!("parse `{body}` failed: {e}"));
        let leaf = crate::extension::temporal::Temporal {
            condition,
            span: Span::new(0, 0),
        };
        let schema = cedar_policy::Schema::from_cedarschema_str(SCHEMA)
            .expect("fixture schema parses")
            .0;
        let info = SchemaInfo::from_validator_schema(schema.as_ref());
        let actions = [ActionRef {
            namespace: Some("Drupe".to_string()),
            id: "Pay".to_string(),
        }];
        validate_leaf(&leaf, &info, None, &actions, ScopeNarrowing::default())
            .into_iter()
            .map(|e| e.message)
            .collect()
    }

    fn has_sort_error(errs: &[String], needle: &str) -> bool {
        errs.iter().any(|m| m.contains(needle))
    }

    #[test]
    fn wildcard_atom_in_compound_is_rejected() {
        let errs = errors(r#"context.input.amount == * * 2"#);
        assert!(
            has_sort_error(&errs, "wildcard"),
            "expected a wildcard sort error, got: {errs:?}"
        );
    }

    #[test]
    fn decimal_atom_in_compound_is_rejected() {
        let errs = errors(r#"context.input.amount <= decimal("1.5") + 1"#);
        assert!(
            has_sort_error(&errs, "arithmetic operates only on `Long`"),
            "expected a Long-only sort error, got: {errs:?}"
        );
    }

    #[test]
    fn string_typed_atom_in_compound_is_rejected() {
        let errs = errors(r#"context.input.note + 1 <= 5"#);
        assert!(
            has_sort_error(&errs, "arithmetic operates only on `Long`"),
            "expected a Long-only sort error, got: {errs:?}"
        );
    }

    #[test]
    fn long_atoms_in_compound_pass_the_sort_rule() {
        // The pre-admission budget shape: an aggregate (tp-dependent,
        // Long) plus a Long context field against a literal. No errors.
        let errs = errors(
            r#"(sum a for (a: Long), (t: Timepoint). where (
                   formerly within 1h (Drupe::Action::"Pay"::request{ input.amount: a } && tp(t))
               )) + context.input.amount <= 100"#,
        );
        assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
    }

    #[test]
    fn var_and_attribute_atoms_in_compound_pass_the_sort_rule() {
        // A bound `Long` event variable and a `Long` entity attribute are
        // legal compound atoms under every operator.
        let errs = errors(
            r#"exists (a: Long). (
                   formerly within 1h Drupe::Action::"Pay"::request{ input.amount: a }
                   && a * 2 - resource.limit <= context.input.amount + 5
               )"#,
        );
        assert!(errs.is_empty(), "expected no errors, got: {errs:?}");
    }
}
