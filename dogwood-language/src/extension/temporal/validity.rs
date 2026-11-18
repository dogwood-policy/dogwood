//! Validity rules of the formal specification that the temporal dialect's
//! older checks (`validate.rs`) do not cover.
//!
//! Each rule is one of `Formula.WellTyped`'s (`dogwood-lean`,
//! `Dogwood.Spec.Temporal.Typing`), and each finding names its category in its
//! message, so a reader, and the conformance harness, can tell them apart:
//!
//! * **Optional attributes.** A `context.<path>`, `principal.<path>`, or
//!   `resource.<path>` term reads an optional attribute only where the Cedar
//!   part of the rule tests it with `has` at the leaf's position
//!   ([`super::facts`]), as in `context.input has amount && temporal { … }`.
//!   Unguarded, the read makes a comparison false when the attribute is
//!   absent, and true under `!`.
//! * **Pins.** Every pin of an event a predicate names correlates its field
//!   with a request-side path that is declared and *required* in every request
//!   the rule decides, of a type the field can hold: so a conforming request
//!   always has the pin's value.
//! * **Binders.** The `for` variables of one aggregation have distinct names.
//! * **Binding fields.** A variable bound by a predicate field, `P{ f: x }`,
//!   has a type every value of the field has. A field of `principalType(A)`
//!   holds an entity of any of `A`'s principal types, so a variable it binds
//!   must accept every one of them.
//!
//! A rule is checked in every request environment the rule's scope admits, as
//! Cedar validates a policy: every action the scope resolves to, and every
//! principal and resource type the scope admits for it.

use std::collections::BTreeSet;

use cedar_policy_core::ast::EntityType;
use cedar_policy_core::validator::ValidatorSchema;
use cedar_policy_core::validator::types::{Attributes, Type};

use super::ast::{
    AggExpr, AggExprKind, BinderSlot, Condition, ConditionKind, Predicate, Term,
    Type as BinderType, TypedBinder,
};
use super::facts::Guard;
use super::schema_info::{ActionHandle, SchemaInfo, UNSUPPORTED_EXTENSION};
use super::validate::{LeafError, ScopeNarrowing};
use crate::conformance::{CType, event_fields};
use crate::error::Span;
use crate::event_schema::ast::PinRoot;
use crate::event_schema::derive::DerivedEventSchema;

/// Run the rules on one leaf. `facts` are the facts its position establishes.
pub(crate) fn check_leaf(
    leaf: &crate::api::TemporalField,
    info: &SchemaInfo,
    events: &DerivedEventSchema,
    facts: &[Guard],
) -> Vec<LeafError> {
    let narrow = ScopeNarrowing {
        principal: Some(&leaf.principal),
        resource: Some(&leaf.resource),
    };
    let schema = info.validator_schema();
    let mut errs = Vec::new();
    check_for_lists(&leaf.condition.condition, schema, &mut errs);
    check_binder_types(&leaf.condition.condition, schema, &mut errs);
    let actions: Vec<ActionHandle<'_>> = leaf
        .target_actions
        .iter()
        .filter_map(|a| info.action(a.namespace.as_deref(), &a.id))
        .filter(|a| a.admits_any_env(narrow.principal, narrow.resource))
        .collect();
    visit(
        &leaf.condition.condition,
        schema,
        &mut Vec::new(),
        &mut |node, scope| {
            for term in node_terms(node) {
                check_optional_read(term, node.span, &actions, narrow, facts, &mut errs);
            }
            if let ConditionKind::Predicate(p) = &node.kind {
                check_pins(p, &actions, narrow, schema, events, &mut errs);
                check_binding_fields(p, scope, schema, events, &mut errs);
            }
        },
    );
    // One finding however many environments produce it.
    let mut seen = BTreeSet::new();
    errs.retain(|e| seen.insert((e.message.clone(), e.span.map(|s| s.start))));
    errs
}

// ─── Traversal ───────────────────────────────────────────────────────

/// The binders in scope at a node, innermost last.
type Scope<'a> = Vec<&'a TypedBinder>;

/// Visit every condition node of `c`, aggregation bodies included, with the
/// binders in scope there. The body of an ill-formed binder list
/// (`binders_typed`) is not visited: the binder's finding stands for it.
fn visit<'a>(
    c: &'a Condition,
    schema: &ValidatorSchema,
    scope: &mut Scope<'a>,
    f: &mut impl FnMut(&'a Condition, &Scope<'a>),
) {
    f(c, scope);
    match &c.kind {
        ConditionKind::And { left, right }
        | ConditionKind::Or { left, right }
        | ConditionKind::Since { left, right, .. } => {
            visit(left, schema, scope, f);
            visit(right, schema, scope, f);
        }
        ConditionKind::Not { inner }
        | ConditionKind::Formerly { body: inner, .. }
        | ConditionKind::Previous { body: inner, .. } => visit(inner, schema, scope, f),
        ConditionKind::Exists { var, body } => {
            if binders_typed(std::slice::from_ref(var), schema) {
                scope.push(var);
                visit(body, schema, scope, f);
                scope.pop();
            }
        }
        ConditionKind::Comparison { left, right, .. } => {
            for term in [left, right] {
                visit_term(term, schema, scope, f);
            }
        }
        ConditionKind::Predicate(p) => {
            for arg in &p.args {
                visit_term(&arg.value, schema, scope, f);
            }
        }
        ConditionKind::Refine { base, .. } => visit(base, schema, scope, f),
        ConditionKind::Tp { .. } | ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => {}
    }
}

fn visit_term<'a>(
    t: &'a Term,
    schema: &ValidatorSchema,
    scope: &mut Scope<'a>,
    f: &mut impl FnMut(&'a Condition, &Scope<'a>),
) {
    match t {
        Term::Agg(agg) => match &agg.kind {
            AggExprKind::Count { for_vars, body } | AggExprKind::Sum { for_vars, body, .. } => {
                if binders_typed(for_vars, schema) {
                    let depth = scope.len();
                    scope.extend(for_vars.iter());
                    visit(body, schema, scope, f);
                    scope.truncate(depth);
                }
            }
            AggExprKind::Call(_) => {}
        },
        Term::Arith { left, right, .. } => {
            visit_term(left, schema, scope, f);
            visit_term(right, schema, scope, f);
        }
        Term::Array(items) => {
            for item in items {
                visit_term(item, schema, scope, f);
            }
        }
        _ => {}
    }
}

/// The terms a node carries directly, with the atoms of a compound operand and
/// the elements of an array: the comparison operands and the predicate
/// arguments. Aggregation bodies are nodes of their own.
fn node_terms(node: &Condition) -> Vec<&Term> {
    fn atoms<'a>(t: &'a Term, out: &mut Vec<&'a Term>) {
        out.push(t);
        match t {
            Term::Arith { left, right, .. } => {
                atoms(left, out);
                atoms(right, out);
            }
            Term::Array(items) => items.iter().for_each(|i| atoms(i, out)),
            _ => {}
        }
    }
    let mut out = Vec::new();
    match &node.kind {
        ConditionKind::Comparison { left, right, .. } => {
            atoms(left, &mut out);
            atoms(right, &mut out);
        }
        ConditionKind::Predicate(p) => p.args.iter().for_each(|a| atoms(&a.value, &mut out)),
        _ => {}
    }
    out
}

// ─── Optional attributes ─────────────────────────────────────────────

fn record_attrs(ty: &Type) -> Option<&Attributes> {
    match ty {
        Type::Record { attrs, .. } => Some(attrs),
        _ => None,
    }
}

/// The first optional attribute along `path` in `attrs` that no fact guards:
/// the full prefix that ends at it. `guarded` tells whether a prefix is tested
/// present. A path that does not resolve has none: the path checks report it.
fn unguarded_optional(
    mut attrs: &Attributes,
    path: &[String],
    guarded: &dyn Fn(&[String]) -> bool,
) -> Option<Vec<String>> {
    for (k, segment) in path.iter().enumerate() {
        let attr = attrs.get_attr(segment)?;
        if !attr.is_required() && !guarded(&path[..=k]) {
            return Some(path[..=k].to_vec());
        }
        if k + 1 < path.len() {
            attrs = record_attrs(&attr.attr_type)?;
        }
    }
    None
}

fn check_optional_read(
    term: &Term,
    span: Span,
    actions: &[ActionHandle<'_>],
    narrow: ScopeNarrowing<'_>,
    facts: &[Guard],
    errs: &mut Vec<LeafError>,
) {
    match term {
        Term::ContextField(path) => {
            let guarded = |prefix: &[String]| facts.contains(&Guard::Context(prefix.to_vec()));
            for action in actions {
                let Some(attrs) = action.context_type().and_then(record_attrs) else {
                    continue;
                };
                if let Some(prefix) = unguarded_optional(attrs, path, &guarded) {
                    let (last, parent) = prefix.split_last().expect("a non-empty prefix");
                    let parent = crate::field_path::join_under("context", parent);
                    errs.push(LeafError {
                        message: format!(
                            "`context.{}` reads the optional attribute `{}` of the context of \
                             `{}` with no `has` test guarding it, so a request without it makes \
                             the comparison false, and true under `!`; test it first, as in \
                             `{parent} has {last} && temporal {{ … }}`",
                            crate::field_path::join(path),
                            crate::field_path::join(&prefix),
                            action.uid(),
                        ),
                        span: Some(span),
                    });
                }
            }
        }
        Term::ScopeField(path) => {
            let [root, tail @ ..] = path.as_slice() else {
                return;
            };
            let root: &'static str = match root.as_str() {
                "principal" => "principal",
                "resource" => "resource",
                _ => return,
            };
            // A bare `principal` / `resource` is the entity itself, always present.
            if tail.is_empty() {
                return;
            }
            let guarded = |prefix: &[String]| facts.contains(&Guard::Scope(root, prefix.to_vec()));
            let narrowing = match root {
                "principal" => narrow.principal,
                _ => narrow.resource,
            };
            for action in actions {
                for ety in action.admitted_types(root, narrowing) {
                    let Some(attrs) = action.entity_attributes(ety) else {
                        continue;
                    };
                    if let Some(prefix) = unguarded_optional(attrs, tail, &guarded) {
                        let (last, parent) = prefix.split_last().expect("a non-empty prefix");
                        let parent = crate::field_path::join_under(root, parent);
                        errs.push(LeafError {
                            message: format!(
                                "`{}` reads the optional attribute `{}` of `{ety}` with no `has` \
                                 test guarding it, so a request without it makes the comparison \
                                 false, and true under `!`; test it first, as in \
                                 `{parent} has {last} && temporal {{ … }}`",
                                crate::field_path::join(path),
                                crate::field_path::join(&prefix),
                            ),
                            span: Some(span),
                        });
                    }
                }
            }
        }
        _ => {}
    }
}

// ─── Pins ────────────────────────────────────────────────────────────

/// The type of the attribute at `path` in `attrs`, when every attribute along
/// it is declared and required.
fn required_path_type<'a>(mut attrs: &'a Attributes, path: &[String]) -> Option<&'a Type> {
    let (last, init) = path.split_last()?;
    for segment in init {
        let attr = attrs.get_attr(segment).filter(|a| a.is_required())?;
        attrs = record_attrs(&attr.attr_type)?;
    }
    let attr = attrs.get_attr(last).filter(|a| a.is_required())?;
    Some(&attr.attr_type)
}

/// Whether a field of type `field` can hold a value of type `value`
/// (`FieldTy.Accepts`). A field whose type the event schema names in text the
/// schema does not declare (`CType::Any`) holds no value of a known type, so a
/// pin or an argument of it cannot be checked, and is rejected.
pub(crate) fn accepts(field: &CType, value: &CType) -> bool {
    match (field, value) {
        (CType::Any, _) | (_, CType::Any) => false,
        (CType::Entity(names), CType::Entity(value)) => {
            value.len() == 1 && names.contains(&value[0])
        }
        _ => field == value,
    }
}

/// The types a pin's request-side reference has in the environments of
/// `action` the rule decides: `None` when the reference is not a declared,
/// required path there.
fn pin_ref_types(
    root: PinRoot,
    path: &[String],
    action: &ActionHandle<'_>,
    narrow: ScopeNarrowing<'_>,
) -> Option<Vec<CType>> {
    match root {
        PinRoot::Context => {
            // A hoisted attribute is not part of the request a caller supplies.
            if path.first().is_some_and(|head| crate::api::is_hoisted_name(head)) {
                return None;
            }
            let ty = required_path_type(record_attrs(action.context_type()?)?, path)?;
            Some(vec![CType::from_type(ty)])
        }
        PinRoot::Scope => {
            let (scope, tail) = path.split_first()?;
            let narrowing = match scope.as_str() {
                "principal" => narrow.principal,
                "resource" => narrow.resource,
                _ => return None,
            };
            let types = action.admitted_types(scope, narrowing);
            if tail.is_empty() {
                return Some(
                    types
                        .into_iter()
                        .map(|ety| CType::Entity(vec![ety.to_string()]))
                        .collect(),
                );
            }
            types
                .into_iter()
                .map(|ety| {
                    let ty = required_path_type(action.entity_attributes(ety)?, tail)?;
                    Some(CType::from_type(ty))
                })
                .collect()
        }
    }
}

/// Whether a value type is, or holds, one of Cedar's extension types other
/// than `decimal` (`RichType::holds_unsupported_extension`).
fn ctype_holds_unsupported_extension(t: &CType) -> bool {
    match t {
        CType::Extension(_) => true,
        CType::Set(inner) => ctype_holds_unsupported_extension(inner),
        CType::Record { attrs, .. } => attrs
            .values()
            .any(|(t, _)| ctype_holds_unsupported_extension(t)),
        _ => false,
    }
}

fn check_pins(
    p: &Predicate,
    actions: &[ActionHandle<'_>],
    narrow: ScopeNarrowing<'_>,
    schema: &ValidatorSchema,
    events: &DerivedEventSchema,
    errs: &mut Vec<LeafError>,
) {
    let Some(event) = events.get(&p.namespace, &p.action, &p.kind) else {
        return;
    };
    if event.pins.is_empty() {
        return;
    }
    let fields = event_fields(event, schema);
    let head = format!(
        "{}::{}",
        crate::api::qualified_action_uid(&event.namespace, &event.action),
        event.kind
    );
    for pin in &event.pins {
        let Some((_, field_ty, _)) = fields.iter().find(|(path, _, _)| *path == pin.field_path)
        else {
            continue;
        };
        let reference = match pin.root {
            PinRoot::Context => crate::field_path::join_under("context", &pin.context_path),
            PinRoot::Scope => crate::field_path::join(&pin.context_path),
        };
        for action in actions {
            let ref_types = pin_ref_types(pin.root, &pin.context_path, action, narrow);
            if let Some(t) = ref_types
                .iter()
                .flatten()
                .find(|t| ctype_holds_unsupported_extension(t))
            {
                errs.push(LeafError {
                    message: format!(
                        "pin `{}` of `{head}` correlates the field with `{reference}`, of type \
                         `{}`; {UNSUPPORTED_EXTENSION}",
                        crate::field_path::join(&pin.field_path),
                        t.render(),
                    ),
                    span: Some(p.span),
                });
                continue;
            }
            let message = match ref_types {
                None => format!(
                    "pin `{}` of `{head}` correlates the field with `{reference}`, which is not a \
                     declared, required attribute in the requests of `{}` the rule decides; a \
                     pin's request-side path must be, so that every conforming request has its \
                     value",
                    crate::field_path::join(&pin.field_path),
                    action.uid(),
                ),
                Some(types) => match types.iter().find(|t| !accepts(field_ty, t)) {
                    Some(t) => format!(
                        "pin `{}` of `{head}` correlates the field, of type `{}`, with \
                         `{reference}`, which is a `{}` in the requests of `{}` the rule decides; \
                         the field cannot hold it",
                        crate::field_path::join(&pin.field_path),
                        field_ty.render(),
                        t.render(),
                        action.uid(),
                    ),
                    None => continue,
                },
            };
            errs.push(LeafError {
                message,
                span: Some(p.span),
            });
        }
    }
}

// ─── Binders and binding fields ──────────────────────────────────────

fn binder_name(b: &TypedBinder) -> Option<&str> {
    match &b.slot {
        BinderSlot::Name(name) => Some(name),
        _ => None,
    }
}

fn check_for_lists(c: &Condition, schema: &ValidatorSchema, errs: &mut Vec<LeafError>) {
    let mut check = |agg: &AggExpr| {
        let (AggExprKind::Count { for_vars, .. } | AggExprKind::Sum { for_vars, .. }) = &agg.kind
        else {
            return;
        };
        let mut seen = BTreeSet::new();
        for name in for_vars.iter().filter_map(binder_name) {
            if !seen.insert(name) {
                errs.push(LeafError {
                    message: format!(
                        "the `for` list of this aggregation binds `{name}` more than once; give \
                         each `for` variable a name of its own, since the rows are projected \
                         onto one column per name"
                    ),
                    span: Some(agg.span),
                });
            }
        }
    };
    visit(c, schema, &mut Vec::new(), &mut |node, _| {
        if let ConditionKind::Comparison { left, right, .. } = &node.kind {
            for term in [left, right] {
                term.for_each_operand_agg(&mut |agg| check(agg));
            }
        }
    });
}

/// Whether a binder's declared type means something: a scalar, named by its
/// last segment (`Long`, `String`, `Bool`, `decimal`), `Timepoint`, or an
/// entity type the schema declares, by its qualified name as written. Cedar's
/// other extension types (`datetime`, `duration`, `ipaddr`) are not: temporal
/// conditions do not support them (`unsupported_extension_binder`).
pub(crate) fn binder_type_declared(ty: &BinderType, schema: &ValidatorSchema) -> bool {
    match ty {
        BinderType::Timepoint => true,
        BinderType::Named(path) => match path.last().map(String::as_str) {
            Some("Long" | "String" | "Bool" | "Boolean" | "decimal" | "Decimal") => true,
            _ => path
                .join("::")
                .parse::<EntityType>()
                .is_ok_and(|ety| schema.get_entity_type(&ety).is_some()),
        },
    }
}

/// Whether a list of binders (an `exists` binder, or an aggregation's `for`
/// list) is well-formed: every type means something, and the names are
/// distinct. The body of an ill-formed list is not typed further: its finding
/// is the binder's, as the specification reports it (`domainSorts?`,
/// `Binder.sort?`).
pub(crate) fn binders_typed(binders: &[TypedBinder], schema: &ValidatorSchema) -> bool {
    let mut names = BTreeSet::new();
    binders.iter().all(|b| {
        binder_type_declared(&b.ty, schema) && binder_name(b).is_none_or(|n| names.insert(n))
    })
}

/// Every `exists` binder and `for` variable has a type that means something
/// (`binder_type_declared`). An undeclared entity type, or one written by its
/// last segment only, types no value: a predicate the binder appears in can
/// never match.
fn check_binder_types(c: &Condition, schema: &ValidatorSchema, errs: &mut Vec<LeafError>) {
    visit(c, schema, &mut Vec::new(), &mut |node, _| {
        let mut check = |binder: &TypedBinder, span: Span| {
            if !binder_type_declared(&binder.ty, schema) {
                let name = binder_name(binder).unwrap_or("_");
                let message = if unsupported_extension_binder(&binder.ty) {
                    format!(
                        "the binder `{name}` is declared `{}`; {UNSUPPORTED_EXTENSION}",
                        binder.ty.render()
                    )
                } else {
                    format!(
                        "the binder `{name}` is declared `{}`, which names no declared entity \
                         type; a binder's type is `Long`, `String`, `Bool`, `decimal`, \
                         `Timepoint`, or an entity type the schema declares, written with its \
                         namespace",
                        binder.ty.render()
                    )
                };
                errs.push(LeafError {
                    message,
                    span: Some(span),
                });
            }
        };
        match &node.kind {
            ConditionKind::Exists { var, .. } => check(var, node.span),
            ConditionKind::Comparison { left, right, .. } => {
                for term in [left, right] {
                    term.for_each_operand_agg(&mut |agg| {
                        if let AggExprKind::Count { for_vars, .. }
                        | AggExprKind::Sum { for_vars, .. } = &agg.kind
                        {
                            for v in for_vars {
                                check(v, agg.span);
                            }
                        }
                    });
                }
            }
            _ => {}
        }
    });
}

/// Whether a binder is declared with one of Cedar's extension types other than
/// `decimal`, by its last segment, as a scalar is named.
fn unsupported_extension_binder(ty: &BinderType) -> bool {
    matches!(ty, BinderType::Named(path)
        if matches!(path.last().map(String::as_str), Some("datetime" | "duration" | "ipaddr")))
}

/// The type a binder's declared type means, as a value type: `None` for a
/// `Timepoint`, which is not a value of any field.
fn binder_value_type(ty: &BinderType, schema: &ValidatorSchema) -> Option<CType> {
    match ty {
        BinderType::Timepoint => None,
        BinderType::Named(path) => Some(match path.last().map(String::as_str) {
            Some("Long") => CType::Long,
            Some("String") => CType::String,
            Some("Bool" | "Boolean") => CType::Bool,
            Some("decimal" | "Decimal") => CType::Decimal,
            _ => {
                let name = path.join("::");
                match name.parse::<EntityType>() {
                    Ok(ety) if schema.get_entity_type(&ety).is_some() => {
                        CType::Entity(vec![ety.to_string()])
                    }
                    // An undeclared type is the binder checks' finding.
                    _ => return Some(CType::Any),
                }
            }
        }),
    }
}

/// Whether every value of a field of type `field` has type `var`
/// (`FieldTy.Within`). A field of a type the schema does not declare
/// (`CType::Any`) has no such type, nor does a binder of an undeclared type.
fn within(field: &CType, var: &CType) -> bool {
    match (field, var) {
        (CType::Any, _) | (_, CType::Any) => false,
        (CType::Entity(names), CType::Entity(var)) => {
            !names.is_empty() && var.len() == 1 && names.iter().all(|n| *n == var[0])
        }
        _ => field == var,
    }
}

fn check_binding_fields(
    p: &Predicate,
    scope: &Scope<'_>,
    schema: &ValidatorSchema,
    events: &DerivedEventSchema,
    errs: &mut Vec<LeafError>,
) {
    let Some(event) = events.get(&p.namespace, &p.action, &p.kind) else {
        return;
    };
    let fields = event_fields(event, schema);
    for arg in &p.args {
        let Term::Var(x) = &arg.value else {
            continue;
        };
        // Spliced `input` / `output` fields are typed by the operand and
        // argument checks; this rule covers the fields the event schema names.
        let path = arg.field_path();
        if matches!(path.first().map(String::as_str), Some("input" | "output")) {
            continue;
        }
        let Some((_, field_ty, _)) = fields.iter().find(|(p, _, _)| *p == path) else {
            continue;
        };
        let Some(binder) = scope.iter().rev().find(|b| binder_name(b) == Some(x)) else {
            continue;
        };
        let ok = match binder_value_type(&binder.ty, schema) {
            Some(var_ty) => within(field_ty, &var_ty),
            None => false,
        };
        if !ok {
            let action = cedar_policy_core::ast::Eid::new(p.action.as_str()).escaped();
            errs.push(LeafError {
                message: format!(
                    "argument `{}` of `{action}` expects `{}`, but binds the variable `{x}`, \
                     declared `{}`: a variable bound by a field must have a type every value \
                     of the field has",
                    arg.name,
                    field_ty.render(),
                    binder.ty.render(),
                ),
                span: Some(p.span),
            });
        }
    }
}
