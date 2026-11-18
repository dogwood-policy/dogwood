//! The facts a hoisted leaf's position establishes: the attribute paths the
//! Cedar part of its rule has tested present, with `has`, wherever Cedar
//! evaluates the leaf.
//!
//! A temporal term may read an optional attribute of the request context, or
//! of the principal or resource, only where such a test guards it
//! (`dogwood-lean`, `Formula.WellTyped` and `Expr.leafFacts`). The facts are
//! read off the lowered Cedar policy, in which the leaf is the attribute access
//! `context.<id>`:
//!
//! * a test establishes a fact when it is `has` on an attribute chain rooted at
//!   `context`, `principal`, or `resource`: `context.input has amount`
//!   establishes `context.input.amount`. Cedar's `context has input.amount`
//!   is the conjunction `context has input && context.input has amount`, and
//!   establishes both facts;
//! * a conjunction establishes the facts of both operands;
//! * facts flow from the left operand of `&&` to its right operand, and from
//!   the condition of `if` to its `then` branch, because Cedar evaluates those
//!   only when the left operand or the condition is `true`. A policy's `when` and
//!   `unless` clauses are conjoined in source order, so facts flow from a clause
//!   to the clauses after it, and never out of an `unless`, which negates.

use std::collections::BTreeMap;

use cedar_policy_core::ast::{Expr, ExprKind, Var};
use smol_str::SmolStr;

/// An attribute path that the Cedar part of a rule has tested present.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Guard {
    /// A path of the request context: `context.input.amount` is
    /// `["input", "amount"]`.
    Context(Vec<String>),
    /// A path of the principal's or resource's attributes: `principal.dept`
    /// is `("principal", ["dept"])`.
    Scope(&'static str, Vec<String>),
}

/// The facts established at each `context.<id>` leaf of `policy`'s condition,
/// for every `id` that `is_leaf` accepts, keyed by `id`. A leaf the condition
/// reads twice keeps the facts both positions establish in common.
pub(crate) fn leaf_facts(
    condition: &Expr,
    is_leaf: &dyn Fn(&str) -> bool,
) -> BTreeMap<String, Vec<Guard>> {
    let mut out: BTreeMap<String, Vec<Guard>> = BTreeMap::new();
    walk(condition, &[], is_leaf, &mut out);
    out
}

/// The variable and attribute names an expression reads, when it is an
/// attribute chain rooted at a request variable.
fn attr_chain(e: &Expr) -> Option<(Var, Vec<String>)> {
    match e.expr_kind() {
        ExprKind::Var(v) => Some((*v, Vec::new())),
        ExprKind::GetAttr { expr, attr } => {
            let (v, mut path) = attr_chain(expr)?;
            path.push(attr.to_string());
            Some((v, path))
        }
        _ => None,
    }
}

/// The facts an expression establishes when it evaluates to `true`.
fn facts(e: &Expr) -> Vec<Guard> {
    match e.expr_kind() {
        ExprKind::HasAttr { expr, attr } => has_facts(expr, std::iter::once(attr)),
        // `e has a.b` (Cedar 4.14 keeps it unexpanded) is `e has a && e.a has b`.
        ExprKind::ExtHasAttr { expr, attrs } => has_facts(expr, attrs.iter()),
        ExprKind::And { left, right } => {
            let mut out = facts(left);
            out.extend(facts(right));
            out
        }
        _ => Vec::new(),
    }
}

/// The facts `base has a1.….an` establishes: one per prefix `base.a1.….ak`.
fn has_facts<'a>(base: &Expr, attrs: impl Iterator<Item = &'a SmolStr>) -> Vec<Guard> {
    let Some((var, mut path)) = attr_chain(base) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for attr in attrs {
        path.push(attr.to_string());
        match var {
            Var::Context => out.push(Guard::Context(path.clone())),
            Var::Principal => out.push(Guard::Scope("principal", path.clone())),
            Var::Resource => out.push(Guard::Scope("resource", path.clone())),
            Var::Action => {}
        }
    }
    out
}

fn record(out: &mut BTreeMap<String, Vec<Guard>>, id: &str, here: &[Guard]) {
    match out.get_mut(id) {
        Some(existing) => existing.retain(|g| here.contains(g)),
        None => {
            out.insert(id.to_string(), here.to_vec());
        }
    }
}

fn walk(
    e: &Expr,
    here: &[Guard],
    is_leaf: &dyn Fn(&str) -> bool,
    out: &mut BTreeMap<String, Vec<Guard>>,
) {
    let mut go = |x: &Expr, facts: &[Guard]| walk(x, facts, is_leaf, out);
    match e.expr_kind() {
        ExprKind::GetAttr { expr, attr } => {
            if matches!(expr.expr_kind(), ExprKind::Var(Var::Context)) && is_leaf(attr) {
                record(out, attr, here);
            } else {
                go(expr, here);
            }
        }
        ExprKind::And { left, right } => {
            go(left, here);
            let mut after = here.to_vec();
            after.extend(facts(left));
            go(right, &after);
        }
        ExprKind::If {
            test_expr,
            then_expr,
            else_expr,
        } => {
            go(test_expr, here);
            let mut after = here.to_vec();
            after.extend(facts(test_expr));
            go(then_expr, &after);
            go(else_expr, here);
        }
        ExprKind::Or { left, right } => {
            go(left, here);
            go(right, here);
        }
        ExprKind::BinaryApp { arg1, arg2, .. } => {
            go(arg1, here);
            go(arg2, here);
        }
        ExprKind::UnaryApp { arg, .. } => go(arg, here),
        ExprKind::HasAttr { expr, .. }
        | ExprKind::ExtHasAttr { expr, .. }
        | ExprKind::Like { expr, .. }
        | ExprKind::Is { expr, .. } => go(expr, here),
        ExprKind::ExtensionFunctionApp { args, .. } => {
            for a in args.iter() {
                go(a, here);
            }
        }
        ExprKind::Set(items) => {
            for a in items.iter() {
                go(a, here);
            }
        }
        ExprKind::Record(fields) => {
            for a in fields.values() {
                go(a, here);
            }
        }
        ExprKind::Lit(_) | ExprKind::Var(_) | ExprKind::Slot(_) | ExprKind::Unknown(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn facts_of(condition: &str) -> BTreeMap<String, Vec<Guard>> {
        let policy = cedar_policy_core::parser::parse_policy(
            None,
            &format!("permit (principal, action, resource) when {{ {condition} }};"),
        )
        .expect("policy parses");
        let expr = policy.non_scope_constraints().expect("a condition").clone();
        leaf_facts(&expr, &|id| id.starts_with("leaf"))
    }

    fn ctx(path: &[&str]) -> Guard {
        Guard::Context(path.iter().map(|s| s.to_string()).collect())
    }

    #[test]
    fn a_has_test_before_the_leaf_guards_it() {
        let f = facts_of("context.input has note && context.leaf0");
        assert_eq!(f["leaf0"], vec![ctx(&["input", "note"])]);
    }

    #[test]
    fn a_has_path_establishes_every_prefix() {
        let f = facts_of("context has input.note && context.leaf0");
        assert_eq!(f["leaf0"], vec![ctx(&["input"]), ctx(&["input", "note"])]);
    }

    #[test]
    fn a_scope_has_path_establishes_every_prefix() {
        let f = facts_of("principal has dept.team && context.leaf0");
        assert_eq!(
            f["leaf0"],
            vec![
                Guard::Scope("principal", vec!["dept".to_string()]),
                Guard::Scope("principal", vec!["dept".to_string(), "team".to_string()]),
            ]
        );
    }

    #[test]
    fn a_leaf_under_a_has_path_is_found() {
        let f = facts_of("context.input has note && context.leaf0 has a.b");
        assert_eq!(f["leaf0"], vec![ctx(&["input", "note"])]);
    }

    #[test]
    fn a_test_after_the_leaf_or_beside_it_guards_nothing() {
        let f = facts_of("context.leaf0 && context.input has note");
        assert_eq!(f["leaf0"], Vec::<Guard>::new());
        let f = facts_of("context.input has note || context.leaf0");
        assert_eq!(f["leaf0"], Vec::<Guard>::new());
        let f = facts_of("!(context.input has note) && context.leaf0");
        assert_eq!(f["leaf0"], Vec::<Guard>::new());
    }

    #[test]
    fn an_if_condition_guards_its_then_branch_only() {
        let f = facts_of("if context.input has note then context.leaf0 else context.leaf1");
        assert_eq!(f["leaf0"], vec![ctx(&["input", "note"])]);
        assert_eq!(f["leaf1"], Vec::<Guard>::new());
    }

    #[test]
    fn scope_attributes_are_guarded_by_their_root() {
        let f = facts_of("principal has dept && resource.owner has team && context.leaf0");
        assert_eq!(
            f["leaf0"],
            vec![
                Guard::Scope("principal", vec!["dept".to_string()]),
                Guard::Scope("resource", vec!["owner".to_string(), "team".to_string()]),
            ]
        );
    }
}
