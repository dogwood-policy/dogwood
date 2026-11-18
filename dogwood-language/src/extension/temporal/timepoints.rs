//! Timepoints are equality-only: the executable form of an authored leaf.
//!
//! A `tp(x)`-bound variable holds a timepoint, which the language observes only
//! through equality: two timepoints may be compared with `==`, and a timepoint
//! keeps aggregation rows distinct, but a timepoint is not ordered and is not an
//! operand of arithmetic. Validation rejects a leaf that orders a timepoint
//! (`check_types_for_action`) or computes with one (`check_arith_atoms`). The
//! specification gives such a comparison its meaning anyway, since its
//! semantics is total: an ordering applies only to two integers and is false
//! otherwise, and a compound operand with a timepoint atom denotes nothing, so
//! the comparison is false (`dogwood-lean`, `CmpOp.Holds` and `Term.arith`).
//!
//! The interpreter represents a timepoint by its index, an integer, so it would
//! order two timepoints by position. The pin-relativization rewrite relies on
//! exactly that ordering for the fresh timepoint variables it introduces
//! (`event_schema::relativize`), so the interpreter cannot refuse to order
//! timepoints. Instead, [`unorder_timepoints`] gives an authored leaf its
//! specified meaning before the rewrite runs: every comparison that orders a
//! timepoint, or computes with one, is replaced by a comparison that is false.
//! The rewrite's own orderings come afterwards, so they are untouched.
//!
//! A variable is a timepoint when its innermost binder declares it
//! `Timepoint`. A leaf that binds a variable of another declared type with
//! `tp(x)` is rejected by validation, and is not normalized.

use super::ast::{
    AggExpr, AggExprKind, BinderSlot, CmpOp, Condition, ConditionKind, Term, Type, TypedBinder,
};

/// The executable form of an authored temporal condition: every comparison
/// that orders a timepoint variable, or has a compound operand with a
/// timepoint atom, is replaced by the constant-false comparison `0 == 1`.
/// Every other node is unchanged.
pub(crate) fn unorder_timepoints(cond: &Condition) -> Condition {
    let mut scope = Vec::new();
    rewrite(cond, &mut scope)
}

/// The binders in scope, innermost last: each name, and whether it is a
/// timepoint.
type Scope = Vec<(String, bool)>;

/// A binder's name and whether it is a timepoint. A binder still carrying a
/// macro sigil binds no name a term can refer to.
fn binding(binder: &TypedBinder) -> (String, bool) {
    let name = match &binder.slot {
        BinderSlot::Name(name) => name.clone(),
        _ => String::new(),
    };
    (name, binder.ty == Type::Timepoint)
}

fn is_timepoint(scope: &Scope, name: &str) -> bool {
    scope
        .iter()
        .rev()
        .find(|(n, _)| n == name)
        .is_some_and(|(_, tp)| *tp)
}

/// Whether a comparison operand is a timepoint variable.
fn is_timepoint_var(term: &Term, scope: &Scope) -> bool {
    matches!(term, Term::Var(x) if is_timepoint(scope, x))
}

/// Whether a compound operand has a timepoint atom.
fn computes_with_timepoint(term: &Term, scope: &Scope) -> bool {
    match term {
        Term::Arith { left, right, .. } => {
            is_timepoint_var(left, scope)
                || is_timepoint_var(right, scope)
                || computes_with_timepoint(left, scope)
                || computes_with_timepoint(right, scope)
        }
        _ => false,
    }
}

/// The comparison `0 == 1`, which is false at every timepoint.
fn constant_false(span: crate::error::Span) -> Condition {
    Condition {
        span,
        kind: ConditionKind::Comparison {
            op: CmpOp::Eq,
            left: Term::Integer(0),
            right: Term::Integer(1),
        },
    }
}

fn rewrite(c: &Condition, scope: &mut Scope) -> Condition {
    let boxed = |c: &Condition, scope: &mut Scope| Box::new(rewrite(c, scope));
    let kind = match &c.kind {
        ConditionKind::And { left, right } => ConditionKind::And {
            left: boxed(left, scope),
            right: boxed(right, scope),
        },
        ConditionKind::Or { left, right } => ConditionKind::Or {
            left: boxed(left, scope),
            right: boxed(right, scope),
        },
        ConditionKind::Not { inner } => ConditionKind::Not {
            inner: boxed(inner, scope),
        },
        ConditionKind::Formerly { within, body } => ConditionKind::Formerly {
            within: within.clone(),
            body: boxed(body, scope),
        },
        ConditionKind::Previous { within, body } => ConditionKind::Previous {
            within: within.clone(),
            body: boxed(body, scope),
        },
        ConditionKind::Since {
            left,
            within,
            right,
        } => ConditionKind::Since {
            left: boxed(left, scope),
            within: within.clone(),
            right: boxed(right, scope),
        },
        ConditionKind::Exists { var, body } => {
            scope.push(binding(var));
            let body = boxed(body, scope);
            scope.pop();
            ConditionKind::Exists {
                var: var.clone(),
                body,
            }
        }
        ConditionKind::Comparison { op, left, right } => {
            let left = rewrite_term(left, scope);
            let right = rewrite_term(right, scope);
            let orders = matches!(op, CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge);
            let computes =
                computes_with_timepoint(&left, scope) || computes_with_timepoint(&right, scope);
            if computes
                || (orders && (is_timepoint_var(&left, scope) || is_timepoint_var(&right, scope)))
            {
                return constant_false(c.span);
            }
            ConditionKind::Comparison {
                op: *op,
                left,
                right,
            }
        }
        other => other.clone(),
    };
    Condition { span: c.span, kind }
}

fn rewrite_term(t: &Term, scope: &mut Scope) -> Term {
    match t {
        Term::Agg(agg) => Term::Agg(Box::new(rewrite_agg(agg, scope))),
        Term::Arith { op, left, right } => Term::Arith {
            op: *op,
            left: Box::new(rewrite_term(left, scope)),
            right: Box::new(rewrite_term(right, scope)),
        },
        other => other.clone(),
    }
}

fn rewrite_agg(agg: &AggExpr, scope: &mut Scope) -> AggExpr {
    let kind = match &agg.kind {
        AggExprKind::Count { for_vars, body } => {
            let depth = scope.len();
            scope.extend(for_vars.iter().map(binding));
            let body = Box::new(rewrite(body, scope));
            scope.truncate(depth);
            AggExprKind::Count {
                for_vars: for_vars.clone(),
                body,
            }
        }
        AggExprKind::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            let depth = scope.len();
            scope.extend(for_vars.iter().map(binding));
            let body = Box::new(rewrite(body, scope));
            scope.truncate(depth);
            AggExprKind::Sum {
                bound_var: bound_var.clone(),
                for_vars: for_vars.clone(),
                body,
            }
        }
        AggExprKind::Call(call) => AggExprKind::Call(call.clone()),
    };
    AggExpr {
        span: agg.span,
        kind,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extension::temporal::parse::parse_condition;

    fn normalized(src: &str) -> Condition {
        unorder_timepoints(&parse_condition(src).expect("parses"))
    }

    fn has_comparison(c: &Condition, wanted: &dyn Fn(&CmpOp, &Term, &Term) -> bool) -> bool {
        match &c.kind {
            ConditionKind::And { left, right }
            | ConditionKind::Or { left, right }
            | ConditionKind::Since { left, right, .. } => {
                has_comparison(left, wanted) || has_comparison(right, wanted)
            }
            ConditionKind::Not { inner }
            | ConditionKind::Formerly { body: inner, .. }
            | ConditionKind::Previous { body: inner, .. }
            | ConditionKind::Exists { body: inner, .. } => has_comparison(inner, wanted),
            ConditionKind::Comparison { op, left, right } => wanted(op, left, right),
            _ => false,
        }
    }

    fn is_false(op: &CmpOp, l: &Term, r: &Term) -> bool {
        *op == CmpOp::Eq && *l == Term::Integer(0) && *r == Term::Integer(1)
    }

    #[test]
    fn an_ordering_of_timepoints_is_false() {
        let c = normalized(
            r#"exists (s: Timepoint). exists (t: Timepoint). (
                formerly within 1h (A::Action::"X"::request{ u: _ } && tp(s))
                && formerly within 1h (A::Action::"Y"::request{ u: _ } && tp(t))
                && s < t)"#,
        );
        assert!(has_comparison(&c, &is_false));
        assert!(!has_comparison(&c, &|op, _, _| *op == CmpOp::Lt));
    }

    #[test]
    fn an_equality_of_timepoints_is_kept() {
        let c = normalized(
            r#"exists (s: Timepoint). exists (t: Timepoint). (
                formerly within 1h (A::Action::"X"::request{ u: _ } && tp(s))
                && formerly within 1h (A::Action::"Y"::request{ u: _ } && tp(t))
                && s == t)"#,
        );
        assert!(!has_comparison(&c, &is_false));
    }

    #[test]
    fn an_ordering_of_longs_is_kept() {
        let c = normalized(
            r#"exists (n: Long). (formerly within 1h A::Action::"X"::request{ n: n } && n < 5)"#,
        );
        assert!(!has_comparison(&c, &is_false));
        assert!(has_comparison(&c, &|op, _, _| *op == CmpOp::Lt));
    }

    #[test]
    fn a_rebound_name_follows_the_innermost_binder() {
        // The outer `t` is a timepoint; the inner `t` is a `Long`, so the
        // ordering inside the inner scope compares two integers.
        let c = normalized(
            r#"exists (t: Timepoint). (formerly within 1h (A::Action::"X"::request{ u: _ } && tp(t))
                && exists (t: Long). (formerly within 1h A::Action::"Y"::request{ n: t } && t < 5))"#,
        );
        assert!(!has_comparison(&c, &is_false));
    }
}
