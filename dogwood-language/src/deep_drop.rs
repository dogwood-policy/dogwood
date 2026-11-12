//! Non-recursive destruction for the surface trees.
//!
//! The parser builds chain shapes (`a && b && …`, `x.a.b.…`, `!!!x`) with
//! loops, so a tree far deeper than
//! [`ParseOptions::max_depth`](crate::ParseOptions::max_depth) can
//! exist briefly before the measured check on the finished root rejects it.
//! A derived `Drop` frees a tree with one nested call per level and
//! overflows the stack on exactly the inputs the limit exists to refuse.
//!
//! These `Drop` impls use the standard iterative pattern instead (see "Too
//! Many Linked Lists", chapter "Drop"): hoist each node's owning pointers
//! out of the node and into a worklist, then free nodes off the worklist in
//! a loop. Hoisting means `mem::replace`: a node's `kind` field (which has
//! no `Drop` of its own) is swapped for a cheap leaf, the old kind is taken
//! apart, and its child `Box`es move onto the worklist as plain pointers.
//! When the worklist later frees a node, that node's kind has already been
//! taken, so its own `Drop` sees a leaf and returns at once — the re-entry
//! is constant-depth and the whole teardown runs in constant stack.
//!
//! Two departures from the pure pointer form, both bounded:
//! - Children stored by value (set/record/argument elements) move onto the
//!   worklist as values, since they have no box to hoist.
//! - `Term` is itself the enum with the `Drop` impl, with no inner kind
//!   field, so a `Term` cannot be destructured by move. Its children are
//!   swapped out for leaves one at a time and pushed by value.

use crate::ast::{Expr, ExprKind};
use crate::error::Span;
use crate::extension::Extension;
use crate::extension::temporal::ast::{
    AggExpr, AggExprKind, Call, CallArg, Condition, ConditionKind, Sigil, Term,
};
use std::mem::{replace, take};

pub(crate) fn leaf_expr_kind() -> ExprKind {
    ExprKind::Var(cedar_policy_core::ast::Var::Principal)
}

pub(crate) fn leaf_cond_kind() -> ConditionKind {
    ConditionKind::SigilRef {
        sigil: Sigil::Param,
        name: String::new(),
    }
}

fn leaf_agg() -> AggExpr {
    AggExpr {
        span: Span::new(0, 0),
        kind: AggExprKind::Call(Call {
            span: Span::new(0, 0),
            name: String::new(),
            args: Vec::new(),
        }),
    }
}

/// Whether dropping this term recurses (into elements or an aggregate
/// body).
fn term_is_deep(t: &Term) -> bool {
    matches!(t, Term::Array(_) | Term::Agg(_))
}

impl Drop for Expr {
    fn drop(&mut self) {
        if matches!(
            self.kind,
            ExprKind::Lit(_) | ExprKind::Var(_) | ExprKind::Slot(_) | ExprKind::ParamRef { .. }
        ) {
            return;
        }
        let kind = replace(&mut self.kind, leaf_expr_kind());
        let mut work = Vec::new();
        scatter_expr(kind, &mut work);
        drain(work);
    }
}

impl Drop for Condition {
    fn drop(&mut self) {
        if matches!(
            self.kind,
            ConditionKind::Tp { .. } | ConditionKind::SigilRef { .. }
        ) {
            return;
        }
        let kind = replace(&mut self.kind, leaf_cond_kind());
        let mut work = Vec::new();
        scatter_cond(kind, &mut work);
        drain(work);
    }
}

impl Drop for Term {
    fn drop(&mut self) {
        if !term_is_deep(self) {
            return;
        }
        let mut work = Vec::new();
        scatter_term(self, &mut work);
        drain(work);
        // `self` now holds only leaves; the compiler's field cleanup after
        // this function frees them without meaningful recursion.
    }
}

/// One worklist entry. Chain spines travel as hoisted owning pointers
/// (8 bytes); only elements that are stored by value travel as values.
enum Node {
    Expr(Box<Expr>),
    Cond(Box<Condition>),
    ExprVal(Expr),
    CondVal(Condition),
    TermVal(Term),
}

/// Free every entry: take the node's kind (leaving a leaf), scatter the
/// kind's children onto the worklist, and let the emptied node drop
/// shallowly.
fn drain(mut work: Vec<Node>) {
    while let Some(node) = work.pop() {
        match node {
            Node::Expr(mut b) => {
                let kind = replace(&mut b.kind, leaf_expr_kind());
                scatter_expr(kind, &mut work);
            }
            Node::ExprVal(mut e) => {
                let kind = replace(&mut e.kind, leaf_expr_kind());
                scatter_expr(kind, &mut work);
            }
            Node::Cond(mut b) => {
                let kind = replace(&mut b.kind, leaf_cond_kind());
                scatter_cond(kind, &mut work);
            }
            Node::CondVal(mut c) => {
                let kind = replace(&mut c.kind, leaf_cond_kind());
                scatter_cond(kind, &mut work);
            }
            Node::TermVal(mut t) => scatter_term(&mut t, &mut work),
        }
    }
}

/// Move every child out of a taken kind onto the worklist. Boxed children
/// move as pointers; value children move as values; everything else in the
/// kind drops here, shallowly.
fn scatter_expr(kind: ExprKind, work: &mut Vec<Node>) {
    match kind {
        ExprKind::Lit(_) | ExprKind::Var(_) | ExprKind::Slot(_) | ExprKind::ParamRef { .. } => {}
        ExprKind::Extension(Extension::Temporal(t)) => work.push(Node::CondVal(t.condition)),
        ExprKind::UnaryApp { expr, .. }
        | ExprKind::GetAttr { expr, .. }
        | ExprKind::HasAttr { expr, .. }
        | ExprKind::Like { expr, .. } => work.push(Node::Expr(expr)),
        ExprKind::BinaryApp { left, right, .. } => {
            work.push(Node::Expr(left));
            work.push(Node::Expr(right));
        }
        ExprKind::Is { expr, in_expr, .. } => {
            work.push(Node::Expr(expr));
            if let Some(in_expr) = in_expr {
                work.push(Node::Expr(in_expr));
            }
        }
        ExprKind::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => {
            work.push(Node::Expr(cond));
            work.push(Node::Expr(then_expr));
            work.push(Node::Expr(else_expr));
        }
        ExprKind::Set(elems) | ExprKind::Call { args: elems, .. } => {
            work.extend(elems.into_iter().map(Node::ExprVal));
        }
        ExprKind::Record(map) => work.extend(map.into_values().map(Node::ExprVal)),
        ExprKind::MethodCall { receiver, args, .. } => {
            work.push(Node::Expr(receiver));
            work.extend(args.into_iter().map(Node::ExprVal));
        }
    }
}

fn scatter_cond(kind: ConditionKind, work: &mut Vec<Node>) {
    match kind {
        ConditionKind::And { left, right }
        | ConditionKind::Or { left, right }
        | ConditionKind::Since { left, right, .. } => {
            work.push(Node::Cond(left));
            work.push(Node::Cond(right));
        }
        ConditionKind::Not { inner: body }
        | ConditionKind::Formerly { body, .. }
        | ConditionKind::Previous { body, .. }
        | ConditionKind::Exists { body, .. } => work.push(Node::Cond(body)),
        ConditionKind::Predicate(p) => {
            work.extend(p.args.into_iter().map(|a| Node::TermVal(a.value)));
        }
        ConditionKind::Comparison { left, right, .. } => {
            work.push(Node::TermVal(left));
            work.push(Node::TermVal(right));
        }
        ConditionKind::Call(call) => scatter_call(call, work),
        ConditionKind::Refine { base, fields, .. } => {
            work.push(Node::Cond(base));
            work.extend(fields.into_iter().map(|a| Node::TermVal(a.value)));
        }
        ConditionKind::Tp { .. } | ConditionKind::SigilRef { .. } => {}
    }
}

fn scatter_call(call: Call, work: &mut Vec<Node>) {
    for arg in call.args {
        match arg {
            CallArg::Condition(c) => work.push(Node::CondVal(c)),
            CallArg::Term(t) => work.push(Node::TermVal(t)),
            CallArg::Within(_) => {}
        }
    }
}

/// `Term` has the `Drop` impl itself, so it cannot be destructured by move;
/// its children are swapped out for leaves and pushed by value. Leaf
/// children drop right here (their `Drop` returns at once), so the shell
/// that remains holds only leaves.
fn scatter_term(t: &mut Term, work: &mut Vec<Node>) {
    match t {
        Term::Array(items) => {
            work.extend(take(items).into_iter().filter(term_is_deep).map(Node::TermVal));
        }
        Term::Agg(b) => {
            let agg = replace(&mut **b, leaf_agg());
            match agg.kind {
                AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => {
                    work.push(Node::Cond(body));
                }
                AggExprKind::Call(call) => scatter_call(call, work),
            }
        }
        _ => {}
    }
}
