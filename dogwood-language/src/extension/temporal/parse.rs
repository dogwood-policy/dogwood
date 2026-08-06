//! Parser for the temporal sub-language: the body of a
//! `temporal { … }` marker block → a temporal [`Condition`] AST.
//!
//! The grammar (`grammar.pest`) is walked by hand. Spans are byte
//! ranges into the block body; the caller (`Temporal::parse`) records
//! a base offset so they can be rebased into the original `.dw`.

use pest::Parser;
use pest_derive::Parser;

use super::ast::{
    AggExpr, AggExprKind, BinderSlot, Call, CallArg, CmpOp, Condition, ConditionKind, Interval,
    NamedArg, Predicate, Term, TimeUnit, Type, TypedBinder, WithinSpec,
};
use crate::error::Span;

#[derive(Parser)]
#[grammar = "extension/temporal/grammar.pest"]
struct TemporalParser;

type Pair<'i> = pest::iterators::Pair<'i, Rule>;

fn span_of(p: &Pair<'_>) -> Span {
    let s = p.as_span();
    Span::new(s.start(), s.end())
}

/// Parse a temporal condition body into a [`Condition`].
pub fn parse_condition(body: &str) -> Result<Condition, String> {
    let mut pairs = TemporalParser::parse(Rule::condition_entry, body)
        .map_err(|e| enhance_temporal_error(&e, body))?;
    let entry = pairs.next().expect("condition_entry yields one pair");
    let cond = entry
        .into_inner()
        .find(|p| p.as_rule() == Rule::condition)
        .expect("condition_entry contains a condition");
    Ok(build_condition(cond))
}

/// Parse a `def temporal` macro body. The body is either a bare
/// aggregation expression (in which case the macro is callable as an
/// aggregate value — a comparison operand, e.g.
/// `(my_agg(...)) == n`) or a temporal condition.
pub fn parse_macro_body(body: &str) -> Result<crate::ast::MacroBody, String> {
    let mut pairs = TemporalParser::parse(Rule::temporal_macro_body_entry, body)
        .map_err(|e| enhance_temporal_error(&e, body))?;
    let entry = pairs
        .next()
        .expect("temporal_macro_body_entry yields one pair");
    let inner = entry
        .into_inner()
        .find(|p| matches!(p.as_rule(), Rule::agg_expr | Rule::condition))
        .expect("temporal_macro_body_entry contains an agg_expr or condition");
    match inner.as_rule() {
        Rule::agg_expr => Ok(crate::ast::MacroBody::TemporalAgg(build_agg_expr(inner))),
        Rule::condition => Ok(crate::ast::MacroBody::TemporalCondition(build_condition(
            inner,
        ))),
        other => unreachable!("unexpected temporal macro body child: {other:?}"),
    }
}

/// `condition = conjunct_or_since ("&&" conjunct_or_since)*` —
/// left-associative And.
fn build_condition(pair: Pair<'_>) -> Condition {
    let mut iter = pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::conjunct_or_since);
    let mut acc = build_conjunct_or_since(iter.next().expect("at least one conjunct_or_since"));
    for next in iter {
        let right = build_conjunct_or_since(next);
        let s = Span::new(acc.span.start, right.span.end);
        acc = Condition {
            span: s,
            kind: ConditionKind::And {
                left: Box::new(acc),
                right: Box::new(right),
            },
        };
    }
    acc
}

/// `conjunct_or_since = neg_conjunct ("since" within atom)?`.
fn build_conjunct_or_since(pair: Pair<'_>) -> Condition {
    let span = span_of(&pair);
    let mut inner = pair.into_inner().peekable();
    let left = build_neg_conjunct(inner.next().expect("neg_conjunct"));

    // Optional `since within <atom>`.
    let mut within: Option<WithinSpec> = None;
    let mut right: Option<Condition> = None;
    for p in inner {
        match p.as_rule() {
            Rule::within => within = Some(build_within(p)),
            Rule::atom => right = Some(build_atom(p)),
            _ => {}
        }
    }

    match (within, right) {
        (Some(within), Some(right)) => Condition {
            span,
            kind: ConditionKind::Since {
                left: Box::new(left),
                within,
                right: Box::new(right),
            },
        },
        _ => left,
    }
}

/// `neg_conjunct = bang* conjunct` — wrap the conjunct in one `Not` per
/// leading `!`. An even count of `!` cancels to the bare conjunct
/// (double negation); the span of each wrapper covers the `!` prefix
/// through the conjunct.
///
/// The negation count is the number of `bang` children — counting parse
/// nodes (not source characters) is robust against whitespace or a line
/// comment appearing between consecutive `!`s, and a `!` that sits inside
/// such a comment is consumed by the silent COMMENT rule and never
/// becomes a `bang` node.
fn build_neg_conjunct(pair: Pair<'_>) -> Condition {
    let span = span_of(&pair);
    let mut bangs = 0usize;
    let mut conjunct = None;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::bang => bangs += 1,
            Rule::conjunct => conjunct = Some(p),
            _ => {}
        }
    }
    let conjunct = conjunct.expect("neg_conjunct has a conjunct child");
    let mut node = build_conjunct(conjunct);
    for _ in 0..bangs {
        node = Condition {
            span,
            kind: ConditionKind::Not {
                inner: Box::new(node),
            },
        };
    }
    node
}

/// `conjunct = comparison | parenthesized | temporal_op | exists_op
///            | tp_op | call | refinable`.
fn build_conjunct(pair: Pair<'_>) -> Condition {
    let inner = pair.into_inner().next().expect("conjunct has one child");
    build_node(inner)
}

/// `atom = "(" condition ")" | tp_op | call | refinable | comparison`.
fn build_atom(pair: Pair<'_>) -> Condition {
    let inner = pair.into_inner().next().expect("atom has one child");
    build_node(inner)
}

/// Dispatch a single condition-producing node by rule.
fn build_node(pair: Pair<'_>) -> Condition {
    let span = span_of(&pair);
    match pair.as_rule() {
        Rule::parenthesized => {
            let cond = pair
                .into_inner()
                .find(|p| p.as_rule() == Rule::condition)
                .expect("parenthesized wraps a condition");
            build_condition(cond)
        }
        Rule::condition => build_condition(pair),
        Rule::temporal_op => build_temporal_op(pair),
        Rule::predicate => Condition {
            span,
            kind: ConditionKind::Predicate(build_predicate(pair)),
        },
        Rule::exists_op => build_exists(pair, span),
        Rule::tp_op => build_tp(pair, span),
        Rule::call => Condition {
            span,
            kind: ConditionKind::Call(build_call(pair, span)),
        },
        Rule::sigil_cond => build_sigil_cond(pair, span),
        Rule::refinable => build_refinable(pair, span),
        Rule::comparison => build_comparison(pair, span),
        other => unreachable!("unexpected condition node: {other:?}"),
    }
}

/// `sigil_cond = param_ref` — only a `?p` macro-parameter reference can
/// stand for a whole condition. (A `$t` binder reference is not
/// admissible here: a bare binder name is not a condition, so
/// `binder_ref` is not part of `sigil_cond`.)
fn build_sigil_cond(pair: Pair<'_>, span: Span) -> Condition {
    let inner = pair.into_inner().next().expect("sigil_cond has a child");
    let (sigil, name) = match inner.as_rule() {
        Rule::param_ref => (
            super::ast::Sigil::Param,
            inner.as_str().trim_start_matches('?').to_string(),
        ),
        other => unreachable!("unexpected sigil_cond child: {other:?}"),
    };
    Condition {
        span,
        kind: ConditionKind::SigilRef { sigil, name },
    }
}

/// `refinable = (predicate | sigil_cond) field_block*` — a predicate or
/// condition-sigil optionally refined by trailing field-injection blocks.
///
/// With zero `field_block`s the base is returned unchanged (a plain
/// `Predicate` / `SigilRef`), so nothing that predates field injection
/// sees a new node. With one or more blocks the injected named args are
/// concatenated (chaining `{a}{b}` ≡ `{a, b}`) and wrapped in a single
/// [`ConditionKind::Refine`] over the base; the macro expansion pass folds
/// that into the base predicate's args.
fn build_refinable(pair: Pair<'_>, span: Span) -> Condition {
    let mut base: Option<Condition> = None;
    let mut fields: Vec<NamedArg> = Vec::new();
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::predicate => {
                let s = span_of(&p);
                base = Some(Condition {
                    span: s,
                    kind: ConditionKind::Predicate(build_predicate(p)),
                });
            }
            Rule::sigil_cond => {
                let s = span_of(&p);
                base = Some(build_sigil_cond(p, s));
            }
            Rule::field_block => {
                if let Some(list) = p.into_inner().find(|c| c.as_rule() == Rule::named_arg_list) {
                    fields.extend(build_named_args(list));
                }
            }
            _ => {}
        }
    }
    let base = base.expect("refinable has a predicate or sigil_cond base");
    if fields.is_empty() {
        base
    } else {
        Condition {
            span,
            kind: ConditionKind::Refine {
                base: Box::new(base),
                fields,
                span,
            },
        }
    }
}

/// `temporal_op = once_op | previous_op`.
fn build_temporal_op(pair: Pair<'_>) -> Condition {
    let op = pair.into_inner().next().expect("temporal_op child");
    let span = span_of(&op);
    let is_previous = op.as_rule() == Rule::previous_op;
    let mut within: Option<WithinSpec> = None;
    let mut body = None;
    for p in op.into_inner() {
        match p.as_rule() {
            Rule::within => within = Some(build_within(p)),
            Rule::atom => body = Some(build_atom(p)),
            _ => {}
        }
    }
    let within = within.expect("temporal op has within");
    let body = Box::new(body.expect("temporal op has body"));
    Condition {
        span,
        kind: if is_previous {
            ConditionKind::Previous { within, body }
        } else {
            ConditionKind::Formerly { within, body }
        },
    }
}

/// `predicate = qualified_action "::" event_kind "{" named_arg_list? "}"`.
fn build_predicate(pair: Pair<'_>) -> Predicate {
    let span = span_of(&pair);
    let mut namespace = Vec::new();
    let mut action = String::new();
    let mut kind = String::new();
    let mut args = Vec::new();
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::qualified_action => {
                (namespace, action) = build_qualified_action(&p);
            }
            Rule::event_kind => kind = p.as_str().to_string(),
            Rule::named_arg_list => args = build_named_args(p),
            _ => {}
        }
    }
    Predicate {
        span,
        namespace,
        action,
        kind,
        args,
    }
}

/// Split a `qualified_action` pair `(ident "::")* "::" string` into its
/// namespace path and quoted action id.
fn build_qualified_action(qa: &Pair<'_>) -> (Vec<String>, String) {
    let mut namespace = Vec::new();
    let mut action = String::new();
    for p in qa.clone().into_inner() {
        match p.as_rule() {
            Rule::ident => namespace.push(p.as_str().to_string()),
            Rule::string => action = unquote(p.as_str()),
            _ => {}
        }
    }
    (namespace, action)
}

fn build_named_args(pair: Pair<'_>) -> Vec<NamedArg> {
    let mut args = Vec::new();
    for na in pair.into_inner().filter(|p| p.as_rule() == Rule::named_arg) {
        let mut name = String::new();
        let mut value = Term::Wildcard;
        for p in na.into_inner() {
            match p.as_rule() {
                // The field name is a dotted path (`input.user`); keep it
                // as the dotted string — `NamedArg::field_path` splits it
                // for lookup, and matching descends nested records.
                Rule::field_path => name = build_field_path(&p),
                Rule::term => value = build_term(p),
                _ => {}
            }
        }
        args.push(NamedArg { name, value });
    }
    args
}

/// `field_path = ident ("." ident)*` — render back to the dotted string
/// stored on [`NamedArg::name`].
fn build_field_path(pair: &Pair<'_>) -> String {
    pair.clone()
        .into_inner()
        .filter(|p| p.as_rule() == Rule::ident)
        .map(|p| p.as_str().to_string())
        .collect::<Vec<_>>()
        .join(".")
}

/// `exists_op = "exists" typed_binder "." condition`. Builds a
/// [`ConditionKind::Exists`] whose body is the full trailing condition
/// (greedy-right scope).
fn build_exists(pair: Pair<'_>, span: Span) -> Condition {
    let mut var: Option<TypedBinder> = None;
    let mut body: Option<Condition> = None;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::typed_binder => var = Some(build_typed_binder(p)),
            Rule::condition => body = Some(build_condition(p)),
            _ => {}
        }
    }
    Condition {
        span,
        kind: ConditionKind::Exists {
            var: var.expect("exists has a typed binder"),
            body: Box::new(body.expect("exists has a body")),
        },
    }
}

/// `agg_expr = sum_expr | count_expr | call` — the value half of a `let`.
pub(super) fn build_agg_expr(pair: Pair<'_>) -> AggExpr {
    let span = span_of(&pair);
    let inner = pair.into_inner().next().expect("agg_expr has a child");
    let kind = match inner.as_rule() {
        Rule::sum_expr => build_sum_expr(inner),
        Rule::count_expr => build_count_expr(inner),
        Rule::call => {
            let call_span = span_of(&inner);
            AggExprKind::Call(build_call(inner, call_span))
        }
        other => unreachable!("unexpected agg_expr child: {other:?}"),
    };
    AggExpr { span, kind }
}

/// `sum_expr = "sum" binder_slot for_binders "where" condition`.
fn build_sum_expr(pair: Pair<'_>) -> AggExprKind {
    let mut bound_var: Option<BinderSlot> = None;
    let mut for_vars: Vec<TypedBinder> = Vec::new();
    let mut body: Option<Condition> = None;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::binder_slot => bound_var = Some(build_binder_slot(p)),
            Rule::for_binders => for_vars = build_for_binders(p),
            Rule::condition => body = Some(build_condition(p)),
            _ => {}
        }
    }
    AggExprKind::Sum {
        bound_var: bound_var.expect("sum_expr has a bound_var binder_slot"),
        for_vars,
        body: Box::new(body.expect("sum_expr has a body")),
    }
}

/// `count_expr = "count" for_binders "where" condition`.
fn build_count_expr(pair: Pair<'_>) -> AggExprKind {
    let mut for_vars: Vec<TypedBinder> = Vec::new();
    let mut body: Option<Condition> = None;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::for_binders => for_vars = build_for_binders(p),
            Rule::condition => body = Some(build_condition(p)),
            _ => {}
        }
    }
    AggExprKind::Count {
        for_vars,
        body: Box::new(body.expect("count_expr has a body")),
    }
}

/// `for_binders = "for" typed_binder ("," typed_binder)* "."` — the
/// explicit domain, each element a typed declaration-site binder.
fn build_for_binders(pair: Pair<'_>) -> Vec<TypedBinder> {
    pair.into_inner()
        .filter(|p| p.as_rule() == Rule::typed_binder)
        .map(build_typed_binder)
        .collect()
}

/// `typed_binder = "(" binder_slot ":" type_expr ")"` — a declaration-site
/// binder with its mandatory type annotation.
fn build_typed_binder(pair: Pair<'_>) -> TypedBinder {
    let mut slot: Option<BinderSlot> = None;
    let mut ty: Option<Type> = None;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::binder_slot => slot = Some(build_binder_slot(p)),
            Rule::type_expr => ty = Some(build_temporal_type(&p)),
            _ => {}
        }
    }
    TypedBinder {
        slot: slot.expect("typed_binder has a binder_slot"),
        ty: ty.expect("typed_binder has a type_expr"),
    }
}

/// `type_expr = ident ("::" ident)*` — a binder's type annotation. The
/// reserved word `Timepoint` (a single unqualified segment) maps to
/// [`Type::Timepoint`]; any other path is a [`Type::Named`] concrete or
/// entity type. Types are carried but not yet checked against the schema.
fn build_temporal_type(pair: &Pair<'_>) -> Type {
    let path: Vec<String> = pair
        .clone()
        .into_inner()
        .filter(|p| p.as_rule() == Rule::ident)
        .map(|p| p.as_str().to_string())
        .collect();
    if path.len() == 1 && path[0] == "Timepoint" {
        Type::Timepoint
    } else {
        Type::Named(path)
    }
}

/// `binder_slot = param_ref | binder_ref | ident`.
fn build_binder_slot(pair: Pair<'_>) -> BinderSlot {
    let inner = pair.into_inner().next().expect("binder_slot has a child");
    match inner.as_rule() {
        Rule::param_ref => BinderSlot::ParamRef(inner.as_str().trim_start_matches('?').to_string()),
        Rule::binder_ref => {
            BinderSlot::BinderRef(inner.as_str().trim_start_matches('$').to_string())
        }
        Rule::ident => BinderSlot::Name(inner.as_str().to_string()),
        other => unreachable!("unexpected binder_slot child: {other:?}"),
    }
}

/// `tp_op = "tp" "(" binder_slot ")"`.
fn build_tp(pair: Pair<'_>, span: Span) -> Condition {
    let var = pair
        .into_inner()
        .find(|p| p.as_rule() == Rule::binder_slot)
        .map(build_binder_slot)
        .unwrap_or_else(|| BinderSlot::Name(String::new()));
    Condition {
        span,
        kind: ConditionKind::Tp { var },
    }
}

/// `call = ident "(" call_arg_list? ")"`.
fn build_call(pair: Pair<'_>, span: Span) -> Call {
    let mut name = String::new();
    let mut args = Vec::new();
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::ident => name = p.as_str().to_string(),
            Rule::call_arg_list => {
                for arg in p.into_inner().filter(|p| p.as_rule() == Rule::call_arg) {
                    args.push(build_call_arg(arg));
                }
            }
            _ => {}
        }
    }
    Call { span, name, args }
}

/// `call_arg = interval_lit | condition | term` — try in grammar order.
/// A window argument is a bare interval (`1h`), not a `within …` clause.
fn build_call_arg(pair: Pair<'_>) -> CallArg {
    let inner = pair.into_inner().next().expect("call_arg has a child");
    match inner.as_rule() {
        Rule::interval_lit => CallArg::Within(build_interval_lit(inner)),
        Rule::condition => CallArg::Condition(build_condition(inner)),
        Rule::term => CallArg::Term(build_term(inner)),
        other => unreachable!("unexpected call_arg child: {other:?}"),
    }
}

/// `comparison = term cmp_op term`. Either term may be an aggregate
/// (`Term::Agg`); the comparison-operand-only rule is checked by `check`.
fn build_comparison(pair: Pair<'_>, span: Span) -> Condition {
    let mut terms = Vec::new();
    let mut op = CmpOp::Eq;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::term => terms.push(build_term(p)),
            Rule::cmp_op => {
                op = match p.as_str() {
                    "<=" => CmpOp::Le,
                    "<" => CmpOp::Lt,
                    ">=" => CmpOp::Ge,
                    ">" => CmpOp::Gt,
                    "==" => CmpOp::Eq,
                    "!=" => CmpOp::NotEq,
                    _ => CmpOp::Eq,
                }
            }
            _ => {}
        }
    }
    let mut it = terms.into_iter();
    let left = it.next().expect("comparison left");
    let right = it.next().expect("comparison right");
    Condition {
        span,
        kind: ConditionKind::Comparison { op, left, right },
    }
}

/// `within = "within" within_payload`. The payload is either a
/// concrete `integer time_unit` pair (the user-facing form) or a macro
/// `?w` reference (only legal inside a macro body; resolved by the
/// expander).
fn build_within(pair: Pair<'_>) -> WithinSpec {
    let payload = pair
        .into_inner()
        .find(|p| p.as_rule() == Rule::within_payload)
        .expect("within has a within_payload");
    let mut amount = 0;
    let mut unit = TimeUnit::Seconds;
    let mut sigil: Option<String> = None;
    for p in payload.into_inner() {
        match p.as_rule() {
            Rule::integer => amount = p.as_str().parse().unwrap_or(0),
            Rule::time_unit => unit = TimeUnit::from_token(p.as_str()).unwrap_or(TimeUnit::Seconds),
            Rule::param_ref => sigil = Some(p.as_str().trim_start_matches('?').to_string()),
            _ => {}
        }
    }
    match sigil {
        Some(name) => WithinSpec::ParamRef(name),
        None => WithinSpec::Concrete(Interval { amount, unit }),
    }
}

/// Build a concrete `Interval` from an `interval_lit` (`integer
/// time_unit`), the bare-interval form a macro call site uses to supply a
/// window argument (e.g. `once(1h, …)`). Unlike the `within` clause used
/// by the temporal operators, there is no `within` keyword and no `?w`
/// sigil here — a call-site window is always concrete.
fn build_interval_lit(pair: Pair<'_>) -> Interval {
    let mut amount = 0;
    let mut unit = TimeUnit::Seconds;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::integer => amount = p.as_str().parse().unwrap_or(0),
            Rule::time_unit => unit = TimeUnit::from_token(p.as_str()).unwrap_or(TimeUnit::Seconds),
            _ => {}
        }
    }
    Interval { amount, unit }
}

fn build_term(pair: Pair<'_>) -> Term {
    let inner = pair.into_inner().next();
    match inner.as_ref().map(|p| p.as_rule()) {
        Some(Rule::entity) => {
            let p = inner.unwrap();
            let mut segs = Vec::new();
            let mut id = String::new();
            for c in p.into_inner() {
                match c.as_rule() {
                    Rule::ident => segs.push(c.as_str().to_string()),
                    Rule::string => id = unquote(c.as_str()),
                    _ => {}
                }
            }
            Term::Entity {
                ty: segs.join("::"),
                id,
            }
        }
        Some(Rule::decimal_lit) => {
            let p = inner.unwrap();
            let s = p
                .into_inner()
                .find(|c| c.as_rule() == Rule::string)
                .map(|c| unquote(c.as_str()))
                .unwrap_or_default();
            Term::Decimal(s)
        }
        // A bare or parenthesized aggregate term (`count …` / `(count …)`).
        // The parens (`paren_agg`) carry no semantics — they only fence the
        // greedy `where` body off a trailing `== n`.
        Some(Rule::agg_expr) => Term::Agg(Box::new(build_agg_expr(inner.unwrap()))),
        Some(Rule::paren_agg) => {
            let agg = inner
                .unwrap()
                .into_inner()
                .find(|c| c.as_rule() == Rule::agg_expr)
                .expect("paren_agg wraps an agg_expr");
            Term::Agg(Box::new(build_agg_expr(agg)))
        }
        Some(Rule::integer) => Term::Integer(inner.unwrap().as_str().parse().unwrap_or(0)),
        Some(Rule::string) => Term::String(unquote(inner.unwrap().as_str())),
        Some(Rule::kw_true) => Term::Bool(true),
        Some(Rule::kw_false) => Term::Bool(false),
        Some(Rule::array) => {
            let p = inner.unwrap();
            Term::Array(
                p.into_inner()
                    .filter(|c| c.as_rule() == Rule::term)
                    .map(build_term)
                    .collect(),
            )
        }
        Some(Rule::context_field) => {
            let p = inner.unwrap();
            let path: Vec<String> = p
                .into_inner()
                .filter(|c| c.as_rule() == Rule::ident)
                .map(|c| c.as_str().to_string())
                .collect();
            Term::ContextField(path)
        }
        // `principal` / `resource` (± an attribute tail). The `scope_root`
        // (`principal` / `resource`) is the path head; the trailing `ident`s
        // are the attribute path, so `principal.address.zone` becomes
        // `["principal", "address", "zone"]` and a bare `principal` is
        // `["principal"]`.
        Some(Rule::scope_field) => {
            let p = inner.unwrap();
            let path: Vec<String> = p
                .into_inner()
                .filter(|c| matches!(c.as_rule(), Rule::scope_root | Rule::ident))
                .map(|c| c.as_str().to_string())
                .collect();
            Term::ScopeField(path)
        }
        Some(Rule::wildcard) => Term::Wildcard,
        Some(Rule::param_ref) => {
            Term::ParamRef(inner.unwrap().as_str().trim_start_matches('?').to_string())
        }
        Some(Rule::binder_ref) => {
            Term::BinderRef(inner.unwrap().as_str().trim_start_matches('$').to_string())
        }
        Some(Rule::ident) => {
            // A bare `_` is the wildcard (matches anything, binds
            // nothing). It lexes as an identifier rather than the `*`
            // wildcard token, but is semantically a wildcard: crucially,
            // each `_` is independent, so `P{a: _, b: _}` does NOT force
            // `a == b` (which a shared `Var("_")` binding would).
            let s = inner.unwrap().as_str();
            if s == "_" {
                Term::Wildcard
            } else {
                Term::Var(s.to_string())
            }
        }
        _ => Term::Wildcard,
    }
}

fn unquote(s: &str) -> String {
    s.trim_matches('"').to_string()
}

// ─── Removed-syntax detection ───────────────────────────────────────
//
// `let` is not a temporal keyword but users sometimes attempt a
// `let var = agg in …` binding pattern. Since the grammar has no `let`
// rule, pest sees it as an identifier (valid term start) and then
// chokes on the next token expecting a comparison operator — a
// confusing message. We detect this *after* the parse fails: only when
// the error position falls immediately after a standalone `let` word
// do we replace the message, so earlier genuine errors are not masked.

/// Format a temporal parse error, upgrading known confusing patterns to
/// actionable diagnostics. Falls back to `format_temporal_pest_error`.
fn enhance_temporal_error(e: &pest::error::Error<Rule>, src: &str) -> String {
    let pos = match e.location {
        pest::error::InputLocation::Pos(p) => p,
        pest::error::InputLocation::Span((s, _)) => s,
    };

    if is_after_let_keyword(src, pos) {
        return "`let` is not recognized; to bind an aggregation result, \
                use `exists (var: Type). ((count/sum …) == var && …)`"
            .to_string();
    }

    format_temporal_pest_error(e, src)
}

/// Check whether `pos` is right after a standalone `let` keyword.
/// For example, in `let total = …`, if `pos` points at `total`, then
/// the preceding non-whitespace is `let`.
fn is_after_let_keyword(src: &str, pos: usize) -> bool {
    let before = src[..pos].trim_end();
    if !before.ends_with("let") {
        return false;
    }
    // Ensure `let` is a complete word (not the tail of `outlet` etc.).
    let let_start = before.len() - 3;
    if let_start > 0 {
        let preceding_byte = before.as_bytes()[let_start - 1];
        if preceding_byte.is_ascii_alphanumeric() || preceding_byte == b'_' {
            return false;
        }
    }
    true
}

// ─── Human-readable temporal parse error translation ────────────────
//
// Mirrors the Cedar-side `format_pest_error` / `rule_display` /
// `extract_token` approach in `parser/mod.rs`. Every pest grammar rule
// maps to a short human-readable name; the raw pest error is translated
// into a Cedar-style message like
//   "unexpected token `foo`, expected temporal condition, event predicate"
// instead of the raw
//   "expected neg_conjunct, predicate, once_op"

/// Map a temporal grammar `Rule` to its human-readable display name.
fn temporal_rule_display(rule: &Rule) -> &'static str {
    match rule {
        // Entry points (should not normally appear in user-facing errors)
        Rule::condition_entry => "temporal condition",
        Rule::temporal_macro_body_entry => "temporal macro body",

        // Condition structure
        Rule::condition => "temporal condition",
        Rule::conjunct_or_since => "temporal condition",
        Rule::neg_conjunct => "temporal condition",
        Rule::bang => "'!'",
        Rule::conjunct => "temporal condition",
        Rule::sigil_cond => "macro parameter",
        Rule::refinable => "event predicate",
        Rule::field_block => "field injection block",
        Rule::parenthesized => "'('",

        // Temporal operators
        Rule::temporal_op => "'formerly' or 'previous'",
        Rule::once_op => "'formerly'",
        Rule::previous_op => "'previous'",
        Rule::atom => "temporal condition",

        // Exists
        Rule::exists_op => "'exists'",

        // Timepoint
        Rule::tp_op => "'tp'",

        // Predicates
        Rule::predicate => "event predicate",
        Rule::qualified_action => "qualified action",
        Rule::event_kind => "event kind",
        Rule::named_arg_list => "field binding",
        Rule::named_arg => "field binding",
        Rule::field_path => "field name",

        // Comparison
        Rule::comparison => "comparison",
        Rule::cmp_op => "comparison operator",

        // Aggregation
        Rule::agg_expr => "aggregation",
        Rule::sum_expr => "'sum'",
        Rule::count_expr => "'count'",
        Rule::for_binders => "'for' clause",
        Rule::typed_binder => "typed binder",
        Rule::type_expr => "type",

        // Windows
        Rule::within => "'within' clause",
        Rule::within_payload => "window interval",
        Rule::time_unit => "time unit ('s', 'm', 'h', or 'd')",

        // Macro calls
        Rule::call => "macro call",
        Rule::call_arg_list => "argument list",
        Rule::call_arg => "argument",
        Rule::interval_lit => "interval literal",

        // Terms
        Rule::term => "value",
        Rule::paren_agg => "'('",
        Rule::entity => "entity reference",
        Rule::decimal_lit => "'decimal(...)'",
        Rule::array => "'['",
        Rule::context_field => "'context' field",
        Rule::scope_field => "'principal' or 'resource'",
        Rule::scope_root => "'principal' or 'resource'",
        Rule::wildcard => "'*'",

        // Identifiers and literals
        Rule::ident => "identifier",
        Rule::integer => "integer",
        Rule::string => "string literal",
        Rule::kw_true => "'true'",
        Rule::kw_false => "'false'",

        // Macro sigils
        Rule::param_ref => "parameter reference",
        Rule::binder_ref => "binder reference",
        Rule::binder_slot => "binder",

        // Implicit / whitespace (should not appear in errors)
        Rule::WHITESPACE => "whitespace",
        Rule::COMMENT => "comment",
        Rule::EOI => "end of input",
    }
}

/// Deduplicate rule descriptions (many rules map to the same display string).
fn deduplicate_temporal_descriptions(rules: &[Rule]) -> Vec<&'static str> {
    let mut descs: Vec<&str> = rules.iter().map(|r| temporal_rule_display(r)).collect();
    descs.sort_unstable();
    descs.dedup();
    descs
}

/// Extract the token at `pos` in `src` for error messages. Returns `None`
/// at EOF. Grabs a meaningful token (identifier, keyword, number, string
/// start, or single punctuation character).
fn extract_temporal_token(src: &str, pos: usize) -> Option<String> {
    let remaining = src.get(pos..)?;
    if remaining.is_empty() {
        return None;
    }

    let first = remaining.chars().next()?;

    // Identifier / keyword: grab the whole word.
    if first.is_ascii_alphabetic() || first == '_' {
        let end = remaining
            .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .unwrap_or(remaining.len());
        return Some(remaining[..end].to_string());
    }

    // Macro parameter `?ident` or binder `$ident`.
    if first == '?' || first == '$' {
        let rest = &remaining[1..];
        let end = rest
            .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .unwrap_or(rest.len());
        return Some(remaining[..1 + end].to_string());
    }

    // Number: grab consecutive digits (may have leading `-`).
    if first.is_ascii_digit()
        || (first == '-' && remaining.len() > 1 && remaining.as_bytes()[1].is_ascii_digit())
    {
        let end = remaining[1..]
            .find(|c: char| !c.is_ascii_digit())
            .map(|i| i + 1)
            .unwrap_or(remaining.len());
        return Some(remaining[..end].to_string());
    }

    // String literal: show the opening quote + a prefix.
    if first == '"' {
        let close = remaining[1..].find('"').map(|i| i + 2);
        let end = close.unwrap_or_else(|| {
            // Unclosed string: truncate at ~20 bytes on a char boundary.
            remaining
                .char_indices()
                .take_while(|(i, _)| *i <= 20)
                .last()
                .map(|(i, c)| i + c.len_utf8())
                .unwrap_or(remaining.len())
                .min(remaining.len())
        });
        return Some(remaining[..end].to_string());
    }

    // Multi-character operators: `::`, `==`, `!=`, `<=`, `>=`, `&&`.
    if remaining.len() >= 2 && remaining.is_char_boundary(2) {
        let two = &remaining[..2];
        if matches!(two, "::" | "==" | "!=" | "<=" | ">=" | "&&") {
            return Some(two.to_string());
        }
    }

    // Single character (handles `{`, `}`, `(`, `)`, `<`, `>`, etc.).
    Some(first.to_string())
}

/// Format a temporal pest `Error<Rule>` into a human-readable error message,
/// matching the Cedar parser's style.
fn format_temporal_pest_error(e: &pest::error::Error<Rule>, src: &str) -> String {
    match &e.variant {
        pest::error::ErrorVariant::CustomError { message } => message.clone(),
        pest::error::ErrorVariant::ParsingError {
            positives,
            negatives,
        } => {
            let at_pos = match e.location {
                pest::error::InputLocation::Pos(p) => p,
                pest::error::InputLocation::Span((s, _)) => s,
            };
            let found_token = extract_temporal_token(src, at_pos);

            if !negatives.is_empty() {
                if let Some(token) = &found_token {
                    format!("unexpected token `{token}`")
                } else {
                    let neg_names = deduplicate_temporal_descriptions(negatives);
                    format!("unexpected {}", neg_names.join(", "))
                }
            } else if positives.is_empty() {
                if let Some(token) = &found_token {
                    format!("unexpected token `{token}`")
                } else {
                    "unexpected end of input".to_string()
                }
            } else {
                let descriptions = deduplicate_temporal_descriptions(positives);
                if let Some(token) = &found_token {
                    if descriptions.len() <= 3 {
                        format!(
                            "unexpected token `{token}`, expected {}",
                            descriptions.join(", ")
                        )
                    } else {
                        format!("unexpected token `{token}`")
                    }
                } else {
                    // At EOF
                    if descriptions.len() <= 3 {
                        format!(
                            "unexpected end of input, expected {}",
                            descriptions.join(", ")
                        )
                    } else {
                        "unexpected end of input".to_string()
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    //! Grammar/AST tests for the `!` conjunct-level negation operator
    //! that replaced `except` (`a except b` → `a && !b`) and the
    //! `without … since` form (`without X since …` → `!X since …`).
    //! These pin the precedence (`!` binds tighter than `since` and
    //! `&&`), double-negation cancellation, and — for good measure — that
    //! `!` negation is independent of the macro fresh-binder sigil `$t`
    //! (which uses a distinct character and lives only in binder/term
    //! positions).

    use super::*;

    fn parse(body: &str) -> Condition {
        parse_condition(body).unwrap_or_else(|e| panic!("parse `{body}` failed: {e}"))
    }

    fn pred(c: &Condition) -> &str {
        match &c.kind {
            ConditionKind::Predicate(p) => &p.action,
            other => panic!("expected predicate, got {other:?}"),
        }
    }

    #[test]
    fn bare_negation_wraps_a_not() {
        match &parse(r#"!Drupe::Action::"Logout"::request{}"#).kind {
            ConditionKind::Not { inner } => assert_eq!(pred(inner), "Logout"),
            other => panic!("expected Not, got {other:?}"),
        }
    }

    #[test]
    fn double_negation_nests_two_nots() {
        // Two leading `!` produce Not(Not(pred)) — semantics-preserving
        // double negation (the rewriter never emits this, but the
        // grammar must accept it and the evaluator cancels it).
        match &parse(r#"!!Drupe::Action::"Login"::request{}"#).kind {
            ConditionKind::Not { inner } => match &inner.kind {
                ConditionKind::Not { inner } => assert_eq!(pred(inner), "Login"),
                other => panic!("expected inner Not, got {other:?}"),
            },
            other => panic!("expected outer Not, got {other:?}"),
        }
    }

    #[test]
    fn negation_count_survives_whitespace_and_comments_between_bangs() {
        // The negation count is the number of `bang` parse nodes, NOT a
        // scan of source characters — so whitespace, newlines, and even a
        // line comment between consecutive `!`s must still count every
        // `!`. (A character-scan recovery would stop at the comment's `/`
        // and undercount, silently flipping negation parity.) Two `!`s
        // separated by a comment must yield Not(Not(pred)); three must
        // yield Not(Not(Not(pred))). The evaluator — not the parser —
        // collapses the parity.
        fn not_depth(c: &Condition) -> (usize, &Condition) {
            let mut d = 0;
            let mut cur = c;
            while let ConditionKind::Not { inner } = &cur.kind {
                d += 1;
                cur = inner;
            }
            (d, cur)
        }
        let two_c = parse("! // a comment here\n ! Drupe::Action::\"Login\"::request{}");
        let (d, leaf) = not_depth(&two_c);
        assert_eq!(d, 2, "two `!` across a comment must count as 2 negations");
        assert_eq!(pred(leaf), "Login");

        let three_c = parse("!\n!  // mid\n! Drupe::Action::\"Login\"::request{}");
        let (d, leaf) = not_depth(&three_c);
        assert_eq!(d, 3, "three `!` across whitespace/comments must count as 3");
        assert_eq!(pred(leaf), "Login");
    }

    #[test]
    fn except_desugaring_shape_and_left_assoc() {
        // `a && !b && !c` (the rewrite of `a except b except c`) is a
        // left-associative And whose right operands are negations.
        let c = parse(
            r#"Drupe::Action::"A"::request{} && !Drupe::Action::"B"::request{} && !Drupe::Action::"C"::request{}"#,
        );
        let (l, c_neg) = match &c.kind {
            ConditionKind::And { left, right } => (left, right),
            other => panic!("expected top And, got {other:?}"),
        };
        // right is `!C`
        match &c_neg.kind {
            ConditionKind::Not { inner } => assert_eq!(pred(inner), "C"),
            other => panic!("expected Not(C), got {other:?}"),
        }
        // left is `A && !B`
        match &l.kind {
            ConditionKind::And { left, right } => {
                assert_eq!(pred(left), "A");
                match &right.kind {
                    ConditionKind::Not { inner } => assert_eq!(pred(inner), "B"),
                    other => panic!("expected Not(B), got {other:?}"),
                }
            }
            other => panic!("expected nested And, got {other:?}"),
        }
    }

    #[test]
    fn negation_binds_tighter_than_since() {
        // `!X since within 1h Y` negates only the `since` LEFT operand —
        // this is the desugaring of `without X since within 1h Y`.
        let c = parse(
            r#"!Drupe::Action::"Logout"::request{} since within 1h Drupe::Action::"Login"::request{}"#,
        );
        match &c.kind {
            ConditionKind::Since { left, right, .. } => {
                match &left.kind {
                    ConditionKind::Not { inner } => assert_eq!(pred(inner), "Logout"),
                    other => panic!("expected Not(Logout) on since-left, got {other:?}"),
                }
                assert_eq!(pred(right), "Login");
            }
            other => panic!("expected Since, got {other:?}"),
        }
    }

    #[test]
    fn negation_binds_tighter_than_and() {
        // `!a && b` is `And(Not(a), b)`, not `Not(And(a, b))`.
        let c = parse(r#"!Drupe::Action::"A"::request{} && Drupe::Action::"B"::request{}"#);
        match &c.kind {
            ConditionKind::And { left, right } => {
                match &left.kind {
                    ConditionKind::Not { inner } => assert_eq!(pred(inner), "A"),
                    other => panic!("expected Not(A), got {other:?}"),
                }
                assert_eq!(pred(right), "B");
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn negation_of_parenthesized_group() {
        // `!(a && b)` negates the whole group.
        let c = parse(r#"!(Drupe::Action::"A"::request{} && Drupe::Action::"B"::request{})"#);
        match &c.kind {
            ConditionKind::Not { inner } => {
                assert!(
                    matches!(inner.kind, ConditionKind::And { .. }),
                    "inner is And"
                );
            }
            other => panic!("expected Not(And), got {other:?}"),
        }
    }

    #[test]
    fn dollar_binder_sigil_parses_in_binder_and_term_positions() {
        // The macro fresh-binder sigil `$t` parses in binder position
        // (`for ($t: Timepoint).`) and term position (`tp($t)`). It uses a
        // distinct character from the `!` negation operator, so the two
        // never interact. The aggregate sits as a comparison operand
        // inside an `exists` (the post-`let` shape).
        let c = parse(
            r#"exists (n: Long). ((count for ($t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp($t)))) == n && n > 0)"#,
        );
        // exists body is `(count …) == n && n > 0`; find the count operand.
        let count_agg = find_count_operand(&c).expect("an aggregate operand");
        match &count_agg.kind {
            AggExprKind::Count { for_vars, .. } => {
                assert!(
                    matches!(for_vars[0].slot, BinderSlot::BinderRef(ref n) if n == "t"),
                    "for-binder is the `$t` BinderRef, got {:?}",
                    for_vars[0].slot
                );
                assert_eq!(for_vars[0].ty, Type::Timepoint);
            }
            other => panic!("expected Count, got {other:?}"),
        }
    }

    #[test]
    fn old_bang_binder_sigil_no_longer_parses() {
        // The fresh-binder sigil moved from `!` to `$`. The OLD `!t`
        // spelling in binder position (`for (!t: …)`, `tp(!t)`) must no
        // longer parse — this is the exact `!`-vs-`$` counterpart of
        // `dollar_binder_sigil_parses_in_binder_and_term_positions`.
        // Without this guard, a future grammar edit could silently re-admit
        // `!t` as a binder. (A leading `!` now only ever lexes as negation,
        // and a bare name is not a valid binder slot, so the parse fails.)
        assert!(
            parse_condition(
                r#"exists (n: Long). ((count for (!t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp(!t)))) == n && n > 0)"#
            )
            .is_err(),
            "old `!t` binder syntax must no longer parse"
        );
        // Term position: `!q` as a predicate-arg value (the mc_0022 shape)
        // is likewise gone — `!` no longer starts a term.
        assert!(
            parse_condition(r#"Drupe::Action::"Transfer"::request{ requestId: !q }"#).is_err(),
            "old `!q` term-position binder syntax must no longer parse"
        );
    }

    #[test]
    fn dollar_sigil_is_not_a_whole_condition() {
        // A `$t` binder reference is only valid in binder/term positions,
        // never as a standalone condition: `sigil_cond` admits only `?p`. A
        // bare `$t` where a condition is expected must fail to parse.
        assert!(
            parse_condition(r#"$t"#).is_err(),
            "`$t` is not a valid standalone condition"
        );
    }

    /// Find the first aggregate term anywhere in a condition.
    fn find_count_operand(c: &Condition) -> Option<&AggExpr> {
        fn agg_of(t: &Term) -> Option<&AggExpr> {
            match t {
                Term::Agg(a) => Some(a.as_ref()),
                _ => None,
            }
        }
        match &c.kind {
            ConditionKind::Comparison { left, right, .. } => agg_of(left).or_else(|| agg_of(right)),
            ConditionKind::And { left, right } | ConditionKind::Since { left, right, .. } => {
                find_count_operand(left).or_else(|| find_count_operand(right))
            }
            ConditionKind::Not { inner }
            | ConditionKind::Formerly { body: inner, .. }
            | ConditionKind::Previous { body: inner, .. }
            | ConditionKind::Exists { body: inner, .. } => find_count_operand(inner),
            _ => None,
        }
    }

    #[test]
    fn removed_keywords_no_longer_parse() {
        // `except` and `without` are no longer operators; a policy using
        // them must fail to parse (the rewrite migrated every live case).
        assert!(
            parse_condition(
                r#"Drupe::Action::"A"::request{} except Drupe::Action::"B"::request{}"#
            )
            .is_err(),
            "`except` should no longer parse as an operator"
        );
        assert!(
            parse_condition(
                r#"without Drupe::Action::"A"::request{} since within 1h Drupe::Action::"B"::request{}"#
            )
            .is_err(),
            "`without … since` should no longer parse"
        );
    }

    // ─── Field-injection refinement (`P{…}{…}`, `?s{…}`) ────────────

    /// A refinement `Refine{ base, fields }` accessor for assertions.
    fn refine(c: &Condition) -> (&Condition, &[NamedArg]) {
        match &c.kind {
            ConditionKind::Refine { base, fields, .. } => (base, fields),
            other => panic!("expected Refine, got {other:?}"),
        }
    }

    /// The literal-string value of a named arg, for assertions.
    fn arg_str<'a>(args: &'a [NamedArg], name: &str) -> &'a str {
        let a = args
            .iter()
            .find(|a| a.name == name)
            .unwrap_or_else(|| panic!("no arg named `{name}` in {args:?}"));
        match &a.value {
            Term::String(s) => s,
            other => panic!("arg `{name}` is not a string: {other:?}"),
        }
    }

    #[test]
    fn bare_predicate_has_no_refine_node() {
        // NEGATIVE CONTROL: a predicate with no trailing block must parse
        // to a plain Predicate, never a Refine. If `refinable` leaked a
        // Refine here, every existing predicate would suddenly carry an
        // extra node and the residue/eval panics would fire.
        let c = parse(r#"Drupe::Action::"Read"::request{ user: u }"#);
        assert!(
            matches!(c.kind, ConditionKind::Predicate(_)),
            "bare predicate must stay a plain Predicate, got {:?}",
            c.kind
        );
    }

    #[test]
    fn single_field_block_builds_refine_over_predicate() {
        // `P{a}{b}` → Refine{ base: Predicate(P{a}), fields: [b] } with the
        // base predicate keeping ONLY its own arg.
        let c =
            parse(r#"Drupe::Action::"Transfer"::request{ amount: "10" }{ status: "approved" }"#);
        let (base, fields) = refine(&c);
        assert_eq!(pred(base), "Transfer");
        // The base predicate keeps its inline arg `amount`; the injected
        // block carries `status` — they are NOT merged at parse time (the
        // fold happens in the expander).
        match &base.kind {
            ConditionKind::Predicate(p) => {
                assert_eq!(p.args.len(), 1, "base keeps only its inline arg");
                assert_eq!(p.args[0].name, "amount");
            }
            other => panic!("expected Predicate base, got {other:?}"),
        }
        assert_eq!(fields.len(), 1);
        assert_eq!(arg_str(fields, "status"), "approved");
    }

    #[test]
    fn chained_blocks_flatten_to_one_refine() {
        // `P{}{a}{b}` chains — the parser flattens the two trailing blocks
        // into a single Refine with concatenated fields (chaining ≡ one
        // block with both args).
        let c =
            parse(r#"Drupe::Action::"Transfer"::request{}{ status: "approved" }{ region: "us" }"#);
        let (base, fields) = refine(&c);
        assert_eq!(pred(base), "Transfer");
        assert_eq!(fields.len(), 2, "both trailing blocks flatten together");
        assert_eq!(arg_str(fields, "status"), "approved");
        assert_eq!(arg_str(fields, "region"), "us");
    }

    #[test]
    fn sigil_condition_can_be_refined() {
        // `?s{ status: "approved" }` — the load-bearing macro path. The
        // base is a SigilRef (a `?s` standing for a whole condition), and
        // the injected block rides on top of it. Only legal in a macro
        // body, but the parser accepts it here; the expander resolves `?s`.
        let c = parse(r#"?s{ status: "approved" }"#);
        let (base, fields) = refine(&c);
        assert!(
            matches!(&base.kind, ConditionKind::SigilRef { name, .. } if name == "s"),
            "base is the `?s` SigilRef, got {:?}",
            base.kind
        );
        assert_eq!(fields.len(), 1);
        assert_eq!(arg_str(fields, "status"), "approved");
    }

    #[test]
    fn bare_sigil_condition_has_no_refine_node() {
        // NEGATIVE CONTROL for the sigil path: `?s` with no block is a
        // plain SigilRef, not a Refine.
        let c = parse(r#"?s"#);
        assert!(
            matches!(c.kind, ConditionKind::SigilRef { .. }),
            "bare `?s` must stay a SigilRef, got {:?}",
            c.kind
        );
    }

    #[test]
    fn negation_wraps_the_refinement() {
        // `!P{}{x}` parses as Not(Refine(P, [x])) — the `!` negates the
        // whole refined predicate (the `neg_conjunct` wrapper sits outside
        // `refinable`).
        let c = parse(r#"!Drupe::Action::"Transfer"::request{}{ status: "approved" }"#);
        match &c.kind {
            ConditionKind::Not { inner } => {
                let (base, fields) = refine(inner);
                assert_eq!(pred(base), "Transfer");
                assert_eq!(arg_str(fields, "status"), "approved");
            }
            other => panic!("expected Not(Refine), got {other:?}"),
        }
    }

    #[test]
    fn refinement_under_formerly_and_conjunction() {
        // A refined predicate must parse both as a `formerly` body and as
        // a `&&` operand (i.e. `refinable` is reachable from `atom` and
        // `conjunct`). `formerly within 1h P{}{s} && Q{}` →
        // And(Formerly(Refine(P)), Q).
        let c = parse(
            r#"formerly within 1h Drupe::Action::"Transfer"::request{}{ status: "approved" } && Drupe::Action::"Write"::request{}"#,
        );
        match &c.kind {
            ConditionKind::And { left, right } => {
                match &left.kind {
                    ConditionKind::Formerly { body, .. } => {
                        let (base, fields) = refine(body);
                        assert_eq!(pred(base), "Transfer");
                        assert_eq!(arg_str(fields, "status"), "approved");
                    }
                    other => panic!("expected Formerly on the left, got {other:?}"),
                }
                assert_eq!(pred(right), "Write");
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    // ─── Dotted field paths in predicates (`input.user: …`) ─────────

    /// Return the predicate's named-arg field names, in order.
    fn arg_names(c: &Condition) -> Vec<String> {
        match &c.kind {
            ConditionKind::Predicate(p) => p.args.iter().map(|a| a.name.clone()).collect(),
            other => panic!("expected predicate, got {other:?}"),
        }
    }

    #[test]
    fn dotted_field_path_parses() {
        // `input.user` is kept as the dotted name; `field_path()` splits it.
        let c = parse(r#"Drupe::Action::"Login"::request{ input.user: u }"#);
        assert_eq!(arg_names(&c), vec!["input.user".to_string()]);
        match &c.kind {
            ConditionKind::Predicate(p) => {
                assert_eq!(p.args[0].field_path(), vec!["input", "user"]);
            }
            other => panic!("expected predicate, got {other:?}"),
        }
    }

    #[test]
    fn bare_field_name_is_a_single_segment_path() {
        // A flat field (`callerPrincipal`) is a one-segment path — the
        // old behavior, still available for top-level fields.
        let c = parse(r#"Drupe::Action::"Login"::request{ callerPrincipal: p }"#);
        match &c.kind {
            ConditionKind::Predicate(pred) => {
                assert_eq!(pred.args[0].field_path(), vec!["callerPrincipal"]);
            }
            other => panic!("expected predicate, got {other:?}"),
        }
    }

    #[test]
    fn mixed_dotted_and_bare_fields_parse() {
        let c = parse(
            r#"Drupe::Action::"Login"::response{ input.user: u, output.result: true, requestId: x }"#,
        );
        assert_eq!(
            arg_names(&c),
            vec![
                "input.user".to_string(),
                "output.result".to_string(),
                "requestId".to_string()
            ]
        );
    }

    // ─── `exists` binder + aggregates as comparison operands ────────

    /// Accessor: the typed binder + body of an `Exists`.
    fn exists(c: &Condition) -> (&TypedBinder, &Condition) {
        match &c.kind {
            ConditionKind::Exists { var, body } => (var, body),
            other => panic!("expected Exists, got {other:?}"),
        }
    }

    #[test]
    fn exists_parses_with_typed_binder() {
        let c = parse(r#"exists (n: Long). (Drupe::Action::"Login"::request{ input.amount: n })"#);
        let (var, _body) = exists(&c);
        assert!(matches!(var.slot, BinderSlot::Name(ref s) if s == "n"));
        assert_eq!(var.ty, Type::Named(vec!["Long".to_string()]));
    }

    #[test]
    fn exists_binder_scope_is_greedy_right() {
        // `exists (t: Timepoint). P && Q` binds `t` over the WHOLE `P && Q`
        // (greedy-right), i.e. the body is the top-level And — not
        // `(exists t. P) && Q`.
        let c = parse(
            r#"exists (t: Timepoint). Drupe::Action::"Login"::request{} && Drupe::Action::"Read"::request{}"#,
        );
        let (_var, body) = exists(&c);
        assert!(
            matches!(body.kind, ConditionKind::And { .. }),
            "exists body should be the whole `P && Q`, got {:?}",
            body.kind
        );
    }

    #[test]
    fn parens_stop_exists_scope() {
        // `(exists (t: Timepoint). P) && Q` — the parens fence the binder,
        // so the top level is an And whose left is the Exists.
        let c = parse(
            r#"(exists (t: Timepoint). Drupe::Action::"Login"::request{}) && Drupe::Action::"Read"::request{}"#,
        );
        match &c.kind {
            ConditionKind::And { left, right } => {
                assert!(
                    matches!(left.kind, ConditionKind::Exists { .. }),
                    "left should be Exists, got {:?}",
                    left.kind
                );
                assert_eq!(pred(right), "Read");
            }
            other => panic!("expected And(Exists, Read), got {other:?}"),
        }
    }

    #[test]
    fn aggregate_as_right_operand_needs_no_parens() {
        // `0 < count for (t: Timepoint). where φ` — the aggregate is the
        // rightmost operand, so its greedy `where` body has nothing to
        // swallow and no parens are needed.
        let c = parse(
            r#"0 < count for (t: Timepoint). where (Drupe::Action::"Login"::request{} && tp(t))"#,
        );
        match &c.kind {
            ConditionKind::Comparison { op, left, right } => {
                assert_eq!(*op, CmpOp::Lt);
                assert!(matches!(left, Term::Integer(0)));
                assert!(
                    matches!(right, Term::Agg(a) if matches!(a.kind, AggExprKind::Count { .. })),
                    "right operand is a Count aggregate"
                );
            }
            other => panic!("expected Comparison, got {other:?}"),
        }
    }

    #[test]
    fn parenthesized_aggregate_as_left_operand() {
        // `(count …) == n` — the aggregate must be parenthesized on the
        // LEFT so its greedy `where` body does not eat the `== n`. This is
        // the shape the `let`-migration emits.
        let c = parse(
            r#"(count for (t: Timepoint). where (Drupe::Action::"Login"::request{} && tp(t))) == n"#,
        );
        match &c.kind {
            ConditionKind::Comparison { op, left, right } => {
                assert_eq!(*op, CmpOp::Eq);
                assert!(
                    matches!(left, Term::Agg(a) if matches!(a.kind, AggExprKind::Count { .. })),
                    "left operand is a parenthesized Count aggregate"
                );
                assert!(matches!(right, Term::Var(v) if v == "n"));
            }
            other => panic!("expected Comparison, got {other:?}"),
        }
    }

    #[test]
    fn interleaved_binder_scopes_in_exists_of_count() {
        // `exists (n: Long). ((count for (t: Timepoint). where φ) == n && n > 0)`
        // — `t` is scoped to the count's parens (dies at the `)`); `n`
        // lives to the outer `)`. The whole thing is an Exists whose body
        // is an And of the `(count …) == n` comparison and `n > 0`.
        let c = parse(
            r#"exists (n: Long). ((count for (t: Timepoint). where (Drupe::Action::"Login"::request{} && tp(t))) == n && n > 0)"#,
        );
        let (var, body) = exists(&c);
        assert!(matches!(var.slot, BinderSlot::Name(ref s) if s == "n"));
        match &body.kind {
            ConditionKind::And { left, right } => {
                // left: (count …) == n
                assert!(
                    matches!(
                        &left.kind,
                        ConditionKind::Comparison {
                            op: CmpOp::Eq,
                            left: Term::Agg(_),
                            ..
                        }
                    ),
                    "left conjunct is `(count …) == n`, got {:?}",
                    left.kind
                );
                // right: n > 0
                assert!(
                    matches!(&right.kind, ConditionKind::Comparison { op: CmpOp::Gt, .. }),
                    "right conjunct is `n > 0`, got {:?}",
                    right.kind
                );
            }
            other => panic!("expected And body, got {other:?}"),
        }
    }

    #[test]
    fn not_equal_parses_to_noteq() {
        // `!=` is the Cedar inequality operator; the temporal fragment
        // parses it to `CmpOp::NotEq` (parity with the Cedar `when { … }`
        // side, which already supports `!=`).
        let c = parse(r#"context.input.amount != 100"#);
        match &c.kind {
            ConditionKind::Comparison { op, right, .. } => {
                assert_eq!(*op, CmpOp::NotEq);
                assert!(matches!(right, Term::Integer(100)));
            }
            other => panic!("expected Comparison, got {other:?}"),
        }
    }

    #[test]
    fn let_keyword_no_longer_parses() {
        // `let … in …` is deleted; a policy using it must fail to parse
        // (the migration rewrote every live case to `exists`).
        assert!(
            parse_condition(
                r#"let n = count for (t: Timepoint). where Drupe::Action::"Login"::request{} in n > 0"#
            )
            .is_err(),
            "`let … in …` should no longer parse"
        );
    }
}
