//! Lower a structured [`crate::ast::Expr`] to a loc-bearing
//! `cedar_policy_core::ast::Expr`.
//!
//! This is the desugaring lowering — the analog of Cedar's own
//! `cst_to_ast`: the surface [`crate::ast::Expr`] preserves what the user
//! wrote (surface operators like `!=` / `>`, extension *methods* like
//! `.lessThan(…)`), and here we desugar each into Cedar's evaluation `ast`
//! via the [`ExprBuilder`] primitive — the same primitive Cedar's
//! `cst_to_ast` uses. So `>` becomes `!(… <= …)`, `!=` becomes `!(… == …)`,
//! and extension methods/constructors become `ExtensionFunctionApp`s,
//! exactly as Cedar's text parser produces.
//!
//! Crucially, every built `ast::Expr` node carries a
//! [`Loc`](cedar_policy_core::parser::Loc) whose span is the originating
//! `.dw` byte range (from the surface node's [`crate::ast::Expr::span`]) and
//! whose source text is the whole `.dw` source. That is what lets Cedar's
//! validator report a diagnostic that points at the precise `.dw`
//! sub-expression rather than the enclosing rule.
//!
//! The one non-`ast` surface variant, [`ExprKind::Extension`], is
//! **hoisted**: a `temporal { … }` leaf becomes a `context.__temporal_N`
//! reference (recorded as a [`super::ContextField`]); a `provider { … }`
//! leaf hoists its invocation to `context.providers.<name>` (recorded as a
//! [`super::ProviderField`]) and lowers the projection/comparison natively.
//! The hoisted `context.<field>` reference is stamped with the *original
//! leaf's* `.dw` span, so a type error on a hoisted field still points at
//! the `temporal { … }` / `guardrails { … }` block the user wrote.

use std::sync::Arc;

use cedar_policy_core::ast::{self as cedar_ast, Expr as AstExpr, ExprBuilder, Name};
use cedar_policy_core::expr_builder::ExprBuilder as _;
use cedar_policy_core::parser::Loc;

use super::{Ctx, ScopedAction};
use crate::ast::{BinOp, Expr, ExprKind, UnOp};
use crate::error::{RawCedarifyError, Span};
use crate::extension::{Dialect, Extension};

/// A `()`-data `ast` expression builder positioned at `span` within the
/// `.dw` source `src`. Every node this builds carries the matching [`Loc`].
fn at(src: &Arc<str>, span: Span) -> ExprBuilder<()> {
    let loc = Loc::new(span.start..span.end, Arc::clone(src));
    ExprBuilder::new().with_source_loc(&loc)
}

/// Lower `expr` to a loc-bearing `ast::Expr`, hoisting temporal/provider
/// extension leaves into `ctx`. `action` is the rule's scoped action (for
/// attaching hoisted fields). `src` is the whole `.dw` source, shared into
/// every node's `Loc`.
pub(super) fn lower_expr(
    expr: &Expr,
    action: &ScopedAction,
    ctx: &mut Ctx,
    src: &Arc<str>,
) -> Result<AstExpr, RawCedarifyError> {
    let span = expr.span;
    let b = || at(src, span);
    match &expr.kind {
        ExprKind::Lit(lit) => Ok(b().val(lit.clone())),
        ExprKind::Var(v) => Ok(b().var(*v)),
        ExprKind::Slot(s) => Ok(b().slot(*s)),

        ExprKind::Extension(Extension::Temporal(t)) => {
            // Hoist: replace the leaf with a `context.<rule_key>__temporal_N`
            // reference (a pre-evaluated Bool) and record it so `authorize`
            // can evaluate it. The reference carries the leaf's `.dw` span.
            // The rule-key prefix and the per-policy ordinal make the name
            // deterministic and unique across lowering calls (so independently
            // lowered sets never collide when combined).
            let field_name = format!(
                "{}__{}_{}",
                ctx.rule_key,
                Dialect::Temporal.marker(),
                ctx.field_ordinal
            );
            ctx.field_ordinal += 1;
            ctx.bool_fields.push(super::ContextField {
                action: action.clone(),
                field_name: field_name.clone(),
                temporal: t.clone(),
                // Resolved after the fragment is parsed, in `cedarify_with_providers`,
                // where the action hierarchy is available.
                target_actions: Vec::new(),
                principal: ctx.principal_scope.clone(),
                resource: ctx.resource_scope.clone(),
            });
            Ok(b().get_attr(b().var(cedar_ast::Var::Context), field_name.into()))
        }
        ExprKind::UnaryApp { op, expr } => {
            let arg = lower_expr(expr, action, ctx, src)?;
            Ok(lower_unary(*op, arg, src, span))
        }
        ExprKind::BinaryApp { op, left, right } => {
            let l = lower_expr(left, action, ctx, src)?;
            let r = lower_expr(right, action, ctx, src)?;
            Ok(lower_binary(*op, l, r, src, span))
        }
        ExprKind::GetAttr { expr, attr } => {
            let e = lower_expr(expr, action, ctx, src)?;
            Ok(b().get_attr(e, attr.as_str().into()))
        }
        ExprKind::HasAttr { expr, attrs } => {
            let e = lower_expr(expr, action, ctx, src)?;
            Ok(b().extended_has_attr(e, to_nonempty(attrs)))
        }
        ExprKind::Like { expr, pattern } => {
            let e = lower_expr(expr, action, ctx, src)?;
            Ok(b().like(e, cedar_ast::Pattern::from(pattern.clone())))
        }
        ExprKind::Is {
            expr,
            entity_type,
            in_expr,
        } => {
            let e = lower_expr(expr, action, ctx, src)?;
            match in_expr {
                Some(in_e) => {
                    let ine = lower_expr(in_e, action, ctx, src)?;
                    Ok(b().is_in_entity_type(e, entity_type.clone(), ine))
                }
                None => Ok(b().is_entity_type(e, entity_type.clone())),
            }
        }
        ExprKind::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => {
            let c = lower_expr(cond, action, ctx, src)?;
            let t = lower_expr(then_expr, action, ctx, src)?;
            let e = lower_expr(else_expr, action, ctx, src)?;
            Ok(b().ite(c, t, e))
        }
        ExprKind::Set(elems) => {
            let out = elems
                .iter()
                .map(|e| lower_expr(e, action, ctx, src))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(b().set(out))
        }
        ExprKind::Record(entries) => {
            let mut pairs = Vec::with_capacity(entries.len());
            for (k, v) in entries {
                pairs.push((k.as_str().into(), lower_expr(v, action, ctx, src)?));
            }
            b().record(pairs).map_err(|e| RawCedarifyError {
                message: format!("invalid record literal: {e}"),
                span: Some(span),
            })
        }

        ExprKind::Call { name, args } => {
            if is_provider_invocation(name, ctx) {
                let invocation = cedar_call_to_invocation(name, args, span)?;
                // A bare `Ns::Fn(args)` call with no trailing method chain. The
                // invocation span is already an absolute `.dw` span (built from
                // the Cedar expr), so `body_base` is 0 — validation rebases by
                // it, and there is no block-relative offset to add.
                lower_provider_invocation(&invocation, &[], action, 0, ctx, src, span)
            } else {
                Err(RawCedarifyError {
                    message: format!(
                        "unresolved call to `{name}` reached lowering — it is not a declared \
                         information provider, not a declared macro, and not a Cedar built-in \
                         (macro expansion runs before lowering)"
                    ),
                    span: Some(span),
                })
            }
        }
        ExprKind::MethodCall { method, .. } => {
            // A method the parser could not resolve to a Cedar built-in. It is
            // valid only as a **provider output method** on a chain whose base
            // is a declared provider invocation (`Ns::Fn(x).classify().foo()`).
            // Peel the `MethodCall`/`Call` spine to that base; if it is a
            // declared provider, hoist the invocation with the collected method
            // chain (eager-evaluated in Rhai), then lower any trailing
            // field/index projection as native Cedar over the hoisted value.
            // Otherwise it is a genuine unknown method — reject it here (the
            // parse-time error, deferred to where declarations are known).
            match peel_provider_chain(expr, ctx)? {
                Some(peeled) => {
                    let base = lower_provider_invocation(
                        &peeled.invocation,
                        &peeled.methods,
                        action,
                        0,
                        ctx,
                        src,
                        span,
                    )?;
                    Ok(apply_cedar_projection(base, &peeled.trailing, src))
                }
                None => Err(RawCedarifyError {
                    message: format!("unknown method `{method}`"),
                    span: Some(span),
                }),
            }
        }
        ExprKind::ParamRef { name } => Err(RawCedarifyError {
            message: format!(
                "macro parameter `?{name}` reached lowering — expansion did not substitute it"
            ),
            span: Some(span),
        }),
    }
}

/// Desugar a surface unary op onto an already-lowered argument, stamping the
/// node's `.dw` span. Extension constructors/methods become
/// `ExtensionFunctionApp`s; the three core ops use the native builder.
fn lower_unary(op: UnOp, arg: AstExpr, src: &Arc<str>, span: Span) -> AstExpr {
    let b = || at(src, span);
    match op {
        UnOp::Not => b().not(arg),
        UnOp::Neg => b().neg(arg),
        UnOp::IsEmpty => b().is_empty(arg),
        // Extension constructors / zero-argument methods — a single-arg
        // `ExtensionFunctionApp` keyed by the (unqualified) function name.
        UnOp::Decimal => ext_call("decimal", [arg], src, span),
        UnOp::Datetime => ext_call("datetime", [arg], src, span),
        UnOp::Duration => ext_call("duration", [arg], src, span),
        UnOp::Ip => ext_call("ip", [arg], src, span),
        UnOp::IsIpv4 => ext_call("isIpv4", [arg], src, span),
        UnOp::IsIpv6 => ext_call("isIpv6", [arg], src, span),
        UnOp::IsLoopback => ext_call("isLoopback", [arg], src, span),
        UnOp::IsMulticast => ext_call("isMulticast", [arg], src, span),
        UnOp::ToDate => ext_call("toDate", [arg], src, span),
        UnOp::ToTime => ext_call("toTime", [arg], src, span),
        UnOp::ToMilliseconds => ext_call("toMilliseconds", [arg], src, span),
        UnOp::ToSeconds => ext_call("toSeconds", [arg], src, span),
        UnOp::ToMinutes => ext_call("toMinutes", [arg], src, span),
        UnOp::ToHours => ext_call("toHours", [arg], src, span),
        UnOp::ToDays => ext_call("toDays", [arg], src, span),
    }
}

/// Desugar a surface binary op onto two already-lowered operands, stamping
/// the node's `.dw` span. `>`/`>=`/`!=` desugar to `!(…)` via the builder;
/// the decimal comparison methods become two-arg `ExtensionFunctionApp`s.
fn lower_binary(op: BinOp, l: AstExpr, r: AstExpr, src: &Arc<str>, span: Span) -> AstExpr {
    let b = || at(src, span);
    match op {
        BinOp::Eq => b().is_eq(l, r),
        BinOp::NotEq => b().noteq(l, r),
        BinOp::Less => b().less(l, r),
        BinOp::LessEq => b().lesseq(l, r),
        BinOp::Greater => b().greater(l, r),
        BinOp::GreaterEq => b().greatereq(l, r),
        BinOp::And => b().and(l, r),
        BinOp::Or => b().or(l, r),
        BinOp::Add => b().add(l, r),
        BinOp::Sub => b().sub(l, r),
        BinOp::Mul => b().mul(l, r),
        BinOp::In => b().is_in(l, r),
        BinOp::Contains => b().contains(l, r),
        BinOp::ContainsAll => b().contains_all(l, r),
        BinOp::ContainsAny => b().contains_any(l, r),
        BinOp::GetTag => b().get_tag(l, r),
        BinOp::HasTag => b().has_tag(l, r),
        // One-argument extension methods: receiver + argument.
        BinOp::IsInRange => ext_call("isInRange", [l, r], src, span),
        BinOp::Offset => ext_call("offset", [l, r], src, span),
        BinOp::DurationSince => ext_call("durationSince", [l, r], src, span),
        BinOp::DecimalLessThan => ext_call("lessThan", [l, r], src, span),
        BinOp::DecimalLessEq => ext_call("lessThanOrEqual", [l, r], src, span),
        BinOp::DecimalGreater => ext_call("greaterThan", [l, r], src, span),
        BinOp::DecimalGreaterEq => ext_call("greaterThanOrEqual", [l, r], src, span),
    }
}

/// Build an `ExtensionFunctionApp` for `fn_name` over `args`, stamped at
/// `span`. The name is an unqualified identifier (the form Cedar's own
/// `cst_to_ast` uses for method/constructor calls).
fn ext_call<const N: usize>(
    fn_name: &str,
    args: [AstExpr; N],
    src: &Arc<str>,
    span: Span,
) -> AstExpr {
    let name = Name::parse_unqualified_name(fn_name)
        .expect("extension function names are valid identifiers");
    at(src, span)
        .call_extension_fn(name, args)
        .expect("ast::ExprBuilder build is infallible")
}

/// Build the non-empty attribute path `has` requires. The grammar
/// guarantees at least one element; an empty slice would be a parser bug,
/// so we fall back to a single empty segment rather than panic.
fn to_nonempty(attrs: &[String]) -> nonempty::NonEmpty<smol_str::SmolStr> {
    let mut iter = attrs.iter().map(|a| a.as_str().into());
    let head = iter.next().unwrap_or_else(|| "".into());
    nonempty::NonEmpty {
        head,
        tail: iter.collect(),
    }
}

// =========================================================================
// Information-provider lowering
// =========================================================================
//
// A provider invocation is an ordinary Cedar call whose name is a declared
// provider (`Ns::Fn(args)`), optionally followed by output methods and a
// field/index projection: `Ns::Fn(x).classify().violence`. `lower_expr`
// recognizes it two ways — a bare `ExprKind::Call` (no methods) directly, and
// an `ExprKind::MethodCall` chain via `peel_provider_chain` — then hoists the
// invocation (plus its eager method chain, evaluated in Rhai at authorize
// time) to a `context.providers.<name>` reference, leaving any trailing
// projection and the surrounding comparison as native Cedar. The invocation
// is lowered at its own `.dw` span, so a diagnostic points at the call site.

use crate::extension::provider::ast::{Arg, Invocation, MethodCall};

/// A provider invocation peeled out of a Cedar `MethodCall`/`Call` spine:
/// the base [`Invocation`], the eager method chain in call order, and any
/// trailing native-Cedar field/index projection *after* the last method.
struct PeeledChain {
    invocation: Invocation,
    methods: Vec<MethodCall>,
    /// `(attr, span)` for each trailing `.field` / `["key"]` access to lower
    /// as a native-Cedar `GetAttr` over the hoisted value.
    trailing: Vec<(String, Span)>,
}

/// Peel a surface expression that is a chain of provider methods / field
/// accesses down to a base [`Invocation`], **iff** that base is a declared
/// information provider. Returns `None` if the base is not a provider call
/// (so the caller reports a genuine unknown-method error).
///
/// The chain shape produced by the parser for `Ns::Fn(x).m1().f.m2()` is a
/// left-nested spine of `MethodCall`/`GetAttr` over a base `Call`. We walk it
/// **outermost-first**, collecting accessors, then reverse to source order.
/// The split mirrors the old provider grammar: everything up to and including
/// the LAST method is *eager* (evaluated in Rhai, bound into
/// `context.providers.<id>`); accessors after the last method stay native
/// Cedar. A field/index that appears *before* a method (folded into the eager
/// prefix) is not expressible over the hoisted value, so it is rejected —
/// the common forms `Fn(x).m()` and `Fn(x).m().field` are unaffected.
fn peel_provider_chain(expr: &Expr, ctx: &Ctx) -> Result<Option<PeeledChain>, RawCedarifyError> {
    // Accessor kinds gathered while walking the spine (outermost first).
    enum Acc {
        Method(MethodCall),
        Field(String, Span),
    }
    let mut accs: Vec<Acc> = Vec::new();
    let mut cur = expr;
    let base_call = loop {
        match &cur.kind {
            ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => {
                let m_args = args
                    .iter()
                    .map(|a| cedar_expr_to_provider_arg(a, cur.span))
                    .collect::<Result<Vec<_>, _>>()?;
                accs.push(Acc::Method(MethodCall {
                    span: cur.span,
                    name: method.clone(),
                    args: m_args,
                }));
                cur = receiver;
            }
            ExprKind::GetAttr { expr: inner, attr } => {
                accs.push(Acc::Field(attr.clone(), cur.span));
                cur = inner;
            }
            ExprKind::Call { name, args } if is_provider_invocation(name, ctx) => {
                break cedar_call_to_invocation(name, args, cur.span)?;
            }
            // Base is not a provider invocation — not a provider chain.
            _ => return Ok(None),
        }
    };

    // Reverse to source order (base → outermost).
    accs.reverse();

    // Split at the last method: prefix (eager) vs. trailing (native Cedar).
    let last_method = accs.iter().rposition(|a| matches!(a, Acc::Method(_)));
    let split = match last_method {
        Some(i) => i + 1,
        None => 0,
    };
    let (eager, trailing_accs) = accs.split_at(split);

    // A field/index before the last method cannot be a Cedar projection over
    // the hoisted value — it would have to be folded into the eager Rhai
    // prefix. Reject that shape (rare: `Fn(x).field.method()`).
    if eager.iter().any(|a| matches!(a, Acc::Field(_, _))) {
        return Err(RawCedarifyError {
            message: "a field or index projection may not appear before a provider \
                      method in the same chain; put projections after the method chain"
                .to_string(),
            span: Some(expr.span),
        });
    }

    let methods: Vec<MethodCall> = eager
        .iter()
        .filter_map(|a| match a {
            Acc::Method(m) => Some(m.clone()),
            Acc::Field(_, _) => None,
        })
        .collect();
    let trailing: Vec<(String, Span)> = trailing_accs
        .iter()
        .filter_map(|a| match a {
            Acc::Field(name, span) => Some((name.clone(), *span)),
            Acc::Method(_) => None,
        })
        .collect();

    Ok(Some(PeeledChain {
        invocation: base_call,
        methods,
        trailing,
    }))
}

/// Apply a trailing native-Cedar projection (`.field` accesses after the
/// provider's eager method chain) onto the hoisted value.
fn apply_cedar_projection(base: AstExpr, trailing: &[(String, Span)], src: &Arc<str>) -> AstExpr {
    let mut expr = base;
    for (attr, span) in trailing {
        expr = at(src, *span).get_attr(expr, attr.as_str().into());
    }
    expr
}

/// Hoist a provider invocation (plus its eager method chain) to its
/// `context.providers.p_N` reference, recording a [`super::ProviderField`].
///
/// The hoisted field's Cedar type is the type of the value that will be bound
/// at authorize time: the **last method's** `outputType` when a chain is
/// present, else the provider's base `outputType`. (An undeclared provider or
/// an unknown method falls back to a permissive `String`; validation reports
/// the real error.)
fn lower_provider_invocation(
    invocation: &Invocation,
    methods: &[super::super::extension::provider::ast::MethodCall],
    action: &ScopedAction,
    body_base: usize,
    ctx: &mut Ctx,
    src: &Arc<str>,
    span: Span,
) -> Result<AstExpr, RawCedarifyError> {
    let key = invocation.key();
    let decl = ctx.provider_declarations.and_then(|d| d.get(&key));
    // Type the hoisted field from the pipeline's tail: the last method's
    // output type if the chain is non-empty, else the provider's output type.
    let cedar_type = match methods.last() {
        Some(last) => decl
            .and_then(|d| d.methods.get(&last.name))
            .map(|m| m.output_type.to_cedar_type())
            .unwrap_or_else(|| "String".to_string()),
        None => decl
            .map(|d| d.output_type.to_cedar_type())
            .unwrap_or_else(|| "String".to_string()),
    };

    let field_name = format!("{}_p_{}", ctx.rule_key, ctx.field_ordinal);
    ctx.field_ordinal += 1;
    ctx.provider_fields.push(super::ProviderField {
        action: action.clone(),
        target_actions: Vec::new(),
        field_name: field_name.clone(),
        cedar_type,
        body_base,
        invocation: invocation.clone(),
        methods: methods.to_vec(),
    });

    // `context.providers.<field_name>`.
    let b = || at(src, span);
    let providers = b().get_attr(b().var(cedar_ast::Var::Context), "providers".into());
    Ok(b().get_attr(providers, field_name.as_str().into()))
}

/// Is `name` (a call target) a **provider invocation** — structurally, a
/// namespace-qualified name (`Ns::Fn`)?
///
/// Delegates to the canonical [`crate::extension::provider::is_provider_name`]
/// shape test (any namespaced name is a provider invocation), so lowering and
/// the pre-lowering [`ParsedPolicySet`](crate::policy_set::ParsedPolicySet)
/// diagnostics agree on what counts as an invocation. Whether the provider is
/// *declared* is a validation concern
/// (`super::super::extension::provider::validate`), which reports an undeclared
/// name against the invocation's span — matching MFOTL, which likewise
/// recognizes invocations structurally and defers declaration checks.
fn is_provider_invocation(name: &str, _ctx: &Ctx) -> bool {
    crate::extension::provider::is_provider_name(name)
}

/// Convert a bare Cedar call (`Ns::Fn(args)`) into a provider [`Invocation`].
///
/// `pub(crate)` so the pre-lowering
/// [`ParsedPolicy`](crate::policy_set::ParsedPolicy) provider-invocation
/// accessor extracts invocation arguments through the *same* rule lowering
/// uses — the two never diverge on what a provider argument may be.
pub(crate) fn cedar_call_to_invocation(
    name: &str,
    args: &[Expr],
    span: Span,
) -> Result<Invocation, RawCedarifyError> {
    let function: Vec<String> = name.split("::").map(str::to_string).collect();
    let args = args
        .iter()
        .map(|a| cedar_expr_to_provider_arg(a, span))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Invocation {
        span,
        function,
        args,
    })
}

/// Convert one surface argument expression into a provider [`Arg`].
///
/// A provider argument is resolved *pre-Cedar* (it helps build the context
/// Cedar evaluates against), so it must be a value the resolver can read off
/// the request event without evaluating Cedar: an attribute path rooted at
/// `context` / `principal` / `resource`, a literal (string / integer / bool /
/// `decimal("…")`), or a set of those. This mirrors MFOTL's argument rule
/// (field paths + literals + sets); arbitrary arithmetic / `if` is not a
/// provider argument.
fn cedar_expr_to_provider_arg(expr: &Expr, span: Span) -> Result<Arg, RawCedarifyError> {
    match &expr.kind {
        ExprKind::GetAttr { .. }
        | ExprKind::Var(cedar_ast::Var::Context)
        | ExprKind::Var(cedar_ast::Var::Principal)
        | ExprKind::Var(cedar_ast::Var::Resource) => {
            let path = flatten_arg_path(expr).ok_or_else(|| RawCedarifyError {
                message: "a provider argument that is an attribute access must be an attribute \
                          path rooted at `context`, `principal`, or `resource` \
                          (e.g. `context.input.x`, `principal.id`)"
                    .to_string(),
                span: Some(span),
            })?;
            Ok(Arg::Field(path))
        }
        // `decimal("…")` lowers (in the parser) to `UnaryApp { Decimal, "…" }`.
        ExprKind::UnaryApp {
            op: UnOp::Decimal,
            expr: inner,
        } => match &inner.kind {
            ExprKind::Lit(cedar_ast::Literal::String(s)) => Ok(Arg::Decimal(s.to_string())),
            _ => Err(RawCedarifyError {
                message: "`decimal(…)` provider argument requires a string literal, \
                          e.g. `decimal(\"0.5\")`"
                    .to_string(),
                span: Some(span),
            }),
        },
        ExprKind::Lit(cedar_ast::Literal::String(s)) => Ok(Arg::String(s.to_string())),
        ExprKind::Lit(cedar_ast::Literal::Long(n)) => Ok(Arg::Integer(*n)),
        ExprKind::Lit(cedar_ast::Literal::Bool(b)) => Ok(Arg::Bool(*b)),
        ExprKind::Set(elems) => Ok(Arg::Set(
            elems
                .iter()
                .map(|e| cedar_expr_to_provider_arg(e, span))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        _ => Err(RawCedarifyError {
            message: "a provider argument must be an attribute path rooted at `context`, \
                      `principal`, or `resource`, a string / integer / bool / `decimal(…)` \
                      literal, or a set of those"
                .to_string(),
            span: Some(span),
        }),
    }
}

/// Flatten an attribute-path surface expression rooted at `context` /
/// `principal` / `resource` into its segments, e.g. `context.input.x` →
/// `["context","input","x"]`, `principal.id` → `["principal","id"]`.
fn flatten_arg_path(expr: &Expr) -> Option<Vec<String>> {
    match &expr.kind {
        ExprKind::Var(cedar_ast::Var::Context) => Some(vec!["context".to_string()]),
        ExprKind::Var(cedar_ast::Var::Principal) => Some(vec!["principal".to_string()]),
        ExprKind::Var(cedar_ast::Var::Resource) => Some(vec!["resource".to_string()]),
        ExprKind::GetAttr { expr, attr } => {
            let mut path = flatten_arg_path(expr)?;
            path.push(attr.clone());
            Some(path)
        }
        _ => None,
    }
}
