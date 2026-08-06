//! Macro expansion pass.
//!
//! Runs after parsing and before validation/cedarify. Consumes the
//! [`PolicySet::defs`] and substitutes every macro call in the
//! policies' expressions and temporal blocks with the macro's body.
//!
//! The pass has two stages:
//!
//! 1. **Registry build + well-formedness.** Collect all macro definitions
//!    into a name-keyed table; reject duplicates and reserved names;
//!    walk each body to (a) reject macro-in-macro (any unresolved
//!    `Call` inside a body), (b) reject any `?p`/`$t` reference that
//!    doesn't name a declared parameter, and (c) tag each parameter
//!    with whether it is used in a binder position somewhere in the
//!    body — at call sites such params must receive a single-identifier
//!    argument.
//!
//! 2. **Expansion walk.** Recursively transform every policy: each
//!    macro call is looked up, kind-checked against the call slot,
//!    arity-checked, binder-position args are checked to be
//!    single-identifiers, and the macro's body is substituted with
//!    fresh names for `$t` (gensym `<name>$<call-span-start>`).
//!    Any `?p`/`$t`/`SigilRef`/`Expr::ParamRef` that survives the walk
//!    outside a macro body is rejected (it can only come from source
//!    code that uses sigils at top level, which is not legal).
//!
//! Post-expansion: every `Call`, `ParamRef`, `BinderRef`, `SigilRef`,
//! and `BinderSlot::{ParamRef, BinderRef}` is gone. The resulting
//! `PolicySet` has `defs: Vec::new()` and ordinary cedar/temporal ASTs.

use std::collections::BTreeMap;

use crate::ast::{Expr, ExprKind, MacroBody, MacroDef, MacroParam, PolicySet};
use crate::error::Span;
use crate::extension::temporal::ast::{
    self as tast, AggExpr, AggExprKind, BinderSlot, Call, CallArg, Condition, ConditionKind,
    NamedArg, Predicate, Sigil, Term, WithinSpec,
};

/// An error from the macro expansion pass.
#[derive(Debug, Clone)]
pub struct RawMacroError {
    pub message: String,
    pub span: Span,
}

impl std::fmt::Display for RawMacroError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for RawMacroError {}

fn err(message: impl Into<String>, span: Span) -> RawMacroError {
    RawMacroError {
        message: message.into(),
        span,
    }
}

/// Names that may not be used as a macro identifier — they would
/// either shadow Cedar built-ins (post-expansion call resolution would
/// be ambiguous) or temporal keywords (the grammar would never reach
/// the macro path). The temporal grammar already rejects most of these
/// as identifiers, so this list is the user-facing precaution.
const RESERVED_MACRO_NAMES: &[&str] = &[
    // Cedar built-in unary calls.
    "decimal", "datetime", "duration", "ip", // Temporal keywords / operators.
    "let", "in", "where", "for", "sum", "count", "tp", "formerly", "previous", "since",
    // Literals.
    "true", "false",
];

// ─── Public entry point ─────────────────────────────────────────────

/// Expand all macro calls in `ps` and consume `ps.defs`. After this
/// pass returns `Ok`, the AST contains no unresolved macro nodes and
/// `ps.defs` is empty; cedarify and the temporal evaluator may proceed
/// on the result without seeing macro syntax.
///
/// A namespace-qualified call (`Ns::Fn(args)`) is **not** a macro call — it is
/// an information-provider invocation (macros are single-segment by grammar) —
/// so expansion leaves that `Expr::Call` node intact for cedarify to hoist,
/// rather than rejecting it as an unknown macro.
pub fn expand(ps: &mut PolicySet) -> Result<(), RawMacroError> {
    let registry = Registry::build(&ps.defs)?;
    for def in &ps.defs {
        check_def(def, &registry)?;
    }
    for policy in &mut ps.policies {
        for cond in &mut policy.conditions {
            expand_cedar_expr(&mut cond.body, &registry)?;
        }
    }
    ps.defs.clear();
    Ok(())
}

/// Validate a set of macro `defs` in isolation — reserved / duplicate names
/// (via [`Registry::build`]) and each body's well-formedness (via `check_def`)
/// — without expanding anything. Any error's `span` indexes the source `defs`
/// were parsed from.
///
/// This is the subset of [`expand`]'s checks that a `def` can fail on its own.
/// The pipeline runs it on a *macro library* before merging the library's defs
/// into a policy (see `crate::api::merge_macro_library`), so a library error is
/// caught — and rendered — against the library source, not the policy source.
/// After that, every error [`expand`] can still raise over the merged set is
/// necessarily policy-authored.
pub fn check_defs(defs: &[MacroDef]) -> Result<(), RawMacroError> {
    let registry = Registry::build(defs)?;
    for def in defs {
        check_def(def, &registry)?;
    }
    Ok(())
}

// ─── Registry ───────────────────────────────────────────────────────

struct Registry<'a> {
    by_name: BTreeMap<String, &'a MacroDef>,
}

impl<'a> Registry<'a> {
    fn build(defs: &'a [MacroDef]) -> Result<Self, RawMacroError> {
        let mut by_name: BTreeMap<String, &MacroDef> = BTreeMap::new();
        for def in defs {
            if RESERVED_MACRO_NAMES.contains(&def.name.as_str()) {
                return Err(err(
                    format!(
                        "macro name `{}` is reserved (built-in or keyword); pick a different name",
                        def.name
                    ),
                    def.span,
                ));
            }
            if let Some(prev) = by_name.get(&def.name) {
                return Err(err(
                    format!(
                        "duplicate macro definition `{}` (previously defined at byte {})",
                        def.name, prev.span.start
                    ),
                    def.span,
                ));
            }
            by_name.insert(def.name.clone(), def);
        }
        Ok(Registry { by_name })
    }

    fn get(&self, name: &str) -> Option<&'a MacroDef> {
        self.by_name.get(name).copied()
    }
}

// ─── Per-def well-formedness check ──────────────────────────────────

/// Validate a single macro definition's body:
///   * Every `?p` reference names a declared parameter.
///   * No nested macro calls (`Call` in any position is rejected).
fn check_def(def: &MacroDef, _registry: &Registry<'_>) -> Result<(), RawMacroError> {
    let declared: std::collections::BTreeSet<&str> =
        def.params.iter().map(|p| p.name.as_str()).collect();
    match &def.body {
        MacroBody::Cedar(e) => check_cedar_body(e, &declared)?,
        MacroBody::TemporalCondition(c) => check_temporal_condition_body(c, &declared)?,
        MacroBody::TemporalAgg(a) => check_temporal_agg_body(a, &declared)?,
    }
    Ok(())
}

fn check_cedar_body(
    e: &Expr,
    declared: &std::collections::BTreeSet<&str>,
) -> Result<(), RawMacroError> {
    let span = e.span;
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Var(_) | ExprKind::Slot(_) => Ok(()),
        // A cedar macro body may not contain a `temporal { … }` or
        // `provider { … }` block. Cedar substitution treats these
        // blocks as leaves and does not descend into their sub-language
        // ASTs, so any reference to a cedar macro parameter inside such
        // a block would survive the expansion pass and reach lowering
        // unresolved. Even a *self-contained* block (no sigils) would
        // be re-evaluated on every call site rather than hoisted once,
        // which is a misleading semantic surprise. Rather than wire up
        // cross-layer substitution or document the gotcha, we reject
        // both shapes here.
        ExprKind::Extension(ext) => {
            let (kind, ext_span) = match ext {
                crate::extension::Extension::Temporal(t) => ("temporal", t.span),
            };
            Err(err(
                format!(
                    "in `def cedar` body: a `{kind} {{ … }}` block is not allowed inside a \
                     cedar macro (cedar macro bodies must be pure cedar expressions; lift \
                     the block to the call site instead)"
                ),
                ext_span,
            ))
        }
        ExprKind::ParamRef { name } => {
            if !declared.contains(name.as_str()) {
                return Err(err(
                    format!(
                        "in `def cedar` body: `?{name}` does not name a declared parameter \
                         (declared: {})",
                        fmt_params(declared)
                    ),
                    span,
                ));
            }
            Ok(())
        }
        ExprKind::Call { name, .. } => Err(err(
            format!(
                "in `def cedar` body: macro-in-macro is not supported \
                 (call to `{name}` inside a macro body)"
            ),
            span,
        )),
        ExprKind::MethodCall { receiver, args, .. } => {
            check_cedar_body(receiver, declared)?;
            for a in args {
                check_cedar_body(a, declared)?;
            }
            Ok(())
        }
        ExprKind::UnaryApp { expr, .. } => check_cedar_body(expr, declared),
        ExprKind::BinaryApp { left, right, .. } => {
            check_cedar_body(left, declared)?;
            check_cedar_body(right, declared)
        }
        ExprKind::GetAttr { expr, .. } => check_cedar_body(expr, declared),
        ExprKind::HasAttr { expr, .. } => check_cedar_body(expr, declared),
        ExprKind::Like { expr, .. } => check_cedar_body(expr, declared),
        ExprKind::Is { expr, in_expr, .. } => {
            check_cedar_body(expr, declared)?;
            if let Some(e) = in_expr {
                check_cedar_body(e, declared)?;
            }
            Ok(())
        }
        ExprKind::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => {
            check_cedar_body(cond, declared)?;
            check_cedar_body(then_expr, declared)?;
            check_cedar_body(else_expr, declared)
        }
        ExprKind::Set(elems) => {
            for e in elems {
                check_cedar_body(e, declared)?;
            }
            Ok(())
        }
        ExprKind::Record(entries) => {
            for v in entries.values() {
                check_cedar_body(v, declared)?;
            }
            Ok(())
        }
    }
}

fn check_temporal_condition_body(
    c: &Condition,
    declared: &std::collections::BTreeSet<&str>,
) -> Result<(), RawMacroError> {
    match &c.kind {
        ConditionKind::And { left, right } => {
            check_temporal_condition_body(left, declared)?;
            check_temporal_condition_body(right, declared)
        }
        // Internal-only (pin-relativization) — a macro body can never
        // contain one (the parser has no `||`), but recurse defensively.
        ConditionKind::Or { left, right } => {
            check_temporal_condition_body(left, declared)?;
            check_temporal_condition_body(right, declared)
        }
        ConditionKind::Not { inner } => check_temporal_condition_body(inner, declared),
        ConditionKind::Formerly { within, body } => {
            check_within_in_body(within, declared, c.span)?;
            check_temporal_condition_body(body, declared)
        }
        ConditionKind::Previous { within, body } => {
            check_within_in_body(within, declared, c.span)?;
            check_temporal_condition_body(body, declared)
        }
        ConditionKind::Since {
            left,
            within,
            right,
            ..
        } => {
            check_within_in_body(within, declared, c.span)?;
            check_temporal_condition_body(left, declared)?;
            check_temporal_condition_body(right, declared)
        }
        ConditionKind::Predicate(p) => {
            for arg in &p.args {
                check_temporal_term(&arg.value, declared, c.span)?;
            }
            Ok(())
        }
        ConditionKind::Comparison { left, right, .. } => {
            check_temporal_term(left, declared, c.span)?;
            check_temporal_term(right, declared, c.span)
        }
        ConditionKind::Tp { var } => check_binder_slot(var, declared, c.span),
        ConditionKind::Exists { var, body } => {
            check_binder_slot(&var.slot, declared, c.span)?;
            check_temporal_condition_body(body, declared)
        }
        ConditionKind::SigilRef { sigil, name } => check_sigil_ref(*sigil, name, declared, c.span),
        // A field-injection refinement in a `def temporal` body: check the
        // base like any condition and each injected field's term like a
        // predicate arg (so a `?p` in an injected value is validated
        // against the declared parameters).
        ConditionKind::Refine { base, fields, .. } => {
            check_temporal_condition_body(base, declared)?;
            for arg in fields {
                check_temporal_term(&arg.value, declared, c.span)?;
            }
            Ok(())
        }
        ConditionKind::Call { .. } => Err(err(
            "in `def temporal` body: macro-in-macro is not supported".to_string(),
            c.span,
        )),
    }
}

fn check_temporal_agg_body(
    a: &AggExpr,
    declared: &std::collections::BTreeSet<&str>,
) -> Result<(), RawMacroError> {
    match &a.kind {
        AggExprKind::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            check_binder_slot(bound_var, declared, a.span)?;
            for v in for_vars {
                check_binder_slot(&v.slot, declared, a.span)?;
            }
            check_temporal_condition_body(body, declared)
        }
        AggExprKind::Count { for_vars, body } => {
            for v in for_vars {
                check_binder_slot(&v.slot, declared, a.span)?;
            }
            check_temporal_condition_body(body, declared)
        }
        AggExprKind::Call { .. } => Err(err(
            "in `def temporal` body: macro-in-macro is not supported".to_string(),
            a.span,
        )),
    }
}

fn check_temporal_term(
    t: &Term,
    declared: &std::collections::BTreeSet<&str>,
    span: Span,
) -> Result<(), RawMacroError> {
    match t {
        Term::ParamRef(name) => {
            if !declared.contains(name.as_str()) {
                return Err(err(
                    format!(
                        "in `def temporal` body: `?{name}` does not name a declared parameter \
                         (declared: {})",
                        fmt_params(declared)
                    ),
                    span,
                ));
            }
            Ok(())
        }
        // `$t` in term position: any name is accepted at definition
        // time; uses are tied together by name (the gensym substitution
        // at expansion renames all occurrences of one name uniformly).
        Term::BinderRef(_) => Ok(()),
        Term::Array(items) => {
            for it in items {
                check_temporal_term(it, declared, span)?;
            }
            Ok(())
        }
        // An aggregate term (e.g. `count for … where φ` in a macro body): its
        // binders and `where` body are checked like an aggregation body.
        Term::Agg(agg) => check_temporal_agg_body(agg, declared),
        _ => Ok(()),
    }
}

fn check_binder_slot(
    s: &BinderSlot,
    declared: &std::collections::BTreeSet<&str>,
    span: Span,
) -> Result<(), RawMacroError> {
    match s {
        BinderSlot::Name(_) => Ok(()),
        BinderSlot::ParamRef(name) => {
            if !declared.contains(name.as_str()) {
                return Err(err(
                    format!(
                        "in `def temporal` body: `?{name}` does not name a declared parameter \
                         (declared: {})",
                        fmt_params(declared)
                    ),
                    span,
                ));
            }
            Ok(())
        }
        BinderSlot::BinderRef(_) => Ok(()),
    }
}

fn check_within_in_body(
    w: &WithinSpec,
    declared: &std::collections::BTreeSet<&str>,
    span: Span,
) -> Result<(), RawMacroError> {
    match w {
        WithinSpec::Concrete(_) => Ok(()),
        WithinSpec::ParamRef(name) => {
            if !declared.contains(name.as_str()) {
                return Err(err(
                    format!(
                        "in `def temporal` body: `?{name}` does not name a declared parameter \
                         (declared: {})",
                        fmt_params(declared)
                    ),
                    span,
                ));
            }
            Ok(())
        }
    }
}

fn check_sigil_ref(
    sigil: Sigil,
    name: &str,
    declared: &std::collections::BTreeSet<&str>,
    span: Span,
) -> Result<(), RawMacroError> {
    match sigil {
        Sigil::Param => {
            if !declared.contains(name) {
                return Err(err(
                    format!(
                        "in `def temporal` body: `?{name}` does not name a declared parameter \
                         (declared: {})",
                        fmt_params(declared)
                    ),
                    span,
                ));
            }
            Ok(())
        }
        Sigil::Binder => Ok(()),
    }
}

fn fmt_params(declared: &std::collections::BTreeSet<&str>) -> String {
    declared
        .iter()
        .map(|p| format!("?{p}"))
        .collect::<Vec<_>>()
        .join(", ")
}

// ─── Cedar expansion walk ───────────────────────────────────────────

/// Recursively expand calls in a cedar expression. Substituted macro
/// bodies contain no nested `Call` nodes (the well-formedness check
/// rejects macro-in-macro), so the walk doesn't need a depth flag.
fn expand_cedar_expr(e: &mut Expr, registry: &Registry<'_>) -> Result<(), RawMacroError> {
    let span = e.span;
    match &mut e.kind {
        ExprKind::Call { name, args } => {
            // Recursively expand the args first.
            for a in args.iter_mut() {
                expand_cedar_expr(a, registry)?;
            }
            // A namespace-qualified call (`Ns::Fn(args)`) is an information-
            // provider invocation, not a macro: macros are single-segment by
            // grammar, so a `::` name can only be a provider. Leave the `Call`
            // node in place (args already expanded) for cedarify to recognize
            // and hoist to `context.providers.<name>`; if the provider is
            // undeclared, validation reports it (cedarify does not fail the
            // parse). This is a structural check mirroring MFOTL, so an
            // undeclared provider surfaces as a friendly validation error
            // rather than a fatal "unknown macro".
            if name.contains("::") {
                return Ok(());
            }
            // Resolve the call.
            let def = registry.get(name).ok_or_else(|| {
                err(
                    format!(
                        "unknown function or macro `{name}` \
                         (not a Cedar built-in and not a declared macro)"
                    ),
                    span,
                )
            })?;
            let body = match &def.body {
                MacroBody::Cedar(e) => e.clone(),
                MacroBody::TemporalCondition(_) | MacroBody::TemporalAgg(_) => {
                    return Err(err(
                        format!(
                            "macro `{name}` is a temporal macro and cannot be called in a \
                             cedar expression position"
                        ),
                        span,
                    ));
                }
            };
            check_arity(def, args.len(), span)?;
            let substituted = substitute_cedar(body, def, args, span)?;
            *e = substituted;
            Ok(())
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            // A deferred (non-Cedar-builtin) method — potentially a provider
            // output method. Not a macro call itself: just expand the receiver
            // and arguments in place; cedarify resolves the method against the
            // provider declarations. (The receiver may bottom out at a provider
            // `Call`, which the arm above leaves in place.)
            expand_cedar_expr(receiver, registry)?;
            for a in args.iter_mut() {
                expand_cedar_expr(a, registry)?;
            }
            Ok(())
        }
        ExprKind::ParamRef { name } => {
            // A `?p` outside a macro body is a stray reference. (`?principal`
            // and `?resource` were already turned into `Slot`; only
            // generic-name references reach here.)
            Err(err(
                format!("stray macro parameter reference `?{name}` outside a macro body"),
                span,
            ))
        }
        ExprKind::Lit(_) | ExprKind::Var(_) | ExprKind::Slot(_) => Ok(()),
        ExprKind::Extension(ext) => expand_extension(ext, registry),
        ExprKind::UnaryApp { expr, .. } => expand_cedar_expr(expr, registry),
        ExprKind::BinaryApp { left, right, .. } => {
            expand_cedar_expr(left, registry)?;
            expand_cedar_expr(right, registry)
        }
        ExprKind::GetAttr { expr, .. } => expand_cedar_expr(expr, registry),
        ExprKind::HasAttr { expr, .. } => expand_cedar_expr(expr, registry),
        ExprKind::Like { expr, .. } => expand_cedar_expr(expr, registry),
        ExprKind::Is { expr, in_expr, .. } => {
            expand_cedar_expr(expr, registry)?;
            if let Some(e) = in_expr {
                expand_cedar_expr(e, registry)?;
            }
            Ok(())
        }
        ExprKind::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => {
            expand_cedar_expr(cond, registry)?;
            expand_cedar_expr(then_expr, registry)?;
            expand_cedar_expr(else_expr, registry)
        }
        ExprKind::Set(elems) => {
            for el in elems.iter_mut() {
                expand_cedar_expr(el, registry)?;
            }
            Ok(())
        }
        ExprKind::Record(entries) => {
            for v in entries.values_mut() {
                expand_cedar_expr(v, registry)?;
            }
            Ok(())
        }
    }
}

fn expand_extension(
    ext: &mut crate::extension::Extension,
    registry: &Registry<'_>,
) -> Result<(), RawMacroError> {
    use crate::extension::Extension;
    match ext {
        Extension::Temporal(t) => {
            let span = t.span;
            expand_temporal_condition(&mut t.condition, registry)?;
            // After expansion, re-run the temporal binding check on the
            // resolved body. (`Temporal::parse` skips it for bodies with
            // sigils; now that they're substituted, the check is
            // meaningful again.)
            crate::extension::temporal::check::check_condition(
                &t.condition,
                &std::collections::BTreeSet::new(),
            )
            .and_then(|()| crate::extension::temporal::check::check_leaf_closed(&t.condition))
            .and_then(|()| crate::extension::temporal::check::check_demands(&t.condition))
            .map_err(|e| {
                err(
                    format!("temporal binding check failed after expansion: {e}"),
                    span,
                )
            })?;
            Ok(())
        }
    }
}

// ─── Cedar substitution ─────────────────────────────────────────────

fn check_arity(def: &MacroDef, got: usize, span: Span) -> Result<(), RawMacroError> {
    if def.params.len() != got {
        return Err(err(
            format!(
                "macro `{}` expects {} argument(s), got {got}",
                def.name,
                def.params.len()
            ),
            span,
        ));
    }
    Ok(())
}

fn substitute_cedar(
    mut body: Expr,
    def: &MacroDef,
    args: &[Expr],
    _call_span: Span,
) -> Result<Expr, RawMacroError> {
    let map: BTreeMap<&str, &Expr> = def
        .params
        .iter()
        .zip(args.iter())
        .map(|(p, a)| (p.name.as_str(), a))
        .collect();
    subst_cedar_expr(&mut body, &map)?;
    Ok(body)
}

fn subst_cedar_expr(e: &mut Expr, map: &BTreeMap<&str, &Expr>) -> Result<(), RawMacroError> {
    if let ExprKind::ParamRef { name } = &e.kind
        && let Some(arg) = map.get(name.as_str())
    {
        // Splice the call-site argument verbatim — it keeps its own `.dw`
        // span, which is the precise source location for this sub-expression.
        *e = (*arg).clone();
        return Ok(());
    }
    let span = e.span;
    match &mut e.kind {
        ExprKind::ParamRef { name } => Err(err(
            format!("unbound macro parameter `?{name}` in macro body"),
            span,
        )),
        ExprKind::Lit(_) | ExprKind::Var(_) | ExprKind::Slot(_) | ExprKind::Extension(_) => Ok(()),
        ExprKind::Call { args, .. } => {
            for a in args.iter_mut() {
                subst_cedar_expr(a, map)?;
            }
            Ok(())
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            subst_cedar_expr(receiver, map)?;
            for a in args.iter_mut() {
                subst_cedar_expr(a, map)?;
            }
            Ok(())
        }
        ExprKind::UnaryApp { expr, .. } => subst_cedar_expr(expr, map),
        ExprKind::BinaryApp { left, right, .. } => {
            subst_cedar_expr(left, map)?;
            subst_cedar_expr(right, map)
        }
        ExprKind::GetAttr { expr, .. } => subst_cedar_expr(expr, map),
        ExprKind::HasAttr { expr, .. } => subst_cedar_expr(expr, map),
        ExprKind::Like { expr, .. } => subst_cedar_expr(expr, map),
        ExprKind::Is { expr, in_expr, .. } => {
            subst_cedar_expr(expr, map)?;
            if let Some(e) = in_expr {
                subst_cedar_expr(e, map)?;
            }
            Ok(())
        }
        ExprKind::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => {
            subst_cedar_expr(cond, map)?;
            subst_cedar_expr(then_expr, map)?;
            subst_cedar_expr(else_expr, map)
        }
        ExprKind::Set(elems) => {
            for el in elems.iter_mut() {
                subst_cedar_expr(el, map)?;
            }
            Ok(())
        }
        ExprKind::Record(entries) => {
            for v in entries.values_mut() {
                subst_cedar_expr(v, map)?;
            }
            Ok(())
        }
    }
}

// ─── Field-injection refinement folding ─────────────────────────────

/// Describe a condition's shape for a `Refine`-base error message.
fn condition_shape(c: &Condition) -> &'static str {
    match &c.kind {
        ConditionKind::And { .. } => "a conjunction (`&&`)",
        ConditionKind::Or { .. } => "a disjunction (internal)",
        ConditionKind::Not { .. } => "a negation (`!`)",
        ConditionKind::Formerly { .. } => "a `formerly` operator",
        ConditionKind::Previous { .. } => "a `previous` operator",
        ConditionKind::Since { .. } => "a `since` operator",
        ConditionKind::Comparison { .. } => "a comparison",
        ConditionKind::Exists { .. } => "an `exists` binder",
        ConditionKind::Tp { .. } => "a `tp(…)`",
        ConditionKind::Predicate(_) => "a predicate",
        ConditionKind::Call(_) => "an unexpanded macro call",
        ConditionKind::SigilRef { .. } => "an unresolved macro parameter",
        ConditionKind::Refine { .. } => "a refinement",
    }
}

/// Fold a `Refine` node whose `base` has already been fully resolved
/// (both the macro-substitution path and the direct-write path resolve
/// `base` before calling here). The base must be a single [`Predicate`];
/// its `args` gain the injected `fields` (append = conjoin, so a same-named
/// field is ANDed against the event field by the evaluator). The `Refine`
/// node is replaced in place by the augmented predicate.
///
/// `base` and `fields` are moved out of the original `Refine` by the
/// caller (via `std::mem::take` on the `Condition`), so this takes them by
/// value and returns the folded `Condition`.
fn fold_refine(
    base: Condition,
    fields: Vec<NamedArg>,
    span: Span,
) -> Result<Condition, RawMacroError> {
    match base.kind {
        ConditionKind::Predicate(mut p) => {
            p.args.extend(fields);
            Ok(Condition {
                span: base.span,
                kind: ConditionKind::Predicate(p),
            })
        }
        other => Err(err(
            format!(
                "a `{{ … }}` field-injection applies only to a single predicate, \
                 but the refined term is {}",
                condition_shape(&Condition {
                    span: base.span,
                    kind: other,
                })
            ),
            span,
        )),
    }
}

/// Take a `Refine`'s `base` and `fields` out of a `Condition`, leaving a
/// harmless placeholder behind. Used by both fold paths so the borrow of
/// `c` can be released before rebuilding it.
fn take_refine(c: &mut Condition) -> Option<(Condition, Vec<NamedArg>, Span)> {
    match &mut c.kind {
        ConditionKind::Refine { base, fields, span } => {
            let span = *span;
            let base = std::mem::replace(
                base.as_mut(),
                Condition {
                    span,
                    kind: ConditionKind::Predicate(Predicate {
                        span,
                        namespace: Vec::new(),
                        action: String::new(),
                        kind: String::new(),
                        args: Vec::new(),
                    }),
                },
            );
            let fields = std::mem::take(fields);
            Some((base, fields, span))
        }
        _ => None,
    }
}

// ─── Temporal expansion ─────────────────────────────────────────────

fn expand_temporal_condition(
    c: &mut Condition,
    registry: &Registry<'_>,
) -> Result<(), RawMacroError> {
    match &mut c.kind {
        ConditionKind::And { left, right } => {
            expand_temporal_condition(left, registry)?;
            expand_temporal_condition(right, registry)
        }
        // Internal-only (pin-relativization); never present at expansion
        // time (the rewrite runs after expansion), but recurse defensively.
        ConditionKind::Or { left, right } => {
            expand_temporal_condition(left, registry)?;
            expand_temporal_condition(right, registry)
        }
        ConditionKind::Not { inner } => expand_temporal_condition(inner, registry),
        ConditionKind::Formerly { within, body } => {
            check_concrete_within(within, c.span)?;
            expand_temporal_condition(body, registry)
        }
        ConditionKind::Previous { within, body } => {
            check_concrete_within(within, c.span)?;
            expand_temporal_condition(body, registry)
        }
        ConditionKind::Since {
            left,
            within,
            right,
            ..
        } => {
            check_concrete_within(within, c.span)?;
            expand_temporal_condition(left, registry)?;
            expand_temporal_condition(right, registry)
        }
        ConditionKind::Predicate(_) | ConditionKind::Tp { .. } => Ok(()),
        // A comparison operand may be an aggregate that is itself a macro
        // call (`(sum_formerly(…)) == n`) or wraps a macro body; expand
        // each operand.
        ConditionKind::Comparison { left, right, .. } => {
            expand_temporal_operand(left, registry)?;
            expand_temporal_operand(right, registry)
        }
        ConditionKind::Exists { body, .. } => expand_temporal_condition(body, registry),
        ConditionKind::Call(call) => {
            // Recursively expand args first.
            let call = std::mem::replace(
                call,
                Call {
                    span: c.span,
                    name: String::new(),
                    args: Vec::new(),
                },
            );
            let expanded = expand_temporal_call_to_condition(call, registry)?;
            *c = expanded;
            Ok(())
        }
        ConditionKind::SigilRef { sigil, name } => Err(err(
            format!(
                "stray {} reference `{}{name}` outside a macro body",
                match sigil {
                    Sigil::Param => "macro parameter",
                    Sigil::Binder => "macro binder",
                },
                match sigil {
                    Sigil::Param => "?",
                    Sigil::Binder => "$",
                }
            ),
            c.span,
        )),
        // A direct-write refinement `P::kind{a}{b}` (no macro). Expand the
        // base first (folding away any nested refinement / macro call it
        // contains), then conjoin the injected fields onto the resolved
        // predicate.
        ConditionKind::Refine { base, .. } => {
            expand_temporal_condition(base, registry)?;
            let (base, fields, span) = take_refine(c).expect("c is a Refine");
            *c = fold_refine(base, fields, span)?;
            Ok(())
        }
    }
}

fn expand_temporal_agg(a: &mut AggExpr, registry: &Registry<'_>) -> Result<(), RawMacroError> {
    match &mut a.kind {
        AggExprKind::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            check_concrete_slot(bound_var, a.span)?;
            for v in for_vars.iter() {
                check_concrete_slot(&v.slot, a.span)?;
            }
            expand_temporal_condition(body, registry)
        }
        AggExprKind::Count { for_vars, body } => {
            for v in for_vars.iter() {
                check_concrete_slot(&v.slot, a.span)?;
            }
            expand_temporal_condition(body, registry)
        }
        AggExprKind::Call(call) => {
            let call = std::mem::replace(
                call,
                Call {
                    span: a.span,
                    name: String::new(),
                    args: Vec::new(),
                },
            );
            let expanded = expand_temporal_call_to_agg(call, registry)?;
            *a = expanded;
            Ok(())
        }
    }
}

/// Expand a comparison-operand term: an aggregate term is expanded like an
/// aggregation (resolving an aggregate-valued macro call); a bare macro sigil
/// (`?p` / `$t`) in operand position outside a macro body is a stray reference
/// and rejected here, exactly as [`check_concrete_slot`] rejects one in binder
/// position and [`check_concrete_within`] in `within` position. Without this,
/// an unexpanded operand sigil would survive validation and then panic the
/// evaluator at authorize time (`resolve_term`) — a validated policy crashing
/// the authorizer. Any other term carries no macro condition/aggregate.
fn expand_temporal_operand(t: &mut Term, registry: &Registry<'_>) -> Result<(), RawMacroError> {
    match t {
        Term::Agg(agg) => expand_temporal_agg(agg, registry),
        Term::ParamRef(p) => Err(err(
            format!(
                "stray macro parameter reference `?{p}` in a comparison-operand position \
                 outside a macro body"
            ),
            // Term carries no span of its own here; the enclosing condition's
            // span is attached by the caller's `?` propagation site.
            Span::new(0, 0),
        )),
        Term::BinderRef(b) => Err(err(
            format!(
                "stray macro binder reference `${b}` in a comparison-operand position \
                 outside a macro body"
            ),
            Span::new(0, 0),
        )),
        _ => Ok(()),
    }
}

fn check_concrete_within(w: &WithinSpec, span: Span) -> Result<(), RawMacroError> {
    match w {
        WithinSpec::Concrete(_) => Ok(()),
        WithinSpec::ParamRef(p) => Err(err(
            format!(
                "stray macro parameter reference `?{p}` in a `within` position outside a macro body"
            ),
            span,
        )),
    }
}

fn check_concrete_slot(s: &BinderSlot, span: Span) -> Result<(), RawMacroError> {
    match s {
        BinderSlot::Name(_) => Ok(()),
        BinderSlot::ParamRef(p) => Err(err(
            format!(
                "stray macro parameter reference `?{p}` in a binder position outside a macro body"
            ),
            span,
        )),
        BinderSlot::BinderRef(b) => Err(err(
            format!(
                "stray macro binder reference `${b}` in a binder position outside a macro body"
            ),
            span,
        )),
    }
}

// ─── Temporal call resolution + substitution ────────────────────────

fn expand_temporal_call_to_condition(
    mut call: Call,
    registry: &Registry<'_>,
) -> Result<Condition, RawMacroError> {
    // Resolve the macro.
    let def = registry.get(&call.name).ok_or_else(|| {
        err(
            format!("unknown macro `{}` (no declared `def temporal`)", call.name),
            call.span,
        )
    })?;
    let body = match &def.body {
        MacroBody::TemporalCondition(c) => c.clone(),
        MacroBody::Cedar(_) => {
            return Err(err(
                format!(
                    "macro `{}` is a cedar macro and cannot be called in a temporal condition position",
                    call.name
                ),
                call.span,
            ));
        }
        MacroBody::TemporalAgg(_) => {
            return Err(err(
                format!(
                    "macro `{}` is an aggregation macro; it must appear as a comparison operand \
                     (e.g. `exists (n: Long). ((…) == n && n > 0)`), not as a standalone condition",
                    call.name
                ),
                call.span,
            ));
        }
    };
    check_arity(def, call.args.len(), call.span)?;
    expand_temporal_call_args(&mut call.args, registry)?;
    let substituted = substitute_temporal_condition(body, def, registry, &call)?;
    Ok(substituted)
}

/// Expand the macro-call arguments in place before substitution.
///
/// Call-site arguments are not a macro body, so — unlike a body — they may
/// contain macro calls. The parser tags a bare macro-call argument as
/// `CallArg::Condition` (the grammar tries `condition` before `term`, and a
/// `call` is a valid condition atom). That tagging is correct for a
/// condition-producing macro, but an *aggregation*-producing macro call is
/// really a value term (an aggregate is a `Term`, legal as a comparison
/// operand). So here we split by the callee's kind:
///
///   * an aggregation-macro-call argument is expanded to its `AggExpr` and
///     **re-tagged** as `CallArg::Term(Term::Agg(...))`, so it can fill a
///     term-position parameter (e.g. the `?A` in `bind(?n, ?A, ?B)`'s
///     `?A == ?n`). The comparison-operand-only rule is then checked
///     downstream, exactly as for a raw inline aggregate.
///   * any other condition argument (including a condition-macro call) is
///     expanded as a condition, unchanged from before.
fn expand_temporal_call_args(
    args: &mut [CallArg],
    registry: &Registry<'_>,
) -> Result<(), RawMacroError> {
    for arg in args.iter_mut() {
        let CallArg::Condition(c) = arg else { continue };
        // Is this argument a bare call to an aggregation macro? If so it is
        // a value, not a condition — expand it as an aggregate and re-tag.
        if let ConditionKind::Call(inner) = &c.kind
            && matches!(
                registry.get(&inner.name).map(|d| &d.body),
                Some(MacroBody::TemporalAgg(_))
            )
        {
            let ConditionKind::Call(inner) = std::mem::replace(
                &mut c.kind,
                ConditionKind::Tp {
                    var: BinderSlot::Name(String::new()),
                },
            ) else {
                unreachable!("just matched ConditionKind::Call")
            };
            let agg = expand_temporal_call_to_agg(inner, registry)?;
            *arg = CallArg::Term(Term::Agg(Box::new(agg)));
            continue;
        }
        // An ordinary condition argument (or a condition-macro call).
        expand_temporal_condition(c, registry)?;
    }
    Ok(())
}

fn expand_temporal_call_to_agg(
    mut call: Call,
    registry: &Registry<'_>,
) -> Result<AggExpr, RawMacroError> {
    let def = registry.get(&call.name).ok_or_else(|| {
        err(
            format!("unknown macro `{}` (no declared `def temporal`)", call.name),
            call.span,
        )
    })?;
    let body = match &def.body {
        MacroBody::TemporalAgg(a) => a.clone(),
        MacroBody::Cedar(_) => {
            return Err(err(
                format!(
                    "macro `{}` is a cedar macro and cannot be called in an aggregation position",
                    call.name
                ),
                call.span,
            ));
        }
        MacroBody::TemporalCondition(_) => {
            return Err(err(
                format!(
                    "macro `{}` is a condition macro and cannot be used as an aggregation value \
                     (a comparison operand); use it in a condition position instead",
                    call.name
                ),
                call.span,
            ));
        }
    };
    check_arity(def, call.args.len(), call.span)?;
    expand_temporal_call_args(&mut call.args, registry)?;
    let substituted = substitute_temporal_agg(body, def, registry, &call)?;
    Ok(substituted)
}

// ─── Temporal substitution ──────────────────────────────────────────

/// Build the substitution maps for a macro call:
///   * `param_to_arg`: maps `?p` name → call-site argument.
///   * `binder_gensym`: maps `$t` name → freshly-minted concrete name
///     (`<name>$<call-span-start>`).
///
/// Single-identifier checking for binder-position params happens
/// inline at the substitution site (`subst_binder_slot`) rather than
/// being pre-tagged on the registry — the position is known
/// syntactically at substitution time, so the check is local.
struct SubstMaps<'a> {
    param_to_arg: BTreeMap<&'a str, &'a CallArg>,
    binder_gensym: BTreeMap<String, String>,
    call_span: Span,
    macro_name: &'a str,
}

impl<'a> SubstMaps<'a> {
    fn build(def: &'a MacroDef, call: &'a Call) -> Self {
        let param_to_arg: BTreeMap<&str, &CallArg> = def
            .params
            .iter()
            .zip(call.args.iter())
            .map(|(p, a)| (p.name.as_str(), a))
            .collect();
        SubstMaps {
            param_to_arg,
            binder_gensym: BTreeMap::new(),
            call_span: call.span,
            macro_name: def.name.as_str(),
        }
    }

    /// Gensym (memoized) the concrete name to substitute for `$t`.
    fn gensym_for(&mut self, binder_name: &str) -> String {
        if let Some(s) = self.binder_gensym.get(binder_name) {
            return s.clone();
        }
        let s = format!("{}${}", binder_name, self.call_span.start);
        self.binder_gensym
            .insert(binder_name.to_string(), s.clone());
        s
    }

    /// Lookup the call-site argument for `?p`, returning an error if
    /// it's not declared.
    fn arg_for(&self, param_name: &str, span: Span) -> Result<&'a CallArg, RawMacroError> {
        self.param_to_arg.get(param_name).copied().ok_or_else(|| {
            err(
                format!(
                    "unbound macro parameter `?{param_name}` in body of `{}`",
                    self.macro_name
                ),
                span,
            )
        })
    }
}

fn substitute_temporal_condition(
    mut body: Condition,
    def: &MacroDef,
    _registry: &Registry<'_>,
    call: &Call,
) -> Result<Condition, RawMacroError> {
    let mut maps = SubstMaps::build(def, call);
    subst_temporal_condition(&mut body, &mut maps)?;
    Ok(body)
}

fn substitute_temporal_agg(
    mut body: AggExpr,
    def: &MacroDef,
    _registry: &Registry<'_>,
    call: &Call,
) -> Result<AggExpr, RawMacroError> {
    let mut maps = SubstMaps::build(def, call);
    subst_temporal_agg(&mut body, &mut maps)?;
    Ok(body)
}

fn subst_temporal_condition(
    c: &mut Condition,
    maps: &mut SubstMaps<'_>,
) -> Result<(), RawMacroError> {
    // Replace a whole-condition sigil reference first.
    if let ConditionKind::SigilRef { sigil, name } = &c.kind {
        match sigil {
            Sigil::Param => {
                // Splice the call-site argument's condition AST here.
                let arg = maps.arg_for(name, c.span)?;
                match arg {
                    CallArg::Condition(arg_c) => {
                        *c = arg_c.clone();
                        return Ok(());
                    }
                    _ => {
                        return Err(err(
                            format!(
                                "macro `{}` parameter `?{name}` is used in a condition position, \
                                 so the call-site argument must be a temporal condition (got a different shape)",
                                maps.macro_name
                            ),
                            c.span,
                        ));
                    }
                }
            }
            Sigil::Binder => {
                // A whole-condition `$t` is unusual but harmless: it
                // means "the condition is just this gensym name" — but
                // a name isn't a condition. Reject.
                return Err(err(
                    format!("macro binder `${name}` used as a whole condition has no meaning"),
                    c.span,
                ));
            }
        }
    }

    match &mut c.kind {
        ConditionKind::And { left, right } => {
            subst_temporal_condition(left, maps)?;
            subst_temporal_condition(right, maps)
        }
        // Internal-only (pin-relativization); never present in a macro
        // body, but recurse defensively.
        ConditionKind::Or { left, right } => {
            subst_temporal_condition(left, maps)?;
            subst_temporal_condition(right, maps)
        }
        ConditionKind::Not { inner } => subst_temporal_condition(inner, maps),
        ConditionKind::Formerly { within, body } => {
            subst_within(within, maps, c.span)?;
            subst_temporal_condition(body, maps)
        }
        ConditionKind::Previous { within, body } => {
            subst_within(within, maps, c.span)?;
            subst_temporal_condition(body, maps)
        }
        ConditionKind::Since {
            left,
            within,
            right,
            ..
        } => {
            subst_within(within, maps, c.span)?;
            subst_temporal_condition(left, maps)?;
            subst_temporal_condition(right, maps)
        }
        ConditionKind::Predicate(p) => {
            for arg in &mut p.args {
                subst_temporal_term(&mut arg.value, maps, c.span)?;
            }
            Ok(())
        }
        ConditionKind::Comparison { left, right, .. } => {
            subst_temporal_term(left, maps, c.span)?;
            subst_temporal_term(right, maps, c.span)
        }
        ConditionKind::Tp { var } => subst_binder_slot(var, maps, c.span),
        ConditionKind::Exists { var, body } => {
            subst_binder_slot(&mut var.slot, maps, c.span)?;
            subst_temporal_condition(body, maps)
        }
        // A field-injection refinement `?s{ f: v }` (or a nested one) in a
        // macro body: substitute the base first (a `?s` base resolves to a
        // concrete predicate via the early SigilRef branch on re-entry) and
        // resolve any `?p` in the injected values, then conjoin the fields
        // onto the resolved predicate.
        ConditionKind::Refine { base, fields, .. } => {
            subst_temporal_condition(base, maps)?;
            for arg in fields.iter_mut() {
                subst_temporal_term(&mut arg.value, maps, c.span)?;
            }
            let (base, fields, span) = take_refine(c).expect("c is a Refine");
            *c = fold_refine(base, fields, span)?;
            Ok(())
        }
        // Already handled via the early SigilRef branch above; should
        // never reach here.
        ConditionKind::SigilRef { .. } => unreachable!(),
        // The no-macro-in-macro check rejects this before substitution.
        ConditionKind::Call(_) => unreachable!("macro-in-macro should have been rejected"),
    }
}

fn subst_temporal_agg(a: &mut AggExpr, maps: &mut SubstMaps<'_>) -> Result<(), RawMacroError> {
    match &mut a.kind {
        AggExprKind::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            subst_binder_slot(bound_var, maps, a.span)?;
            for v in for_vars.iter_mut() {
                subst_binder_slot(&mut v.slot, maps, a.span)?;
            }
            subst_temporal_condition(body, maps)
        }
        AggExprKind::Count { for_vars, body } => {
            for v in for_vars.iter_mut() {
                subst_binder_slot(&mut v.slot, maps, a.span)?;
            }
            subst_temporal_condition(body, maps)
        }
        AggExprKind::Call(_) => unreachable!("macro-in-macro should have been rejected"),
    }
}

/// Substitute a `WithinSpec`: a `ParamRef("w")` resolves to the
/// call-site argument's `Interval`. The argument must be a `within`
/// clause (parsed as `CallArg::Within`); other shapes are kind
/// mismatches.
fn subst_within(
    w: &mut WithinSpec,
    maps: &mut SubstMaps<'_>,
    span: Span,
) -> Result<(), RawMacroError> {
    let name = match w {
        WithinSpec::Concrete(_) => return Ok(()),
        WithinSpec::ParamRef(name) => name.clone(),
    };
    let arg = maps.arg_for(&name, span)?;
    match arg {
        CallArg::Within(interval) => {
            *w = WithinSpec::Concrete(*interval);
            Ok(())
        }
        _ => Err(err(
            format!(
                "macro `{}` parameter `?{name}` is used in a `within` position; \
                 the call-site argument must be an interval literal `<n><unit>` (e.g. `1h`)",
                maps.macro_name
            ),
            span,
        )),
    }
}

fn subst_temporal_term(
    t: &mut Term,
    maps: &mut SubstMaps<'_>,
    span: Span,
) -> Result<(), RawMacroError> {
    match t {
        Term::ParamRef(name) => {
            let arg = maps.arg_for(name, span)?;
            match arg {
                // A term-position `?p` argument: any `Term` (including
                // a literal, a Var, a wildcard) splices in directly.
                CallArg::Term(arg_t) => {
                    *t = arg_t.clone();
                    Ok(())
                }
                // A condition-position arg in a term slot is a kind
                // mismatch.
                CallArg::Condition(_) | CallArg::Within(_) => Err(err(
                    format!(
                        "macro `{}` parameter `?{name}` used in a term position; \
                         the call-site argument has the wrong shape",
                        maps.macro_name
                    ),
                    span,
                )),
            }
        }
        Term::BinderRef(name) => {
            let g = maps.gensym_for(name);
            *t = Term::Var(g);
            Ok(())
        }
        Term::Array(items) => {
            for it in items.iter_mut() {
                subst_temporal_term(it, maps, span)?;
            }
            Ok(())
        }
        // An aggregate term in a macro body (`(sum ?a for … where …) == ?n`):
        // substitute inside it like an aggregation body.
        Term::Agg(agg) => subst_temporal_agg(agg, maps),
        _ => Ok(()),
    }
}

fn subst_binder_slot(
    s: &mut BinderSlot,
    maps: &mut SubstMaps<'_>,
    span: Span,
) -> Result<(), RawMacroError> {
    match s {
        BinderSlot::Name(_) => Ok(()),
        BinderSlot::ParamRef(name) => {
            // Find the parameter index so we can use the binder-pos
            // single-identifier check.
            // The arg must be a CallArg::Term(Term::Var(name)).
            let arg = maps.arg_for(name, span)?;
            match arg {
                CallArg::Term(Term::Var(ident)) => {
                    *s = BinderSlot::Name(ident.clone());
                    Ok(())
                }
                _ => Err(err(
                    format!(
                        "macro `{}` parameter `?{name}` is used in a binder position, \
                         so the call-site argument must be a single identifier",
                        maps.macro_name
                    ),
                    maps.call_span,
                )),
            }
        }
        BinderSlot::BinderRef(name) => {
            let g = maps.gensym_for(name);
            *s = BinderSlot::Name(g);
            Ok(())
        }
    }
}

// Currently unused: kept to keep the trait-bound on `tast` from being
// trimmed by the "unused imports" warning. Replace this with a real use
// when providers grow macro support.
#[allow(dead_code)]
fn _silence_unused_imports() {
    let _: Option<&tast::Predicate> = None;
    let _: Option<&MacroParam> = None;
}

#[cfg(test)]
mod tests {
    //! Macro expansion tests. We parse a source string through the same
    //! pipeline used by the public `parse` API (parser + expander), then
    //! poke at the resulting AST to assert the macro nodes are gone and
    //! the substitution shapes match expectations.

    use super::*;
    use crate::ast::{ExprKind, PolicySet};
    use crate::parser::parse_policies;

    fn parse_and_expand(src: &str) -> Result<PolicySet, RawMacroError> {
        let mut ps = parse_policies(src).expect("parse should succeed");
        expand(&mut ps)?;
        Ok(ps)
    }

    fn must_expand(src: &str) -> PolicySet {
        parse_and_expand(src).unwrap_or_else(|e| panic!("expansion failed: {e}"))
    }

    fn must_fail(src: &str) -> RawMacroError {
        parse_and_expand(src)
            .err()
            .unwrap_or_else(|| panic!("expansion unexpectedly succeeded"))
    }

    // ─── Positive: cedar macros ─────────────────────────────────────

    #[test]
    fn cedar_macro_substitutes_param() {
        let ps = must_expand(
            r#"
                def cedar is_alice(?u) { ?u == User::"alice" };
                permit (principal, action, resource)
                when { is_alice(principal) };
            "#,
        );
        assert_eq!(ps.defs.len(), 0, "defs consumed after expansion");
        // Body should now be `principal == User::"alice"`.
        let body = &ps.policies[0].conditions[0].body;
        match &body.kind {
            ExprKind::BinaryApp { op, left, right } => {
                assert_eq!(*op, crate::ast::BinOp::Eq);
                assert!(
                    matches!(left.kind, ExprKind::Var(_)),
                    "lhs is principal var"
                );
                assert!(matches!(right.kind, ExprKind::Lit(_)), "rhs is entity lit");
            }
            other => panic!("expected BinaryApp after expansion, got {other:?}"),
        }
    }

    #[test]
    fn cedar_macro_used_in_two_policies() {
        let ps = must_expand(
            r#"
                def cedar is_alice(?u) { ?u == User::"alice" };
                permit (principal, action, resource)
                when { is_alice(principal) };
                permit (principal, action, resource)
                when { is_alice(resource) };
            "#,
        );
        assert_eq!(ps.policies.len(), 2);
        for p in &ps.policies {
            let body = &p.conditions[0].body;
            assert!(matches!(body.kind, ExprKind::BinaryApp { .. }), "expanded");
        }
    }

    // ─── Positive: temporal condition macros ────────────────────────

    #[test]
    fn temporal_condition_macro_expands_inline() {
        let ps = must_expand(
            r#"
                def temporal recent_login() {
                    formerly within 1h Drupe::Action::"Login"::request{ user: principal }
                };
                permit (principal, action, resource)
                when temporal { recent_login() };
            "#,
        );
        // The temporal block should now contain a Formerly directly.
        let body = &ps.policies[0].conditions[0].body;
        match &body.kind {
            ExprKind::Extension(crate::extension::Extension::Temporal(t)) => {
                match &t.condition.kind {
                    ConditionKind::Formerly { .. } => {}
                    other => panic!("expected Formerly after expansion, got {other:?}"),
                }
            }
            other => panic!("expected temporal extension, got {other:?}"),
        }
    }

    #[test]
    fn temporal_condition_macro_with_condition_param() {
        // ?s gets substituted; the body uses `?s && something`.
        let ps = must_expand(
            r#"
                def temporal both(?s) {
                    formerly within 1h (?s && Drupe::Action::"Login"::request{})
                };
                permit (principal, action, resource)
                when temporal { both(Drupe::Action::"Logout"::request{}) };
            "#,
        );
        // No leftover Call or SigilRef anywhere.
        let body = &ps.policies[0].conditions[0].body;
        let cond = match &body.kind {
            ExprKind::Extension(crate::extension::Extension::Temporal(t)) => &t.condition,
            other => panic!("expected temporal extension, got {other:?}"),
        };
        assert!(no_macro_residue_in_condition(cond), "no macro residue");
    }

    // ─── Field-injection refinement folding ─────────────────────────

    /// Extract the (single) temporal condition from an expanded policy.
    fn temporal_cond(ps: &PolicySet) -> &Condition {
        match &ps.policies[0].conditions[0].body.kind {
            ExprKind::Extension(crate::extension::Extension::Temporal(t)) => &t.condition,
            other => panic!("expected temporal extension, got {other:?}"),
        }
    }

    /// Find a predicate's arg value rendered as a debug string, for
    /// assertions that a field was (or was not) injected.
    fn pred_of(c: &Condition) -> &crate::extension::temporal::ast::Predicate {
        match &c.kind {
            ConditionKind::Predicate(p) => p,
            other => panic!("expected Predicate, got {other:?}"),
        }
    }

    #[test]
    fn refined_sigil_arg_conjoins_field_onto_predicate() {
        // The core `?s{ field: value }` case: a condition macro refines its
        // predicate-valued argument with an injected field. After
        // expansion the leaf is a plain Predicate whose args include BOTH
        // the caller's inline field and the injected one — proving the
        // fold ran and appended.
        let ps = must_expand(
            r#"
                def temporal approved_recently(?w, ?s) {
                    formerly within ?w (?s{ status: "approved" })
                };
                permit (principal, action, resource)
                when temporal {
                    approved_recently(1h, Drupe::Action::"Transfer"::request{ amount: * })
                };
            "#,
        );
        let cond = temporal_cond(&ps);
        assert!(no_macro_residue_in_condition(cond), "no macro residue");
        // formerly within 1h <Predicate>.
        let body = match &cond.kind {
            ConditionKind::Formerly { body, .. } => body,
            other => panic!("expected Formerly, got {other:?}"),
        };
        let p = pred_of(body);
        assert_eq!(p.action, "Transfer");
        // Caller's `amount: a` survives, injected `status: "approved"` is
        // appended — the leaf is a single flat predicate, not a Refine.
        let names: Vec<&str> = p.args.iter().map(|a| a.name.as_str()).collect();
        assert!(names.contains(&"amount"), "caller field kept: {names:?}");
        assert!(
            names.contains(&"status"),
            "injected field present: {names:?}"
        );
        let status = p.args.iter().find(|a| a.name == "status").unwrap();
        assert!(
            matches!(&status.value, Term::String(s) if s == "approved"),
            "injected value is the literal \"approved\", got {:?}",
            status.value
        );
    }

    #[test]
    fn refinement_without_injection_is_identical_to_plain_predicate() {
        // NEGATIVE CONTROL: the SAME macro/policy but WITHOUT the `{ status:
        // … }` refinement must expand to a predicate that does NOT carry a
        // `status` arg. This proves the `status` in the positive test comes
        // from the injection, not from some coincidental path.
        let ps = must_expand(
            r#"
                def temporal approved_recently(?w, ?s) {
                    formerly within ?w (?s)
                };
                permit (principal, action, resource)
                when temporal {
                    approved_recently(1h, Drupe::Action::"Transfer"::request{ amount: * })
                };
            "#,
        );
        let cond = temporal_cond(&ps);
        let body = match &cond.kind {
            ConditionKind::Formerly { body, .. } => body,
            other => panic!("expected Formerly, got {other:?}"),
        };
        let p = pred_of(body);
        let names: Vec<&str> = p.args.iter().map(|a| a.name.as_str()).collect();
        assert!(names.contains(&"amount"), "caller field kept: {names:?}");
        assert!(
            !names.contains(&"status"),
            "no injection means no `status` arg, got {names:?}"
        );
    }

    #[test]
    fn direct_write_refinement_folds_without_a_macro() {
        // D5: the refinement operator works on a directly-written predicate
        // too, no macro involved. `P{a}{b}` folds to a single Predicate.
        let ps = must_expand(
            r#"
                permit (principal, action, resource)
                when temporal {
                    formerly within 1h Drupe::Action::"Transfer"::request{ amount: * }{ status: "approved" }
                };
            "#,
        );
        let cond = temporal_cond(&ps);
        assert!(no_macro_residue_in_condition(cond), "no macro residue");
        let body = match &cond.kind {
            ConditionKind::Formerly { body, .. } => body,
            other => panic!("expected Formerly, got {other:?}"),
        };
        let p = pred_of(body);
        let names: Vec<&str> = p.args.iter().map(|a| a.name.as_str()).collect();
        assert!(
            names.contains(&"amount") && names.contains(&"status"),
            "both fields folded onto one predicate: {names:?}"
        );
    }

    #[test]
    fn chained_direct_write_blocks_all_fold() {
        // `P{}{a}{b}` — two chained blocks fold onto one predicate.
        let ps = must_expand(
            r#"
                permit (principal, action, resource)
                when temporal {
                    Drupe::Action::"Transfer"::request{}{ status: "approved" }{ region: "us" }
                };
            "#,
        );
        let cond = temporal_cond(&ps);
        assert!(no_macro_residue_in_condition(cond), "no macro residue");
        let p = pred_of(cond);
        let names: Vec<&str> = p.args.iter().map(|a| a.name.as_str()).collect();
        assert!(
            names.contains(&"status") && names.contains(&"region"),
            "both chained blocks folded: {names:?}"
        );
    }

    #[test]
    fn refining_a_non_predicate_is_a_static_error() {
        // D2: if the refined base resolves to something that is NOT a
        // single predicate (here, a conjunction passed as `?s`), the fold
        // must fail with a clear error rather than silently doing nothing.
        let e = must_fail(
            r#"
                def temporal refine_it(?s) {
                    ?s{ status: "approved" }
                };
                permit (principal, action, resource)
                when temporal {
                    refine_it(Drupe::Action::"Transfer"::request{} && Drupe::Action::"Write"::request{})
                };
            "#,
        );
        assert!(
            e.message.contains("field-injection") && e.message.contains("predicate"),
            "D2 error should explain the base must be a predicate, got: {e}"
        );
    }

    // ─── Window argument is a bare interval, not a `within` clause ──

    #[test]
    fn window_arg_is_a_bare_interval() {
        // A macro window parameter `?w` (used as `within ?w` in the body)
        // is supplied at the call site as a bare interval `1h` — NOT
        // `within 1h`. The `within` keyword belongs to the operator in the
        // body; the call passes only the interval. After expansion the
        // operator carries the concrete 1h window.
        let ps = must_expand(
            r#"
                def temporal recent(?w, ?s) {
                    formerly within ?w (?s)
                };
                permit (principal, action, resource)
                when temporal {
                    recent(1h, Drupe::Action::"Login"::request{})
                };
            "#,
        );
        let cond = temporal_cond(&ps);
        assert!(no_macro_residue_in_condition(cond), "no macro residue");
        match &cond.kind {
            ConditionKind::Formerly { within, .. } => {
                // The `?w` resolved to the concrete 1h interval the call site
                // supplied as a bare `1h`.
                assert_eq!(within.interval().seconds(), 3600, "?w resolved to 1h");
            }
            other => panic!("expected Formerly, got {other:?}"),
        }
    }

    #[test]
    fn within_keyword_as_call_argument_no_longer_parses() {
        // NEGATIVE CONTROL: the old `within 1h` call-argument form is gone.
        // Writing it at a call site must fail — a bare interval is the only
        // accepted window argument now. (`within 1h` is not a valid term or
        // condition either, so the whole parse fails.)
        let src = r#"
            def temporal recent(?w, ?s) {
                formerly within ?w (?s)
            };
            permit (principal, action, resource)
            when temporal {
                recent(within 1h, Drupe::Action::"Login"::request{})
            };
        "#;
        assert!(
            crate::parser::parse_policies(src).is_err(),
            "`within 1h` as a call argument must no longer parse"
        );
    }

    #[test]
    fn refined_field_value_can_be_a_macro_param() {
        // The injected value may itself be a `?p` — it resolves at the
        // same time the fold runs. `?s{ status: ?v }` with `?v` = a
        // string literal.
        let ps = must_expand(
            r#"
                def temporal approved_as(?s, ?v) {
                    ?s{ status: ?v }
                };
                permit (principal, action, resource)
                when temporal {
                    approved_as(Drupe::Action::"Transfer"::request{ amount: * }, "approved")
                };
            "#,
        );
        let cond = temporal_cond(&ps);
        assert!(no_macro_residue_in_condition(cond), "no macro residue");
        let p = pred_of(cond);
        let status = p
            .args
            .iter()
            .find(|a| a.name == "status")
            .expect("status injected");
        assert!(
            matches!(&status.value, Term::String(s) if s == "approved"),
            "injected `?v` resolved to \"approved\", got {:?}",
            status.value
        );
    }

    // ─── Positive: temporal aggregation macros ──────────────────────

    #[test]
    fn count_formerly_style_macro_expands() {
        let ps = must_expand(
            r#"
                def temporal count_formerly(?s) {
                    count for ($t: Timepoint). where (formerly within 1h (?s && tp($t)))
                };
                permit (principal, action, resource)
                when temporal {
                    exists (n: Long). ((count_formerly(Drupe::Action::"Login"::request{})) == n && n > 0)
                };
            "#,
        );
        let body = &ps.policies[0].conditions[0].body;
        let cond = match &body.kind {
            ExprKind::Extension(crate::extension::Extension::Temporal(t)) => &t.condition,
            other => panic!("expected temporal extension, got {other:?}"),
        };
        // The aggregate macro expands into a `Count` sitting as a
        // comparison operand inside the `exists`.
        let agg = find_agg_operand(cond).expect("an aggregate operand");
        match &agg.kind {
            AggExprKind::Count { for_vars, .. } => {
                assert_eq!(for_vars.len(), 1);
                // The gensym name should be "t$<call-span>" (not just "t").
                match &for_vars[0].slot {
                    BinderSlot::Name(n) => {
                        assert!(n.starts_with("t$"), "expected gensym name `t$N`, got `{n}`")
                    }
                    other => panic!("expected concrete Name slot, got {other:?}"),
                }
                // The macro's `$t: Timepoint` annotation is carried through.
                assert_eq!(
                    for_vars[0].ty,
                    crate::extension::temporal::ast::Type::Timepoint
                );
            }
            other => panic!("expected Count, got {other:?}"),
        }
        assert!(no_macro_residue_in_condition(cond), "no macro residue");
    }

    #[test]
    fn agg_macro_call_as_macro_argument_expands() {
        // An aggregation-producing macro call (`count_within(...)`) passed
        // as an argument to another macro (`bind`) whose parameter sits in
        // a comparison-operand position. The parser tags the argument as a
        // `CallArg::Condition` (a bare call parses as a condition atom), and
        // `expand_temporal_call_args` must re-tag it as a `Term::Agg` so it
        // fills the `?A == ?n` slot. This is the composition that lets the
        // stdlib `bind` + `count_within` macros nest.
        let ps = must_expand(
            r#"
                def temporal count_within(?w, ?s) {
                    count for ($t: Timepoint). where (formerly within ?w (?s && tp($t)))
                };
                def temporal bind(?n, ?A, ?B) {
                    exists (?n: Long). (?A == ?n && ?B)
                };
                permit (principal, action, resource)
                when temporal {
                    bind(c, count_within(1h, Drupe::Action::"Login"::request{ input.user: _ }), c > 2)
                };
            "#,
        );
        let body = &ps.policies[0].conditions[0].body;
        let cond = match &body.kind {
            ExprKind::Extension(crate::extension::Extension::Temporal(t)) => &t.condition,
            other => panic!("expected temporal extension, got {other:?}"),
        };
        // The nested `count_within` call expanded into a `Count` aggregate
        // sitting as the comparison operand inside `bind`'s `exists`.
        let agg = find_agg_operand(cond).expect("an aggregate operand");
        match &agg.kind {
            AggExprKind::Count { for_vars, .. } => {
                assert_eq!(for_vars.len(), 1);
                match &for_vars[0].slot {
                    BinderSlot::Name(n) => {
                        assert!(n.starts_with("t$"), "expected gensym name `t$N`, got `{n}`")
                    }
                    other => panic!("expected concrete Name slot, got {other:?}"),
                }
            }
            other => panic!("expected Count, got {other:?}"),
        }
        assert!(no_macro_residue_in_condition(cond), "no macro residue");
    }

    #[test]
    fn condition_macro_in_aggregation_value_slot_rejected() {
        // The dual of the above: a *condition*-producing macro passed into a
        // term/aggregation-value parameter slot stays a `CallArg::Condition`
        // and must be rejected as a shape mismatch, not silently accepted.
        let e = must_fail(
            r#"
                def temporal recent(?w, ?s) { formerly within ?w ?s };
                def temporal bind(?n, ?A, ?B) {
                    exists (?n: Long). (?A == ?n && ?B)
                };
                permit (principal, action, resource)
                when temporal {
                    bind(n, recent(1h, Drupe::Action::"Login"::request{ input.user: _ }), n > 0)
                };
            "#,
        );
        assert!(
            e.message.contains("?A") && e.message.contains("term position"),
            "expected a term-position shape-mismatch on `?A`, got: {e}"
        );
    }

    #[test]
    fn sum_formerly_style_macro_hygiene_no_capture() {
        // ?a in binder position, $t freshly introduced. Crucially, the
        // user passes `t` as the bound-var arg: it must NOT collide with
        // the macro's `$t` (which becomes `t$<span>`).
        let ps = must_expand(
            r#"
                def temporal sum_formerly(?a) {
                    sum ?a for (?a: Long), ($t: Timepoint). where (formerly within 1h (Drupe::Action::"Transfer"::request{ input.amount: ?a } && tp($t)))
                };
                permit (principal, action, resource)
                when temporal {
                    exists (r: Long). ((sum_formerly(t)) == r && r > 0)
                };
            "#,
        );
        let body = &ps.policies[0].conditions[0].body;
        let cond = match &body.kind {
            ExprKind::Extension(crate::extension::Extension::Temporal(t)) => &t.condition,
            other => panic!("expected temporal extension, got {other:?}"),
        };
        // The aggregate macro expands into a `Sum` operand inside `exists`.
        let agg = find_agg_operand(cond).expect("an aggregate operand");
        match &agg.kind {
            AggExprKind::Sum {
                bound_var,
                for_vars,
                ..
            } => {
                // bound_var is the user's `t`.
                assert_eq!(bound_var.name(), "t");
                assert_eq!(for_vars.len(), 2);
                // First slot is `?a` -> user's `t`.
                assert_eq!(for_vars[0].name(), "t");
                // Second slot is `$t` -> gensym `t$N`, NOT `t`.
                let gensym = for_vars[1].name();
                assert!(
                    gensym.starts_with("t$") && gensym != "t",
                    "expected gensym `t$N` distinct from user's `t`, got `{gensym}`"
                );
            }
            other => panic!("expected Sum, got {other:?}"),
        }
        assert!(no_macro_residue_in_condition(cond), "no macro residue");
    }

    #[test]
    fn let_style_macro_binds_result_name_in_binder_and_term_positions() {
        // `let_(?n, ?A, ?B)` = `exists (?n: Long). (?A == ?n && ?B)`. The
        // result param `?n` is used in BOTH the `exists` binder position and
        // a comparison term position; the aggregate `?A` is passed as an
        // ordinary term. Post-expansion the `exists` binder is the caller's
        // `n` and the `?A` aggregate has been spliced into the operand.
        let ps = must_expand(
            r#"
                def temporal let_(?n, ?A, ?B) {
                    exists (?n: Long). (?A == ?n && ?B)
                };
                permit (principal, action, resource)
                when temporal {
                    let_(n, count for (t: Timepoint). where (Drupe::Action::"Login"::request{} && tp(t)), n > 0)
                };
            "#,
        );
        let body = &ps.policies[0].conditions[0].body;
        let cond = match &body.kind {
            ExprKind::Extension(crate::extension::Extension::Temporal(t)) => &t.condition,
            other => panic!("expected temporal extension, got {other:?}"),
        };
        // Top level is the `exists` with binder `n: Long`.
        match &cond.kind {
            ConditionKind::Exists { var, .. } => {
                assert!(matches!(&var.slot, BinderSlot::Name(n) if n == "n"));
                assert_eq!(var.ty, tast::Type::Named(vec!["Long".to_string()]));
            }
            other => panic!("expected Exists, got {other:?}"),
        }
        // The `?A` aggregate was spliced in as a Count operand.
        let agg = find_agg_operand(cond).expect("an aggregate operand");
        assert!(matches!(agg.kind, AggExprKind::Count { .. }), "?A -> Count");
        assert!(no_macro_residue_in_condition(cond), "no macro residue");
    }

    /// Find the first aggregate comparison-operand anywhere in a condition
    /// (test helper for the aggregate-macro expansion tests).
    fn find_agg_operand(c: &Condition) -> Option<&AggExpr> {
        fn agg_of(t: &Term) -> Option<&AggExpr> {
            match t {
                Term::Agg(a) => Some(a.as_ref()),
                _ => None,
            }
        }
        match &c.kind {
            ConditionKind::Comparison { left, right, .. } => agg_of(left).or_else(|| agg_of(right)),
            ConditionKind::And { left, right } | ConditionKind::Since { left, right, .. } => {
                find_agg_operand(left).or_else(|| find_agg_operand(right))
            }
            ConditionKind::Not { inner }
            | ConditionKind::Formerly { body: inner, .. }
            | ConditionKind::Previous { body: inner, .. }
            | ConditionKind::Exists { body: inner, .. } => find_agg_operand(inner),
            _ => None,
        }
    }

    // ─── Negative: errors ───────────────────────────────────────────

    #[test]
    fn unknown_macro_call_in_cedar_is_rejected() {
        let e = must_fail(
            r#"
                permit (principal, action, resource)
                when { not_a_macro(principal) };
            "#,
        );
        assert!(e.message.contains("unknown function or macro"), "{e}");
        assert!(e.message.contains("not_a_macro"), "{e}");
    }

    #[test]
    fn arity_mismatch_is_rejected() {
        let e = must_fail(
            r#"
                def cedar foo(?a, ?b) { ?a == ?b };
                permit (principal, action, resource)
                when { foo(principal) };
            "#,
        );
        assert!(e.message.contains("expects 2 argument"), "{e}");
    }

    #[test]
    fn duplicate_macro_name_is_rejected() {
        let e = must_fail(
            r#"
                def cedar foo(?a) { ?a };
                def cedar foo(?b) { ?b };
            "#,
        );
        assert!(e.message.contains("duplicate macro definition"), "{e}");
    }

    #[test]
    fn cedar_macro_called_in_temporal_position_rejected() {
        let e = must_fail(
            r#"
                def cedar c(?p) { ?p == User::"alice" };
                permit (principal, action, resource)
                when temporal { c(principal) };
            "#,
        );
        // The cedar macro can't satisfy a temporal-condition slot.
        assert!(
            e.message.contains("cedar macro") && e.message.contains("temporal"),
            "expected kind-mismatch error mentioning cedar/temporal, got: {e}"
        );
    }

    #[test]
    fn temporal_condition_macro_in_agg_position_rejected() {
        let e = must_fail(
            r#"
                def temporal cond(?p) { Drupe::Action::"Login"::request{} };
                permit (principal, action, resource)
                when temporal {
                    exists (r: Long). ((cond(principal)) == r && r > 0)
                };
            "#,
        );
        assert!(
            e.message.contains("condition macro"),
            "expected condition-vs-agg error, got: {e}"
        );
    }

    #[test]
    fn macro_in_macro_rejected() {
        let e = must_fail(
            r#"
                def cedar inner(?x) { ?x };
                def cedar outer(?y) { inner(?y) };
                permit (principal, action, resource)
                when { outer(principal) };
            "#,
        );
        assert!(e.message.contains("macro-in-macro"), "{e}");
    }

    #[test]
    fn unknown_param_ref_in_body_rejected() {
        let e = must_fail(
            r#"
                def cedar foo(?a) { ?b };
            "#,
        );
        assert!(
            e.message.contains("does not name a declared parameter"),
            "{e}"
        );
    }

    #[test]
    fn temporal_block_in_cedar_macro_body_rejected() {
        // A cedar macro body cannot contain a `temporal { … }` block —
        // even a fully self-contained one — because cedar substitution
        // doesn't descend into the temporal sub-language AST. The
        // well-formedness pass rejects this with a clear message
        // pointing at the offending block.
        let e = must_fail(
            r#"
                def cedar recent_login() {
                    temporal { formerly within 1h Drupe::Action::"Login"::request{} }
                };
                permit (principal, action, resource)
                when { recent_login() };
            "#,
        );
        assert!(
            e.message.contains("`temporal { … }` block is not allowed"),
            "{e}"
        );
    }

    #[test]
    fn provider_invocation_in_cedar_macro_body_rejected() {
        // A provider invocation is an ordinary Cedar call (`Ns::Fn(args)…`),
        // so writing one inside a `def cedar` body is macro-in-macro, which is
        // not supported. (There is no `guardrails { … }` expression form to
        // reject: `guardrails` is a clause tag, transparent sugar for a bare
        // clause, and never appears in an expression position.)
        let e = must_fail(
            r#"
                def cedar flagged() {
                    Pii::Detect("x").severity > decimal("0.5")
                };
                permit (principal, action, resource)
                when { flagged() };
            "#,
        );
        assert!(e.message.contains("macro-in-macro is not supported"), "{e}");
    }

    #[test]
    fn binder_pos_arg_must_be_identifier() {
        // `sum ?a for (?a: Long), ($t: Timepoint).` — ?a is in binder
        // position; calling with a non-identifier should be rejected.
        let e = must_fail(
            r#"
                def temporal sum_lit(?a) {
                    sum ?a for (?a: Long), ($t: Timepoint). where tp($t)
                };
                permit (principal, action, resource)
                when temporal {
                    exists (r: Long). ((sum_lit(42)) == r && r > 0)
                };
            "#,
        );
        assert!(
            e.message.contains("binder position") && e.message.contains("single identifier"),
            "{e}"
        );
    }

    #[test]
    fn stray_param_ref_outside_body_rejected() {
        // Without any def_decl, a bare `?u` should be rejected (it's
        // not a Cedar template slot like `?principal`/`?resource`).
        let e = must_fail(
            r#"
                permit (principal, action, resource)
                when { ?u == principal };
            "#,
        );
        assert!(e.message.contains("stray macro parameter"), "{e}");
    }

    #[test]
    fn reserved_macro_name_rejected() {
        let e = must_fail(
            r#"
                def cedar count(?a) { ?a };
            "#,
        );
        assert!(e.message.contains("reserved"), "{e}");
    }

    #[test]
    fn stray_binder_ref_outside_body_rejected() {
        // The binder counterpart of `stray_param_ref_outside_body_rejected`:
        // a `$t` fresh-binder sigil used in a `for`-binder position at the
        // top level (no enclosing macro def) is rejected by the expansion
        // pass, and the message uses the new `$` spelling — not `!`.
        let e = must_fail(
            r#"
                permit (principal, action, resource)
                when temporal {
                    exists (n: Long). ((count for ($t: Timepoint). where (Drupe::Action::"Login"::request{} && tp($t))) == n && n > 0)
                };
            "#,
        );
        assert!(
            e.message.contains("stray macro binder reference `$t`"),
            "expected `$`-spelled stray-binder message, got: {e}"
        );
    }

    // ─── Helpers ────────────────────────────────────────────────────

    /// Walk a Condition and return false if any unresolved macro AST
    /// node is found.
    fn no_macro_residue_in_condition(c: &Condition) -> bool {
        match &c.kind {
            ConditionKind::And { left, right } => {
                no_macro_residue_in_condition(left) && no_macro_residue_in_condition(right)
            }
            ConditionKind::Or { left, right } => {
                no_macro_residue_in_condition(left) && no_macro_residue_in_condition(right)
            }
            ConditionKind::Not { inner } => no_macro_residue_in_condition(inner),
            ConditionKind::Formerly { body, .. } | ConditionKind::Previous { body, .. } => {
                no_macro_residue_in_condition(body)
            }
            ConditionKind::Since { left, right, .. } => {
                no_macro_residue_in_condition(left) && no_macro_residue_in_condition(right)
            }
            ConditionKind::Predicate(p) => {
                p.args.iter().all(|a| no_macro_residue_in_term(&a.value))
            }
            ConditionKind::Comparison { left, right, .. } => {
                no_macro_residue_in_term(left) && no_macro_residue_in_term(right)
            }
            ConditionKind::Tp { var } => matches!(var, BinderSlot::Name(_)),
            ConditionKind::Exists { var, body } => {
                matches!(var.slot, BinderSlot::Name(_)) && no_macro_residue_in_condition(body)
            }
            // A surviving `Refine` means the field-injection fold did not
            // run — that is macro residue, like an unresolved Call/SigilRef.
            ConditionKind::Call(_)
            | ConditionKind::SigilRef { .. }
            | ConditionKind::Refine { .. } => false,
        }
    }

    fn no_macro_residue_in_agg(a: &AggExpr) -> bool {
        match &a.kind {
            AggExprKind::Sum {
                bound_var,
                for_vars,
                body,
            } => {
                matches!(bound_var, BinderSlot::Name(_))
                    && for_vars
                        .iter()
                        .all(|v| matches!(v.slot, BinderSlot::Name(_)))
                    && no_macro_residue_in_condition(body)
            }
            AggExprKind::Count { for_vars, body } => {
                for_vars
                    .iter()
                    .all(|v| matches!(v.slot, BinderSlot::Name(_)))
                    && no_macro_residue_in_condition(body)
            }
            AggExprKind::Call(_) => false,
        }
    }

    fn no_macro_residue_in_term(t: &Term) -> bool {
        match t {
            Term::ParamRef(_) | Term::BinderRef(_) => false,
            Term::Array(items) => items.iter().all(no_macro_residue_in_term),
            Term::Agg(a) => no_macro_residue_in_agg(a),
            _ => true,
        }
    }

    // ─── Post-expansion closedness (the re-check's second half) ─────────

    #[test]
    fn macro_expansion_leaving_a_free_variable_is_rejected() {
        // A macro body carrying a plain (non-sigil, non-binder) variable:
        // hygiene renames only the macro's OWN binders, so `leak` survives
        // expansion verbatim and leaves the leaf unclosed. The parse-time
        // closedness check cannot see it (the leaf is an opaque `Call`), so
        // the POST-EXPANSION re-run must reject it with the wrapped message.
        // (mcagg_0524 pins the range-restriction half of the re-run; this
        // pins the closedness half.)
        let e = must_fail(
            r#"
                def temporal leaky(?w) {
                    formerly within ?w Drupe::Action::"Login"::request{ input.user: leak }
                };
                permit (principal, action, resource)
                when temporal {
                    leaky(1h)
                };
            "#,
        );
        let msg = e.to_string();
        assert!(
            msg.contains("temporal binding check failed after expansion"),
            "must be the post-expansion re-run: {msg}"
        );
        assert!(
            msg.contains("variable `leak` is free in this temporal condition"),
            "must be the closedness rejection: {msg}"
        );
    }
}
