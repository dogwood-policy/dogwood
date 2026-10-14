//! Render a parsed, macro-expanded [`Policy`] back to `.dw` source text.
//!
//! This is the inverse of parsing, run on the **post-macro-expansion** surface
//! AST: it produces valid `.dw` text in which every macro is already inlined
//! (macro *definitions* are top-level and never part of a [`Policy`], so a
//! per-policy rendering carries none) and no macro reference remains. The
//! contract is semantic, not textual — re-parsing and lowering the output
//! yields the same policy — so this deliberately does **not** preserve
//! formatting, comments, or the original operator spelling beyond what the
//! surface AST records.
//!
//! Two rules keep the output correct and stable:
//!
//! - **Full parenthesization.** Every compound operand is wrapped in `( … )`
//!   rather than tracking Cedar's precedence/associativity, so a precedence bug
//!   is structurally impossible. Parens are erased by re-parsing, so this does
//!   not change the lowered AST, and re-rendering re-adds them identically
//!   (idempotence).
//! - **Fail loud on the impossible.** Nodes that cannot survive macro expansion
//!   (`ParamRef`, temporal `SigilRef`/`Refine`/`Call`, a `?w`/`?p`/`$t` slot,
//!   the lowering-only temporal `Or`) `panic!` with a clear message rather than
//!   emit partial or invalid text.
//! - Temporal gensym binders are renamed injectively; see [`BinderRenames`].
//!
//! Value leaves (literals, vars, slots, entity types, `like` patterns) delegate
//! to the `cedar_policy_core` `Display` impls, which use Cedar's own escaping —
//! the same grammar Dogwood's parser accepts.

use std::collections::{BTreeMap, BTreeSet};

use cedar_policy_core::ast as cedar_ast;

use crate::ast::{BinOp, Cond, CondKeyword, Effect, Expr, ExprKind, Policy, Scope, UnOp};
use crate::extension::Extension;
use crate::extension::temporal::ast as tast;
use crate::policy_view::{ActionConstraint, PolicyScope, PrincipalConstraint, ResourceConstraint};

/// Render one policy back to `.dw` text: annotations, effect + scope, then each
/// `when`/`unless` clause, terminated by `;`.
pub(crate) fn render_policy(policy: &Policy) -> String {
    let mut out = String::new();

    for ann in &policy.annotations {
        match &ann.value {
            // The parser decodes an annotation value with Cedar's unescaper, so
            // the stored value is already decoded and must be re-encoded — the
            // same `quote` path a Cedar-decoded string uses.
            Some(v) => out.push_str(&format!("@{}({})\n", ann.key, quote(v))),
            None => out.push_str(&format!("@{}\n", ann.key)),
        }
    }

    let effect = match policy.effect {
        Effect::Permit => "permit",
        Effect::Forbid => "forbid",
    };
    out.push_str(&format!("{effect} ({})", render_scope(&policy.scope)));

    for cond in &policy.conditions {
        out.push_str(&format!("\n{}", render_cond_clause(cond)));
    }
    out.push(';');
    out
}

// ─── scope ────────────────────────────────────────────────────────────────

fn render_scope(scope: &Scope) -> String {
    let view = PolicyScope::from_scope(scope);
    format!(
        "{}, {}, {}",
        render_principal(view.principal()),
        render_action(view.action()),
        render_resource(view.resource()),
    )
}

fn render_principal(c: &PrincipalConstraint) -> String {
    match c {
        PrincipalConstraint::Any => "principal".to_string(),
        PrincipalConstraint::In(o) => format!("principal in {}", slot_or_uid(o, "?principal")),
        PrincipalConstraint::Eq(o) => format!("principal == {}", slot_or_uid(o, "?principal")),
        PrincipalConstraint::Is(t) => format!("principal is {t}"),
        PrincipalConstraint::IsIn(t, o) => {
            format!("principal is {t} in {}", slot_or_uid(o, "?principal"))
        }
    }
}

fn render_resource(c: &ResourceConstraint) -> String {
    match c {
        ResourceConstraint::Any => "resource".to_string(),
        ResourceConstraint::In(o) => format!("resource in {}", slot_or_uid(o, "?resource")),
        ResourceConstraint::Eq(o) => format!("resource == {}", slot_or_uid(o, "?resource")),
        ResourceConstraint::Is(t) => format!("resource is {t}"),
        ResourceConstraint::IsIn(t, o) => {
            format!("resource is {t} in {}", slot_or_uid(o, "?resource"))
        }
    }
}

fn render_action(c: &ActionConstraint) -> String {
    match c {
        ActionConstraint::Any => "action".to_string(),
        ActionConstraint::Eq(uid) => format!("action == {uid}"),
        ActionConstraint::In(uids) => {
            let items: Vec<String> = uids.iter().map(|u| u.to_string()).collect();
            format!("action in [{}]", items.join(", "))
        }
    }
}

/// A literal entity uid, or the template slot's spelling when the reference is a
/// slot (`None`).
fn slot_or_uid(o: &Option<cedar_policy::EntityUid>, slot: &str) -> String {
    match o {
        Some(uid) => uid.to_string(),
        None => slot.to_string(),
    }
}

// ─── clauses ────────────────────────────────────────────────────────────────

/// `when { … }` / `unless { … }`. A bare `temporal { … }` clause body renders
/// as `when { temporal { … } }` — the marker is a primary, so this re-parses to
/// the same tagged clause.
fn render_cond_clause(cond: &Cond) -> String {
    let kw = match cond.keyword {
        CondKeyword::When => "when",
        CondKeyword::Unless => "unless",
    };
    format!("{kw} {{ {} }}", render_expr(&cond.body))
}

// ─── Cedar expressions ────────────────────────────────────────────────────

fn render_expr(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Lit(lit) => lit.to_string(),
        ExprKind::Var(var) => var.to_string(),
        ExprKind::Slot(slot) => slot.to_string(),
        ExprKind::Extension(ext) => render_extension(ext),

        ExprKind::UnaryApp { op, expr } => render_unary(*op, expr),
        ExprKind::BinaryApp { op, left, right } => render_binary(*op, left, right),

        ExprKind::GetAttr { expr, attr } => {
            // Dot access requires an identifier (`.foo`); a non-identifier
            // attribute must use index syntax (`["a b"]`), which the parser
            // accepts as the same `GetAttr`.
            if is_ident(attr) {
                format!("{}.{attr}", atom(expr))
            } else {
                format!("{}[{}]", atom(expr), quote(attr))
            }
        }
        ExprKind::HasAttr { expr, attrs } => {
            // The first path segment sits in expression (`add`) position, where a
            // bare name must be a non-reserved identifier — a reserved word like
            // `true`/`false` would parse as a literal, not an attribute. A quoted
            // string is always accepted there and is decoded, so quote the first
            // segment unconditionally. Later segments are `.`-access, which
            // accepts any identifier (keywords included), so they render bare.
            let mut path = quote(&attrs[0]);
            for seg in &attrs[1..] {
                path.push('.');
                path.push_str(seg);
            }
            format!("{} has {path}", atom(expr))
        }
        ExprKind::Like { expr, pattern } => {
            let pat = cedar_ast::Pattern::from(pattern.clone()).to_string();
            format!("{} like \"{pat}\"", atom(expr))
        }
        ExprKind::Is {
            expr,
            entity_type,
            in_expr,
        } => {
            let base = format!("{} is {entity_type}", atom(expr));
            match in_expr {
                Some(in_e) => format!("{base} in {}", atom(in_e)),
                None => base,
            }
        }
        ExprKind::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => format!(
            "if {} then {} else {}",
            render_expr(cond),
            render_expr(then_expr),
            render_expr(else_expr),
        ),
        ExprKind::Set(elems) => {
            let items: Vec<String> = elems.iter().map(render_expr).collect();
            format!("[{}]", items.join(", "))
        }
        ExprKind::Record(entries) => render_record(entries),
        ExprKind::Call { name, args } => {
            let args: Vec<String> = args.iter().map(render_expr).collect();
            format!("{name}({})", args.join(", "))
        }
        ExprKind::MethodCall {
            receiver,
            method,
            args,
        } => {
            let args: Vec<String> = args.iter().map(render_expr).collect();
            format!("{}.{method}({})", atom(receiver), args.join(", "))
        }

        // Cannot survive macro expansion — see the module docs.
        ExprKind::ParamRef { name } => {
            panic!("render: unexpanded macro parameter `?{name}` in expression position")
        }
    }
}

/// Render `e` in a position that demands a *primary* (an operand, a receiver),
/// wrapping it in parens iff its natural form is not already primary-safe.
fn atom(e: &Expr) -> String {
    let s = render_expr(e);
    if needs_parens(e) { format!("({s})") } else { s }
}

/// Whether `e`'s natural rendering needs wrapping to be used as a primary. An
/// infix `BinaryApp` self-parenthesizes (so it is already primary-safe); prefix
/// negation, `is`, `like`, `has`, and `if/then/else` do not.
fn needs_parens(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::UnaryApp { op, .. } => matches!(op, UnOp::Not | UnOp::Neg),
        ExprKind::Is { .. }
        | ExprKind::Like { .. }
        | ExprKind::HasAttr { .. }
        | ExprKind::IfThenElse { .. } => true,
        _ => false,
    }
}

fn render_unary(op: UnOp, expr: &Expr) -> String {
    match op {
        // Prefix operators.
        UnOp::Not => format!("!{}", atom(expr)),
        UnOp::Neg => format!("-{}", atom(expr)),
        // Extension constructors: `name(arg)`.
        UnOp::Decimal => format!("decimal({})", render_expr(expr)),
        UnOp::Datetime => format!("datetime({})", render_expr(expr)),
        UnOp::Duration => format!("duration({})", render_expr(expr)),
        UnOp::Ip => format!("ip({})", render_expr(expr)),
        // Zero-argument extension methods: `recv.name()`.
        _ => format!("{}.{}()", atom(expr), zero_arg_method(op)),
    }
}

/// The surface method name for a zero-argument extension-method [`UnOp`].
fn zero_arg_method(op: UnOp) -> &'static str {
    match op {
        UnOp::IsEmpty => "isEmpty",
        UnOp::IsIpv4 => "isIpv4",
        UnOp::IsIpv6 => "isIpv6",
        UnOp::IsLoopback => "isLoopback",
        UnOp::IsMulticast => "isMulticast",
        UnOp::ToDate => "toDate",
        UnOp::ToTime => "toTime",
        UnOp::ToMilliseconds => "toMilliseconds",
        UnOp::ToSeconds => "toSeconds",
        UnOp::ToMinutes => "toMinutes",
        UnOp::ToHours => "toHours",
        UnOp::ToDays => "toDays",
        UnOp::Not | UnOp::Neg | UnOp::Decimal | UnOp::Datetime | UnOp::Duration | UnOp::Ip => {
            unreachable!("not a zero-argument extension method: {op:?}")
        }
    }
}

fn render_binary(op: BinOp, left: &Expr, right: &Expr) -> String {
    if let Some(sym) = infix_symbol(op) {
        // Fully parenthesized: `(L op R)`.
        format!("({} {sym} {})", atom(left), atom(right))
    } else {
        // One-argument method form: `L.method(R)`.
        format!("{}.{}({})", atom(left), method_name(op), render_expr(right))
    }
}

/// The infix operator symbol for the core relational/boolean/arithmetic
/// [`BinOp`]s, or `None` for the ones written in method form.
fn infix_symbol(op: BinOp) -> Option<&'static str> {
    Some(match op {
        BinOp::Eq => "==",
        BinOp::NotEq => "!=",
        BinOp::Less => "<",
        BinOp::LessEq => "<=",
        BinOp::Greater => ">",
        BinOp::GreaterEq => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::In => "in",
        _ => return None,
    })
}

/// The surface method name for a one-argument method-form [`BinOp`].
fn method_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Contains => "contains",
        BinOp::ContainsAll => "containsAll",
        BinOp::ContainsAny => "containsAny",
        BinOp::GetTag => "getTag",
        BinOp::HasTag => "hasTag",
        BinOp::IsInRange => "isInRange",
        BinOp::Offset => "offset",
        BinOp::DurationSince => "durationSince",
        BinOp::DecimalLessThan => "lessThan",
        BinOp::DecimalLessEq => "lessThanOrEqual",
        BinOp::DecimalGreater => "greaterThan",
        BinOp::DecimalGreaterEq => "greaterThanOrEqual",
        _ => unreachable!("not a method-form binary operator: {op:?}"),
    }
}

fn render_record(entries: &BTreeMap<String, Expr>) -> String {
    if entries.is_empty() {
        return "{}".to_string();
    }
    let fields: Vec<String> = entries
        .iter()
        .map(|(k, v)| format!("{}: {}", member(k), render_expr(v)))
        .collect();
    format!("{{ {} }}", fields.join(", "))
}

/// A record key or attribute name: bare when it is a valid identifier, else a
/// quoted string (both accepted by the parser as a member name).
fn member(name: &str) -> String {
    if is_ident(name) {
        name.to_string()
    } else {
        quote(name)
    }
}

// ─── temporal ───────────────────────────────────────────────────────────────

fn render_extension(ext: &Extension) -> String {
    match ext {
        Extension::Temporal(t) => {
            let ren = binder_renames(&t.condition);
            format!("temporal {{ {} }}", render_condition(&t.condition, &ren))
        }
    }
}

fn render_condition(c: &tast::Condition, ren: &BinderRenames) -> String {
    use tast::ConditionKind as K;
    match &c.kind {
        K::And { left, right } => {
            format!("{} && {}", cond_group(left, ren), cond_group(right, ren))
        }
        K::Not { inner } => format!("!{}", cond_group(inner, ren)),
        K::Formerly { within, body } => {
            format!(
                "formerly within {} {}",
                render_within(within),
                cond_group(body, ren)
            )
        }
        K::Previous { within, body } => {
            format!(
                "previous within {} {}",
                render_within(within),
                cond_group(body, ren)
            )
        }
        K::Since {
            left,
            within,
            right,
        } => format!(
            "{} since within {} {}",
            cond_group(left, ren),
            render_within(within),
            cond_group(right, ren),
        ),
        K::Predicate(p) => render_predicate(p, ren),
        K::Comparison { op, left, right } => {
            format!(
                "{} {} {}",
                render_term(left, ren),
                cmp_symbol(*op),
                render_term(right, ren)
            )
        }
        K::Exists { var, body } => {
            format!(
                "exists ({}: {}). {}",
                binder_name(&var.slot, ren),
                var.ty.render(),
                cond_group(body, ren),
            )
        }
        K::Tp { var } => format!("tp({})", binder_name(var, ren)),

        // Lowering-only or pre-expansion nodes — never in a parsed, expanded tree.
        K::Or { .. } => panic!("render: temporal `Or` is lowering-only and cannot be rendered"),
        K::Call(_) => panic!("render: unexpanded temporal macro call cannot be rendered"),
        K::SigilRef { name, .. } => {
            panic!("render: unexpanded temporal sigil reference `{name}` cannot be rendered")
        }
        K::Refine { .. } => {
            panic!("render: temporal `Refine` is pre-expansion and cannot be rendered")
        }
    }
}

/// A temporal sub-condition in operand position, always parenthesized so no
/// operator-precedence ambiguity can arise. Parens re-parse away, so this is a
/// stable fixed point.
fn cond_group(c: &tast::Condition, ren: &BinderRenames) -> String {
    format!("({})", render_condition(c, ren))
}

fn render_within(w: &tast::WithinSpec) -> String {
    match w {
        tast::WithinSpec::Concrete(i) => i.render(),
        tast::WithinSpec::ParamRef(p) => {
            panic!("render: unexpanded window parameter `?{p}` cannot be rendered")
        }
    }
}

fn render_predicate(p: &tast::Predicate, ren: &BinderRenames) -> String {
    let head = format!(
        "{}::{}::{}",
        p.namespace.join("::"),
        quote(&p.action),
        p.kind
    );
    if p.args.is_empty() {
        return format!("{head}{{}}");
    }
    let args: Vec<String> = p
        .args
        .iter()
        .map(|a| format!("{}: {}", a.name, render_term(&a.value, ren)))
        .collect();
    format!("{head}{{ {} }}", args.join(", "))
}

fn render_term(t: &tast::Term, ren: &BinderRenames) -> String {
    use tast::Term as T;
    match t {
        T::Entity { ty, id } => format!("{ty}::{}", quote(id)),
        T::Integer(n) => n.to_string(),
        T::Decimal(s) => format!("decimal({})", quote(s)),
        T::String(s) => quote(s),
        T::Bool(b) => b.to_string(),
        T::ContextField(path) => format!("context.{}", path.join(".")),
        T::ScopeField(path) => path.join("."),
        T::Var(v) => ren.apply(v),
        T::Wildcard => "*".to_string(),
        T::Array(items) => {
            let items: Vec<String> = items.iter().map(|i| render_term(i, ren)).collect();
            format!("[{}]", items.join(", "))
        }
        T::Agg(agg) => render_agg(agg, ren),
        T::Arith { op, left, right } => format!(
            "{} {} {}",
            render_arith_operand(left, ren),
            op.token(),
            render_arith_operand(right, ren)
        ),
        T::ParamRef(p) => panic!("render: unexpanded macro parameter `?{p}` in term position"),
        T::BinderRef(b) => panic!("render: unexpanded macro binder `${b}` in term position"),
    }
}

/// Render one operand of an arithmetic expression. A nested `Arith` is
/// parenthesized so precedence survives the round trip; an aggregate so
/// its greedy `where` body cannot swallow a following operator.
fn render_arith_operand(t: &tast::Term, ren: &BinderRenames) -> String {
    match t {
        tast::Term::Arith { .. } | tast::Term::Agg(_) => format!("({})", render_term(t, ren)),
        _ => render_term(t, ren),
    }
}

fn render_agg(agg: &tast::AggExpr, ren: &BinderRenames) -> String {
    use tast::AggExprKind as A;
    match &agg.kind {
        A::Sum {
            bound_var,
            for_vars,
            body,
        } => format!(
            "sum {} for {}. where {}",
            binder_name(bound_var, ren),
            render_for_vars(for_vars, ren),
            cond_group(body, ren),
        ),
        A::Count { for_vars, body } => {
            format!(
                "count for {}. where {}",
                render_for_vars(for_vars, ren),
                cond_group(body, ren)
            )
        }
        A::Call(_) => panic!("render: unexpanded aggregation macro call cannot be rendered"),
    }
}

fn render_for_vars(for_vars: &[tast::TypedBinder], ren: &BinderRenames) -> String {
    for_vars
        .iter()
        .map(|b| format!("({}: {})", binder_name(&b.slot, ren), b.ty.render()))
        .collect::<Vec<_>>()
        .join(", ")
}

fn binder_name(slot: &tast::BinderSlot, ren: &BinderRenames) -> String {
    match slot {
        tast::BinderSlot::Name(s) => ren.apply(s),
        tast::BinderSlot::ParamRef(p) => {
            panic!("render: unexpanded macro parameter `?{p}` in binder position")
        }
        tast::BinderSlot::BinderRef(b) => {
            panic!("render: unexpanded macro binder `${b}` in binder position")
        }
    }
}

fn cmp_symbol(op: tast::CmpOp) -> &'static str {
    match op {
        tast::CmpOp::Le => "<=",
        tast::CmpOp::Lt => "<",
        tast::CmpOp::Ge => ">=",
        tast::CmpOp::Gt => ">",
        tast::CmpOp::Eq => "==",
        tast::CmpOp::NotEq => "!=",
    }
}

// ─── leaves ───────────────────────────────────────────────────────────────

/// A `"…"` string literal for a position whose parser **decodes** escapes with
/// Cedar's rules — every string-valued position: record and index-access keys
/// (`e["a b"]`), annotation values, and temporal terms (string / entity id /
/// decimal / action name). All of these funnel through Cedar's unescaper on
/// parse, so the stored value is the decoded string and rendering must re-encode
/// it. Escapes only what that decoder needs (`"`, `\`, control characters) and
/// lets every other character — notably `'` — through, so re-parsing yields
/// exactly the input. Deliberately **not** `Literal`'s own `Display`, which uses
/// `str::escape_debug` and over-escapes `'` as `\'`.
pub(crate) fn quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if c.is_control() => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// ─── temporal binder renaming ─────────────────────────────────────────────

/// Surface names for a temporal condition's gensym binders (`t$372`).
///
/// Spelling `$` as `_` is not injective: a user binder named `t_372` in the
/// same condition would collapse onto the gensym. So every non-gensym name is
/// reserved, and each gensym takes the first free name among `t_372`,
/// `t_372_1`, `t_372_2`, ….
#[derive(Debug, Clone, Default)]
pub(crate) struct BinderRenames {
    /// Gensym name → surface name; every other name maps to itself.
    map: BTreeMap<String, String>,
}

impl BinderRenames {
    /// The surface spelling of `name`.
    pub(crate) fn apply(&self, name: &str) -> String {
        match self.map.get(name) {
            Some(renamed) => renamed.clone(),
            None => name.to_string(),
        }
    }
}

/// Compute the [`BinderRenames`] for one temporal condition.
pub(crate) fn binder_renames(c: &tast::Condition) -> BinderRenames {
    let mut names = BTreeSet::new();
    collect_condition_names(c, &mut names);

    let (gensyms, mut taken): (Vec<&String>, BTreeSet<String>) = {
        let mut gensyms = Vec::new();
        let mut reserved = BTreeSet::new();
        for n in &names {
            if n.contains('$') {
                gensyms.push(n);
            } else {
                reserved.insert(n.clone());
            }
        }
        (gensyms, reserved)
    };

    let mut map = BTreeMap::new();
    // `names` is a BTreeSet, so `gensyms` is in sorted order: deterministic.
    for g in gensyms {
        let natural = g.replace('$', "_");
        let mut candidate = natural.clone();
        let mut nth = 1u32;
        while taken.contains(&candidate) {
            candidate = format!("{natural}_{nth}");
            nth += 1;
        }
        taken.insert(candidate.clone());
        map.insert(g.clone(), candidate);
    }
    BinderRenames { map }
}

/// Collect every binder name a condition declares or uses.
fn collect_condition_names(c: &tast::Condition, out: &mut BTreeSet<String>) {
    use tast::ConditionKind as K;
    match &c.kind {
        K::And { left, right } | K::Or { left, right } => {
            collect_condition_names(left, out);
            collect_condition_names(right, out);
        }
        K::Not { inner } => collect_condition_names(inner, out),
        K::Formerly { body, .. } | K::Previous { body, .. } => collect_condition_names(body, out),
        K::Since { left, right, .. } => {
            collect_condition_names(left, out);
            collect_condition_names(right, out);
        }
        K::Predicate(p) => {
            for a in &p.args {
                collect_term_names(&a.value, out);
            }
        }
        K::Comparison { left, right, .. } => {
            collect_term_names(left, out);
            collect_term_names(right, out);
        }
        K::Exists { var, body } => {
            collect_slot_name(&var.slot, out);
            collect_condition_names(body, out);
        }
        K::Tp { var } => collect_slot_name(var, out),
        K::Refine { base, fields, .. } => {
            collect_condition_names(base, out);
            for f in fields {
                collect_term_names(&f.value, out);
            }
        }
        // No surface syntax; rendering rejects these before any name matters.
        K::Call(_) | K::SigilRef { .. } => {}
    }
}

/// Collect the binder names a term mentions.
fn collect_term_names(t: &tast::Term, out: &mut BTreeSet<String>) {
    use tast::Term as T;
    match t {
        T::Var(v) => {
            out.insert(v.clone());
        }
        T::Array(items) => {
            for i in items {
                collect_term_names(i, out);
            }
        }
        T::Agg(agg) => collect_agg_names(agg, out),
        T::Arith { left, right, .. } => {
            collect_term_names(left, out);
            collect_term_names(right, out);
        }
        T::Entity { .. }
        | T::Integer(_)
        | T::Decimal(_)
        | T::String(_)
        | T::Bool(_)
        | T::ContextField(_)
        | T::ScopeField(_)
        | T::Wildcard
        | T::ParamRef(_)
        | T::BinderRef(_) => {}
    }
}

/// Collect the binder names an aggregation declares and mentions.
fn collect_agg_names(agg: &tast::AggExpr, out: &mut BTreeSet<String>) {
    use tast::AggExprKind as A;
    match &agg.kind {
        A::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            collect_slot_name(bound_var, out);
            for b in for_vars {
                collect_slot_name(&b.slot, out);
            }
            collect_condition_names(body, out);
        }
        A::Count { for_vars, body } => {
            for b in for_vars {
                collect_slot_name(&b.slot, out);
            }
            collect_condition_names(body, out);
        }
        A::Call(_) => {}
    }
}

/// Collect a binder slot's name; a still-sigil slot has none.
fn collect_slot_name(slot: &tast::BinderSlot, out: &mut BTreeSet<String>) {
    if let tast::BinderSlot::Name(s) = slot {
        out.insert(s.clone());
    }
}

/// Whether `name` is a bare identifier (so it needs no quoting as a member).
fn is_ident(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(c) if c == '_' || c.is_ascii_alphabetic() => {}
        _ => return false,
    }
    chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}
