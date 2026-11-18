//! The canonical text of a lowered temporal leaf, and its parser.
//!
//! A caller that lowers a policy set in one place and evaluates its temporal
//! leaves in another sends each leaf's condition as text. [`condition_text`]
//! prints a leaf as lowering produces it (after macro expansion, before pin
//! injection), and [`parse_leaf_condition`] reads it back:
//!
//! * `parse_leaf_condition(&condition_text(c)?)` is `c`, up to the spans, for
//!   every condition `condition_text` prints. `condition_text` checks this
//!   itself, by parsing what it printed, and returns an error instead of a
//!   text that would read back as another leaf;
//! * `condition_text(&parse_leaf_condition(t)?)` is `t` for every text
//!   `condition_text` printed: the text is canonical.
//!
//! The text is the policy grammar's (`grammar.pest`), with one addition. Macro
//! expansion names the binders it introduces `<name>$<n>` (a `$` no author can
//! write, so that they never capture an author's binder), and the text spells
//! such a binder `$<name>$<n>`, the binder-reference sigil followed by the
//! generated name. Only this parser reads that spelling as a binder name; a
//! policy or a macro body that writes it is rejected.

use super::ast::{
    AggExpr, AggExprKind, BinderSlot, Condition, ConditionKind, Term, TypedBinder, WithinSpec,
};
use crate::error::Span;

/// Why a condition has no canonical text, or a text is not one of a lowered
/// leaf.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{message}")]
pub struct TextError {
    message: String,
}

impl TextError {
    pub(crate) fn new(message: impl Into<String>) -> Self {
        TextError {
            message: message.into(),
        }
    }

    /// The reason, as text.
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// Whether `name` is a binder name macro expansion generated (`t$372`).
pub(crate) fn is_generated(name: &str) -> bool {
    name.contains('$')
}

// ─── A walk over a condition ─────────────────────────────────────────────

/// What a walk does at each node it visits. Every hook defaults to nothing.
trait Visit {
    fn span(&mut self, _s: &mut Span) {}
    fn slot(&mut self, _s: &mut BinderSlot) {}
    fn term(&mut self, _t: &mut Term) {}
    fn condition(&mut self, _c: &mut ConditionKind) {}
    fn within(&mut self, _w: &mut WithinSpec) {}
    fn agg(&mut self, _a: &mut AggExprKind) {}
}

fn walk_condition(c: &mut Condition, v: &mut impl Visit) {
    v.span(&mut c.span);
    v.condition(&mut c.kind);
    match &mut c.kind {
        ConditionKind::And { left, right } | ConditionKind::Or { left, right } => {
            walk_condition(left, v);
            walk_condition(right, v);
        }
        ConditionKind::Not { inner } => walk_condition(inner, v),
        ConditionKind::Formerly { within, body } | ConditionKind::Previous { within, body } => {
            v.within(within);
            walk_condition(body, v);
        }
        ConditionKind::Since {
            left,
            within,
            right,
        } => {
            walk_condition(left, v);
            v.within(within);
            walk_condition(right, v);
        }
        ConditionKind::Predicate(p) => {
            v.span(&mut p.span);
            for a in &mut p.args {
                walk_term(&mut a.value, v);
            }
        }
        ConditionKind::Comparison { left, right, .. } => {
            walk_term(left, v);
            walk_term(right, v);
        }
        ConditionKind::Exists { var, body } => {
            walk_binder(var, v);
            walk_condition(body, v);
        }
        ConditionKind::Tp { var } => v.slot(var),
        ConditionKind::Call(call) => v.span(&mut call.span),
        ConditionKind::SigilRef { .. } => {}
        ConditionKind::Refine { base, fields, span } => {
            v.span(span);
            walk_condition(base, v);
            for a in fields {
                walk_term(&mut a.value, v);
            }
        }
    }
}

fn walk_binder(b: &mut TypedBinder, v: &mut impl Visit) {
    v.slot(&mut b.slot);
}

fn walk_term(t: &mut Term, v: &mut impl Visit) {
    v.term(t);
    match t {
        Term::Array(items) => {
            for item in items {
                walk_term(item, v);
            }
        }
        Term::Agg(agg) => walk_agg(agg, v),
        Term::Arith { left, right, .. } => {
            walk_term(left, v);
            walk_term(right, v);
        }
        _ => {}
    }
}

fn walk_agg(a: &mut AggExpr, v: &mut impl Visit) {
    v.span(&mut a.span);
    v.agg(&mut a.kind);
    match &mut a.kind {
        AggExprKind::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            v.slot(bound_var);
            for b in for_vars {
                walk_binder(b, v);
            }
            walk_condition(body, v);
        }
        AggExprKind::Count { for_vars, body } => {
            for b in for_vars {
                walk_binder(b, v);
            }
            walk_condition(body, v);
        }
        AggExprKind::Call(call) => v.span(&mut call.span),
    }
}

// ─── The walks ───────────────────────────────────────────────────────────

/// `c` with every span the empty span at 0: what two conditions that differ
/// only in where they were parsed from have in common.
pub(crate) fn without_spans(c: &Condition) -> Condition {
    struct Erase;
    impl Visit for Erase {
        fn span(&mut self, s: &mut Span) {
            *s = crate::error::dummy_span();
        }
    }
    let mut out = c.clone();
    walk_condition(&mut out, &mut Erase);
    out
}

/// A walk that finds the first binder reference to a generated name.
#[derive(Default)]
struct FindGenerated(Option<String>);

/// The first binder reference in `c` that names a binder macro expansion
/// generates (`$t$372`), if any.
pub(crate) fn first_generated_ref(c: &Condition) -> Option<String> {
    let mut find = FindGenerated::default();
    walk_condition(&mut c.clone(), &mut find);
    find.0
}

/// [`first_generated_ref`] of a term (a macro's value body).
pub(crate) fn first_generated_ref_term(t: &Term) -> Option<String> {
    let mut find = FindGenerated::default();
    walk_term(&mut t.clone(), &mut find);
    find.0
}

impl Visit for FindGenerated {
    fn slot(&mut self, s: &mut BinderSlot) {
        if let BinderSlot::BinderRef(n) = s
            && is_generated(n)
        {
            self.0.get_or_insert_with(|| n.clone());
        }
    }
    fn term(&mut self, t: &mut Term) {
        if let Term::BinderRef(n) = t
            && is_generated(n)
        {
            self.0.get_or_insert_with(|| n.clone());
        }
    }
}

/// The message a policy or a macro body gets for writing a generated name.
pub(crate) fn generated_ref_message(name: &str) -> String {
    format!(
        "`${name}` is the canonical text's spelling of a binder that macro expansion generated; \
         a policy or a macro body cannot write it"
    )
}

/// Every binder reference to a generated name (`$t$372`) read as the binder
/// `t$372` itself: a binder slot as its name, a term as the variable.
fn resolve_generated(c: &mut Condition) {
    struct Resolve;
    impl Visit for Resolve {
        fn slot(&mut self, s: &mut BinderSlot) {
            if let BinderSlot::BinderRef(n) = s
                && is_generated(n)
            {
                *s = BinderSlot::Name(std::mem::take(n));
            }
        }
        fn term(&mut self, t: &mut Term) {
            if let Term::BinderRef(n) = t
                && is_generated(n)
            {
                *t = Term::Var(std::mem::take(n));
            }
        }
    }
    walk_condition(c, &mut Resolve);
}

/// The first node of `c` that a lowered leaf cannot hold, named: a macro call,
/// a macro parameter or binder reference, a refinement, a disjunction (which
/// only the lowering of other dialects makes), or an array constant (which
/// lowering rejects).
pub(crate) fn not_lowered(c: &Condition) -> Option<&'static str> {
    #[derive(Default)]
    struct Find(Option<&'static str>);
    impl Find {
        fn found(&mut self, what: &'static str) {
            self.0.get_or_insert(what);
        }
    }
    impl Visit for Find {
        fn slot(&mut self, s: &mut BinderSlot) {
            match s {
                BinderSlot::Name(_) => {}
                BinderSlot::ParamRef(_) => self.found("a macro parameter"),
                BinderSlot::BinderRef(_) => self.found("a macro binder reference"),
            }
        }
        fn term(&mut self, t: &mut Term) {
            match t {
                Term::ParamRef(_) => self.found("a macro parameter"),
                Term::BinderRef(_) => self.found("a macro binder reference"),
                Term::Array(_) => self.found("an array constant"),
                _ => {}
            }
        }
        fn condition(&mut self, c: &mut ConditionKind) {
            match c {
                ConditionKind::Or { .. } => self.found("a disjunction"),
                ConditionKind::Call(_) => self.found("a macro call"),
                ConditionKind::SigilRef { .. } => self.found("a macro parameter"),
                ConditionKind::Refine { .. } => self.found("a refinement"),
                _ => {}
            }
        }
        fn within(&mut self, w: &mut WithinSpec) {
            if let WithinSpec::ParamRef(_) = w {
                self.found("a window parameter");
            }
        }
        fn agg(&mut self, a: &mut AggExprKind) {
            if let AggExprKind::Call(_) = a {
                self.found("a macro call");
            }
        }
    }
    let mut find = Find::default();
    walk_condition(&mut c.clone(), &mut find);
    find.0
}

// ─── The text ────────────────────────────────────────────────────────────

/// **Read a leaf's canonical text** ([`condition_text`]) back: the condition,
/// with every generated binder (`$t$372`) its name (`t$372`), checked as a
/// policy's temporal block is checked (its bindings, its closedness, its
/// evaluation order, arithmetic only with the experimental feature). A text
/// with a node a lowered leaf cannot hold (a macro call or parameter, a
/// refinement, a disjunction, an array constant) is rejected.
pub fn parse_leaf_condition(text: &str) -> Result<Condition, TextError> {
    let mut c = super::parse::parse_condition_unchecked(text).map_err(TextError::new)?;
    resolve_generated(&mut c);
    if let Some(what) = not_lowered(&c) {
        return Err(TextError::new(format!(
            "the condition holds {what}, which a lowered temporal leaf cannot"
        )));
    }
    super::check::check_condition(&c, &std::collections::BTreeSet::new())
        .and_then(|()| super::check::check_leaf_closed(&c))
        .and_then(|()| super::check::check_demands(&c))
        .and_then(|()| super::check::reject_arithmetic_unless_enabled(&c))
        .map_err(TextError::new)?;
    Ok(c)
}

/// **The canonical text of a lowered temporal leaf**: the condition as
/// Dogwood's grammar writes it, fully parenthesized, every generated binder
/// spelled `$<name>`. Its parse ([`parse_leaf_condition`]) is `c` up to the
/// spans, which this function checks: a condition that would not read back as
/// itself (a node a lowered leaf cannot hold, a name the grammar cannot spell)
/// is an error.
pub fn condition_text(c: &Condition) -> Result<String, TextError> {
    if let Some(what) = not_lowered(c) {
        return Err(TextError::new(format!(
            "the condition holds {what}, which a lowered temporal leaf cannot"
        )));
    }
    let mut text = String::new();
    print_condition(c, &mut text);
    match parse_leaf_condition(&text) {
        Ok(back) if without_spans(&back) == without_spans(c) => Ok(text),
        Ok(_) => Err(TextError::new(
            "the condition has no canonical text: its printing reads back as another condition",
        )),
        Err(e) => Err(TextError::new(format!(
            "the condition has no canonical text: its printing does not read back ({e})"
        ))),
    }
}

// ─── The printer ─────────────────────────────────────────────────────────
//
// Every sub-condition in an operand position is parenthesized, and so is every
// compound term in an operand position (an aggregate, an arithmetic
// expression), so that no reading depends on precedence or on where an
// aggregate's `where` body ends. Strings, entity ids, action names and decimal
// payloads are quoted as Cedar's unescaper reads them back
// (`crate::render::quote`); field paths are written as the grammar spells them.
// `condition_text` checks the result by parsing it.

fn print_group(c: &Condition, out: &mut String) {
    out.push('(');
    print_condition(c, out);
    out.push(')');
}

fn print_window(w: &WithinSpec, out: &mut String) {
    match w {
        WithinSpec::Concrete(i) => out.push_str(&i.render()),
        // `not_lowered` excludes it; print it as the grammar's sigil.
        WithinSpec::ParamRef(p) => {
            out.push('?');
            out.push_str(p);
        }
    }
}

fn print_slot(s: &BinderSlot, out: &mut String) {
    match s {
        BinderSlot::Name(n) => print_name(n, out),
        BinderSlot::ParamRef(p) => {
            out.push('?');
            out.push_str(p);
        }
        BinderSlot::BinderRef(b) => {
            out.push('$');
            out.push_str(b);
        }
    }
}

/// A binder's name: as written, or, for a generated one, with the binder
/// sigil (`$t$372`).
fn print_name(n: &str, out: &mut String) {
    if is_generated(n) {
        out.push('$');
    }
    out.push_str(n);
}

fn print_binders(bs: &[TypedBinder], out: &mut String) {
    for (k, b) in bs.iter().enumerate() {
        if k > 0 {
            out.push_str(", ");
        }
        out.push('(');
        print_slot(&b.slot, out);
        out.push_str(": ");
        out.push_str(&b.ty.render());
        out.push(')');
    }
}

fn print_condition(c: &Condition, out: &mut String) {
    match &c.kind {
        ConditionKind::And { left, right } | ConditionKind::Or { left, right } => {
            print_group(left, out);
            out.push_str(if matches!(c.kind, ConditionKind::And { .. }) {
                " && "
            } else {
                " || "
            });
            print_group(right, out);
        }
        ConditionKind::Not { inner } => {
            out.push('!');
            print_group(inner, out);
        }
        ConditionKind::Formerly { within, body } | ConditionKind::Previous { within, body } => {
            out.push_str(if matches!(c.kind, ConditionKind::Formerly { .. }) {
                "formerly within "
            } else {
                "previous within "
            });
            print_window(within, out);
            out.push(' ');
            print_group(body, out);
        }
        ConditionKind::Since {
            left,
            within,
            right,
        } => {
            print_group(left, out);
            out.push_str(" since within ");
            print_window(within, out);
            out.push(' ');
            print_group(right, out);
        }
        ConditionKind::Predicate(p) => {
            out.push_str(&p.namespace.join("::"));
            out.push_str("::");
            out.push_str(&crate::render::quote(&p.action));
            out.push_str("::");
            out.push_str(&p.kind);
            if p.args.is_empty() {
                out.push_str("{}");
            } else {
                out.push_str("{ ");
                for (k, a) in p.args.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&a.name);
                    out.push_str(": ");
                    print_term(&a.value, out);
                }
                out.push_str(" }");
            }
        }
        ConditionKind::Comparison { op, left, right } => {
            print_operand(left, out);
            out.push_str(match op {
                super::ast::CmpOp::Le => " <= ",
                super::ast::CmpOp::Lt => " < ",
                super::ast::CmpOp::Ge => " >= ",
                super::ast::CmpOp::Gt => " > ",
                super::ast::CmpOp::Eq => " == ",
                super::ast::CmpOp::NotEq => " != ",
            });
            print_operand(right, out);
        }
        ConditionKind::Exists { var, body } => {
            out.push_str("exists ");
            print_binders(std::slice::from_ref(var), out);
            out.push_str(". ");
            print_group(body, out);
        }
        ConditionKind::Tp { var } => {
            out.push_str("tp(");
            print_slot(var, out);
            out.push(')');
        }
        // `not_lowered` excludes these; print something that does not parse
        // as a lowered leaf.
        ConditionKind::Call(_) | ConditionKind::SigilRef { .. } | ConditionKind::Refine { .. } => {
            out.push_str("<macro>");
        }
    }
}

/// A term in an operand position: a compound one parenthesized.
fn print_operand(t: &Term, out: &mut String) {
    if matches!(t, Term::Agg(_) | Term::Arith { .. }) {
        out.push('(');
        print_term(t, out);
        out.push(')');
    } else {
        print_term(t, out);
    }
}

fn print_term(t: &Term, out: &mut String) {
    match t {
        Term::Entity { ty, id } => {
            out.push_str(ty);
            out.push_str("::");
            out.push_str(&crate::render::quote(id));
        }
        Term::Integer(n) => out.push_str(&n.to_string()),
        Term::Decimal(s) => {
            out.push_str("decimal(");
            out.push_str(&crate::render::quote(s));
            out.push(')');
        }
        Term::String(s) => out.push_str(&crate::render::quote(s)),
        Term::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Term::ContextField(path) => out.push_str(&crate::field_path::join_under("context", path)),
        Term::ScopeField(path) => out.push_str(&crate::field_path::join(path)),
        Term::Var(v) => print_name(v, out),
        Term::Wildcard => out.push('*'),
        Term::Array(items) => {
            out.push('[');
            for (k, item) in items.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                print_term(item, out);
            }
            out.push(']');
        }
        Term::Agg(agg) => match &agg.kind {
            AggExprKind::Sum {
                bound_var,
                for_vars,
                body,
            } => {
                out.push_str("sum ");
                print_slot(bound_var, out);
                out.push_str(" for ");
                print_binders(for_vars, out);
                out.push_str(". where ");
                print_group(body, out);
            }
            AggExprKind::Count { for_vars, body } => {
                out.push_str("count for ");
                print_binders(for_vars, out);
                out.push_str(". where ");
                print_group(body, out);
            }
            AggExprKind::Call(_) => out.push_str("<macro>"),
        },
        Term::Arith { op, left, right } => {
            print_operand(left, out);
            out.push(' ');
            out.push_str(op.token());
            out.push(' ');
            print_operand(right, out);
        }
        Term::ParamRef(p) => {
            out.push('?');
            out.push_str(p);
        }
        Term::BinderRef(b) => {
            out.push('$');
            out.push_str(b);
        }
    }
}

#[cfg(test)]
mod tests;
