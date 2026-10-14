//! Informalize a parsed, macro-expanded policy into structured semi-English:
//! the prose counterpart of [`crate::render`]. Deterministic — a pure function
//! of the AST and the optional schemas, with no language model.
//!
//! # Contract
//!
//! The output is **meaning-preserving**: read literally, the prose states the
//! same condition as the policy. It follows the policy's structure — one
//! phrase per AST node, children in source order — except for the rewrites
//! below, each of which applies only under the condition that makes it exact
//! and otherwise falls back to the node-by-node phrasing:
//!
//! * **`since` reads in time order**: the anchor (the right operand) and its
//!   window first, then what has (or has not) held "since then".
//! * **Same-as-the-request fields merge**: a predicate's args that compare an
//!   event field with the request's field at the same path read once, "with
//!   this request's user and stock", where the first of them stands. A
//!   `since` whose two sides compare exactly the same field paths refers back
//!   on its second row ("for that user").
//! * **Per-event aggregates drop their timepoint binder**: `count for (t).
//!   where formerly within W (P && tp(t))` reads "the number of P within the
//!   last W", the matching `sum` "the total f of P within the last W", and a
//!   `count` with no past operator "the number of P, counting only this
//!   request itself" —
//!   when `t` occurs nowhere else in P, and (for `sum`) the summed
//!   variable is the whole value of exactly one arg of P and occurs nowhere
//!   else in it.
//! * **A once-used aggregate binder is its comparison**: `exists (n). (agg ==
//!   n && n op x)` reads "agg op x" when `n` occurs nowhere else.
//! * **A single-field filter folds into its event**: `exists (a). (L && a op
//!   x)` reads "… with f op x …" when `a` is bound by exactly one predicate
//!   arg in `L` (reached only through `&&`, `formerly`, `previous` and other
//!   `exists`) and does not occur in `x`.
//!
//! Wording choices that do not change structure: an `exists` binder is named
//! after the field it is bound to when every such field has the same name
//! ("for some user u"); the `input.` group is dropped from a field name
//! unless another field in the rule would then read the same.
//!
//! The only synthesized phrases are framing: the rule header, the event
//! schema's pins stated once as a preamble, and the `(…)` that fences a
//! compound operand so the prose keeps the AST's grouping (as
//! [`crate::render`] fully parenthesizes). Schema identifiers (actions,
//! fields, entity types, binders) are reproduced verbatim.
//!
//! # Phrase tree and spans
//!
//! Because of the rewrites, the [`Phrase`] tree is **not** isomorphic to the
//! AST. Every phrase carries the `.dw` span of the node it renders; a
//! rewritten construct is one phrase carrying the span of the outermost node
//! it covers (a folded filter carries its `exists`), and the nodes it absorbs
//! (the folded comparison, the dropped binder) have
//! no phrase of their own. Consumers mapping phrases back to source should
//! not assume one phrase per node.
//!
//! Like [`crate::render`], this runs on the post-macro-expansion tree and
//! panics on transient nodes (`ParamRef`, `Call`, `SigilRef`, `Refine`, `?w`).

use std::collections::BTreeSet;
use std::fmt;

use cedar_policy_core::ast as cedar_ast;

use crate::ast::{Annotation, BinOp, Cond, CondKeyword, Effect, Expr, ExprKind, Policy, UnOp};
use crate::event_schema::ast::{EventSchema, FieldSpec, PinRoot, PinValue, TypeExpr};
use crate::extension::Extension;
use crate::extension::temporal::ast as tast;
use crate::policy_view::{ActionConstraint, PolicyScope, PrincipalConstraint, ResourceConstraint};
use crate::render::{BinderRenames, binder_renames, quote};

// ─── Output types ─────────────────────────────────────────────────────────

/// One node of an informalized policy: a template with `{0}`, `{1}`, … slots
/// for its children. The tree follows the AST except where a rewrite merges
/// nodes (see the module docs); render it with [`Display`](fmt::Display) or
/// walk it.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct Phrase {
    /// The phrase text with `{i}` placeholders for `children[i]`; literal
    /// braces are doubled (`{{`, `}}`), as in `std::fmt`.
    pub template: String,
    /// The sub-phrases, in source order (except `since`, anchor first).
    pub children: Vec<Phrase>,
    /// `[start, end)` byte range of the originating `.dw` node — for a
    /// rewritten construct, the outermost node it covers; `None` for
    /// synthesized framing such as the rule header.
    pub span: Option<(usize, usize)>,
    /// How the plain-text renderer lays the children out.
    pub layout: Layout,
}

/// Plain-text layout of a [`Phrase`]'s children — a rendering hint only; the
/// tree is the contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub enum Layout {
    /// Children are spliced into the template where they fall; a multi-row
    /// child continues one level deeper.
    Inline,
    /// The leading text is a header row; each child sits on its own rows one
    /// level deeper, with the text between slots (e.g. "and") glued onto the
    /// child's first row. Used for clause lists and `&&` / `||` chains.
    Block,
    /// [`Inline`](Layout::Inline) when every child fits on one row, otherwise
    /// [`Block`](Layout::Block). Used for header-plus-body shapes.
    Hanging,
}

impl Phrase {
    fn new(
        template: impl Into<String>,
        children: Vec<Phrase>,
        span: Option<Span2>,
        layout: Layout,
    ) -> Phrase {
        Phrase {
            template: template.into(),
            children,
            span,
            layout,
        }
    }

    fn inline(template: impl Into<String>, children: Vec<Phrase>, span: Option<Span2>) -> Phrase {
        Phrase::new(template, children, span, Layout::Inline)
    }

    fn block(template: impl Into<String>, children: Vec<Phrase>, span: Option<Span2>) -> Phrase {
        Phrase::new(template, children, span, Layout::Block)
    }

    fn hanging(template: impl Into<String>, children: Vec<Phrase>, span: Option<Span2>) -> Phrase {
        Phrase::new(template, children, span, Layout::Hanging)
    }

    /// A childless phrase whose text is taken literally (braces escaped).
    fn leaf(text: impl Into<String>, span: Option<Span2>) -> Phrase {
        Phrase::inline(esc(&text.into()), Vec::new(), span)
    }

    /// The phrase as indented plain text, one line per row, no trailing
    /// newline.
    pub fn to_text(&self) -> String {
        let mut lines = Vec::new();
        self.emit(0, &mut lines);
        lines
            .into_iter()
            // A row may contain newlines (a multi-line header); indent each.
            .flat_map(|(indent, text)| {
                text.split('\n')
                    .map(|line| format!("{}{}", "  ".repeat(indent), line))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Render into `(indent, text)` rows according to [`Layout`].
    fn emit(&self, indent: usize, out: &mut Vec<(usize, String)>) {
        let rendered: Vec<Vec<(usize, String)>> = self
            .children
            .iter()
            .map(|c| {
                let mut rows = Vec::new();
                c.emit(0, &mut rows);
                rows
            })
            .collect();
        let pieces = tokenize_template(&self.template, self.children.len());
        let multi = rendered.iter().any(|r| r.len() > 1);
        let layout = match self.layout {
            Layout::Hanging if multi => Layout::Block,
            Layout::Hanging => Layout::Inline,
            other => other,
        };

        match layout {
            Layout::Block => {
                // Header row, then each child one level deeper with the text
                // before its slot ("and …") glued onto its first row.
                let mut child_indent = indent;
                let mut pending = String::new();
                let mut seen_child = false;
                let mut has_header = false;
                for piece in &pieces {
                    match piece {
                        Piece::Text(t) => pending.push_str(t),
                        Piece::Slot(i) => {
                            let prefix = pending.trim().to_string();
                            pending.clear();
                            if !seen_child && !prefix.is_empty() {
                                out.push((indent, prefix.clone()));
                                child_indent = indent + 1;
                                has_header = true;
                            }
                            // Continuation rows shift one level deeper than
                            // the child's first row so operands stay
                            // distinguishable — except a flat same-operator
                            // chain (`(a && b) && c`) or a body already set
                            // off by a header, which are not shifted.
                            let child = &self.children[*i];
                            let flat_chain = !seen_child && child.template == self.template;
                            let body_under_header = !seen_child && has_header;
                            let glue = if seen_child { prefix.as_str() } else { "" };
                            push_child_rows(
                                out,
                                child_indent,
                                glue,
                                &rendered[*i],
                                flat_chain || body_under_header,
                            );
                            seen_child = true;
                        }
                    }
                }
                let tail = pending.trim().to_string();
                if !tail.is_empty() {
                    out.push((child_indent, tail));
                }
            }
            Layout::Inline | Layout::Hanging => {
                // After a multi-row child, the text that follows (a closing
                // `)`, a trailing `> 1000`) is glued onto that child's last
                // row instead of starting a detached row of its own.
                let mut pending = String::new();
                let mut glue_to: Option<usize> = None;
                let flush = |out: &mut Vec<(usize, String)>,
                             pending: &mut String,
                             glue_to: Option<usize>| {
                    match glue_to {
                        Some(row) => out[row].1.push_str(&std::mem::take(pending)),
                        None => out.push((indent, std::mem::take(pending))),
                    }
                };
                for piece in &pieces {
                    match piece {
                        Piece::Text(t) => pending.push_str(t),
                        Piece::Slot(i) => match rendered[*i].split_first() {
                            None => {}
                            Some((first, [])) => pending.push_str(&first.1),
                            Some((first, rest)) => {
                                // Start the child on this row; its
                                // continuation rows go deeper than it.
                                pending.push_str(&first.1);
                                flush(out, &mut pending, glue_to);
                                let shift = continuation_shift(&rendered[*i]);
                                for (d, t) in rest {
                                    out.push((indent + d + shift, t.clone()));
                                }
                                glue_to = Some(out.len() - 1);
                            }
                        },
                    }
                }
                if glue_to.is_some() {
                    if !pending.trim().is_empty() {
                        flush(out, &mut pending, glue_to);
                    }
                } else {
                    let tail = pending.trim().to_string();
                    if !tail.is_empty() {
                        out.push((indent, tail));
                    }
                }
            }
        }
    }
}

/// Append a child's `rows` at `indent`, gluing `prefix` (e.g. "and") onto the
/// first row. Unless `flat`, continuation rows go at least one level deeper
/// than the first.
fn push_child_rows(
    out: &mut Vec<(usize, String)>,
    indent: usize,
    prefix: &str,
    rows: &[(usize, String)],
    flat: bool,
) {
    let shift = if flat { 0 } else { continuation_shift(rows) };
    for (i, (d, t)) in rows.iter().enumerate() {
        let depth = if i == 0 {
            indent + d
        } else {
            indent + d + shift
        };
        if i == 0 && !prefix.is_empty() {
            out.push((depth, format!("{prefix} {t}")));
        } else {
            out.push((depth, t.clone()));
        }
    }
}

/// Shift needed so a child's continuation rows sit deeper than its first row:
/// one for a flat chain, zero for a header-plus-body already indented.
fn continuation_shift(rows: &[(usize, String)]) -> usize {
    match rows.iter().skip(1).map(|(d, _)| *d).min() {
        Some(0) => 1,
        _ => 0,
    }
}

/// A template piece: literal text or a `{i}` child slot.
#[derive(Debug, PartialEq, Eq)]
enum Piece {
    Text(String),
    Slot(usize),
}

/// Tokenize `template` into text and `{i}` slots. Every slot index must be
/// below `n`; slots may appear in any order. As in `std::fmt`, `{{` and `}}`
/// are literal braces — text spliced into a template from the policy or the
/// schema goes through [`esc`] so it can never be read as a slot. A lone
/// brace that is neither an escape nor a slot is kept as text.
fn tokenize_template(template: &str, n: usize) -> Vec<Piece> {
    let mut pieces = Vec::new();
    let mut text = String::new();
    let mut rest = template;
    while let Some(c) = rest.chars().next() {
        if rest.starts_with("{{") || rest.starts_with("}}") {
            text.push(c);
            rest = &rest[2..];
            continue;
        }
        if c == '{'
            && let Some(close) = rest.find('}')
            && let Ok(i) = rest[1..close].parse::<usize>()
        {
            assert!(
                i < n,
                "informalize: template {template:?} slot {{{i}}} out of range"
            );
            if !text.is_empty() {
                pieces.push(Piece::Text(std::mem::take(&mut text)));
            }
            pieces.push(Piece::Slot(i));
            rest = &rest[close + 1..];
            continue;
        }
        text.push(c);
        rest = &rest[c.len_utf8()..];
    }
    if !text.is_empty() {
        pieces.push(Piece::Text(text));
    }
    pieces
}

/// Escape `{` / `}` in text spliced into a [`Phrase`] template, so author- or
/// schema-controlled text (string literals, annotation values, attribute
/// names, patterns, entity ids) is never mistaken for a child slot.
fn esc(s: &str) -> String {
    s.replace('{', "{{").replace('}', "}}")
}

impl fmt::Display for Phrase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_text())
    }
}

/// The informalization of a policy set (or of one policy, via
/// `ParsedPolicy::informalize`): an optional preamble stating event-schema
/// facts that apply to every rule, then one [`Phrase`] per rule in source
/// order.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct Informalization {
    /// The event schema's pins, which restrict which past events every
    /// temporal clause below can match, or `None` if there is no temporal
    /// clause or the schema pins nothing.
    pub preamble: Option<Phrase>,
    /// One phrase tree per rule, in source order.
    pub rules: Vec<Phrase>,
}

impl fmt::Display for Informalization {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        if let Some(p) = &self.preamble {
            f.write_str(&p.to_text())?;
            first = false;
        }
        for r in &self.rules {
            if !first {
                f.write_str("\n\n")?;
            }
            f.write_str(&r.to_text())?;
            first = false;
        }
        Ok(())
    }
}

type Span2 = (usize, usize);

fn sp(span: crate::error::Span) -> Option<Span2> {
    Some((span.start, span.end))
}

// ─── Schema facts ─────────────────────────────────────────────────────────

/// What the informalizer reads off the (optional) action schema: the set of
/// declared namespaces, to decide whether qualification may be dropped.
pub(crate) struct SchemaFacts {
    /// `Some(ns)` iff the schema declares exactly one non-empty namespace.
    single_namespace: Option<String>,
}

impl SchemaFacts {
    /// No schema: nothing is dropped.
    pub(crate) fn none() -> SchemaFacts {
        SchemaFacts {
            single_namespace: None,
        }
    }

    /// Read the facts from Cedar schema text; a schema that does not compile
    /// yields [`SchemaFacts::none`] (informalization never fails on the schema).
    pub(crate) fn from_cedarschema_str(src: &str) -> SchemaFacts {
        let Ok((schema, _warnings)) = cedar_policy::Schema::from_cedarschema_str(src) else {
            return SchemaFacts::none();
        };
        let mut namespaces: BTreeSet<String> = BTreeSet::new();
        for ty in schema.entity_types() {
            namespaces.insert(ty.namespace());
        }
        for action in schema.actions() {
            namespaces.insert(action.type_name().namespace());
        }
        namespaces.remove("");
        let single_namespace = if namespaces.len() == 1 {
            namespaces.into_iter().next()
        } else {
            None
        };
        SchemaFacts { single_namespace }
    }

    /// Drop the single declared namespace from a qualified name, if it is
    /// that namespace. `Drupe::User` → `User`; `Other::User` stays.
    fn strip_ns(&self, qualified: &str) -> String {
        if let Some(ns) = &self.single_namespace {
            let prefix = format!("{ns}::");
            if let Some(rest) = qualified.strip_prefix(&prefix) {
                return rest.to_string();
            }
        }
        qualified.to_string()
    }
}

// ─── Policy set ─────────────────────────────────────────────────────────

/// Informalize a whole policy set into an [`Informalization`].
pub(crate) fn informalize_set(
    policies: &[Policy],
    event_schema: &EventSchema,
    facts: &SchemaFacts,
) -> Informalization {
    let any_temporal = policies.iter().any(|p| p.temporal_block_count() > 0);
    let preamble = if any_temporal {
        preamble_phrase(event_schema)
    } else {
        None
    };
    let rules = policies
        .iter()
        .enumerate()
        .map(|(i, p)| rule_phrase(p, i, event_schema, facts))
        .collect();
    Informalization { preamble, rules }
}

/// Informalize one policy (at `index` in its set) into an [`Informalization`]
/// with that single rule, carrying the pin preamble when the policy has a
/// temporal clause — so it reads exactly as it would inside the set.
pub(crate) fn informalize_single(
    policy: &Policy,
    index: usize,
    event_schema: &EventSchema,
    facts: &SchemaFacts,
) -> Informalization {
    let preamble = if policy.temporal_block_count() > 0 {
        preamble_phrase(event_schema)
    } else {
        None
    };
    Informalization {
        preamble,
        rules: vec![rule_phrase(policy, index, event_schema, facts)],
    }
}

// ─── Short names ────────────────────────────────────────────────────────

thread_local! {
    /// The field names that must keep their `input.` group while the current
    /// rule or preamble is phrased (see [`with_short_names`]).
    static AMBIGUOUS_SHORT_NAMES: std::cell::RefCell<BTreeSet<String>> =
        const { std::cell::RefCell::new(BTreeSet::new()) };
}

/// Phrase one rule with the `input.` group dropped only where that is
/// unambiguous within the rule and the event schema's pins.
fn rule_phrase(
    policy: &Policy,
    index: usize,
    event_schema: &EventSchema,
    facts: &SchemaFacts,
) -> Phrase {
    let mut paths = pin_paths(event_schema);
    for cond in &policy.conditions {
        expr_paths(&cond.body, &mut paths);
    }
    with_short_names(&paths, || informalize_policy(policy, index, facts))
}

/// The pin preamble, with short names decided by the pins alone, so it reads
/// the same in a set and for a single policy.
fn preamble_phrase(event_schema: &EventSchema) -> Option<Phrase> {
    with_short_names(&pin_paths(event_schema), || pin_preamble(event_schema))
}

/// Run `f` with the `input.` group dropped from a field (`input.user` →
/// "user") only when no other field among `paths` — each a context path or
/// an event field path, both of which nest `input` the same way — would read
/// the same (a top-level `user`). Otherwise the group stays ("input user").
fn with_short_names<R>(paths: &[Vec<String>], f: impl FnOnce() -> R) -> R {
    let from_input: BTreeSet<String> = paths
        .iter()
        .filter(|p| p.len() > 1 && p[0] == "input")
        .map(|p| p[1..].join("."))
        .collect();
    let ambiguous: BTreeSet<String> = paths
        .iter()
        .filter(|p| p.first().is_some_and(|g| g != "input"))
        .map(|p| p.join("."))
        .filter(|name| from_input.contains(name))
        .collect();
    let previous = AMBIGUOUS_SHORT_NAMES.with(|a| a.replace(ambiguous));
    // Restored on drop, so a panic in `f` cannot leave this rule's set in
    // place for a later call on the same thread.
    let _restore = OnDrop(Some(move || {
        AMBIGUOUS_SHORT_NAMES.with(|a| a.replace(previous));
    }));
    f()
}

/// Runs its closure when dropped, including during unwinding: restores the
/// informalizer's thread-local state however the scope is left.
struct OnDrop<F: FnOnce()>(Option<F>);

impl<F: FnOnce()> Drop for OnDrop<F> {
    fn drop(&mut self) {
        if let Some(f) = self.0.take() {
            f();
        }
    }
}

thread_local! {
    /// The binder renaming of the temporal block being phrased (see
    /// [`with_binder_renames`]).
    static BINDER_RENAMES: std::cell::RefCell<BinderRenames> =
        std::cell::RefCell::new(BinderRenames::default());
}

/// Run `f` with the binder names of temporal condition `c` renamed as
/// [`crate::render`] renames them: a macro-minted binder (`t$29`) gets the
/// first free surface name (`t_29`, `t_29_1`, ...), never one the condition
/// already uses, so `explain` and the rendered policy name binders alike.
fn with_binder_renames<R>(c: &tast::Condition, f: impl FnOnce() -> R) -> R {
    let previous = BINDER_RENAMES.with(|r| r.replace(binder_renames(c)));
    let _restore = OnDrop(Some(move || {
        BINDER_RENAMES.with(|r| r.replace(previous));
    }));
    f()
}

/// A binder's surface name under the current temporal block's renaming.
fn binder_display(name: &str) -> String {
    BINDER_RENAMES.with(|r| r.borrow().apply(name))
}

/// `input.<rest>` read as just `<rest>`, when that is unambiguous (see
/// [`with_short_names`]); `None` for any other path.
fn short_input_name(path: &[String]) -> Option<String> {
    match path {
        [group, rest @ ..] if group == "input" && !rest.is_empty() => {
            let name = rest.join(".");
            let ambiguous = AMBIGUOUS_SHORT_NAMES.with(|a| a.borrow().contains(&name));
            (!ambiguous).then_some(name)
        }
        _ => None,
    }
}

/// The event field paths and request context paths the pins mention.
fn pin_paths(schema: &EventSchema) -> Vec<Vec<String>> {
    let mut out = Vec::new();
    for decl in &schema.decls {
        for (name, pin) in declared_pins(&decl.fields) {
            out.push(name.split('.').map(str::to_string).collect());
            if pin.root == PinRoot::Context {
                out.push(pin.context_path.clone());
            }
        }
    }
    out
}

/// Every request context path (`context.a.b` → `[a, b]`) and event field
/// path (`P{ a.b: … }` → `[a, b]`) in a Cedar expression, including inside
/// temporal blocks.
fn expr_paths(e: &Expr, out: &mut Vec<Vec<String>>) {
    if let Some((cedar_ast::Var::Context, path)) = var_path(e) {
        out.push(path);
        return;
    }
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Var(_) | ExprKind::Slot(_) | ExprKind::ParamRef { .. } => {}
        ExprKind::Extension(Extension::Temporal(t)) => cond_paths(&t.condition, out),
        ExprKind::UnaryApp { expr, .. }
        | ExprKind::GetAttr { expr, .. }
        | ExprKind::Like { expr, .. } => expr_paths(expr, out),
        ExprKind::HasAttr { expr, attrs } => {
            if let Some((cedar_ast::Var::Context, mut path)) = var_path(expr) {
                path.extend(attrs.iter().cloned());
                out.push(path);
            } else {
                expr_paths(expr, out);
            }
        }
        ExprKind::BinaryApp { left, right, .. } => {
            expr_paths(left, out);
            expr_paths(right, out);
        }
        ExprKind::Is { expr, in_expr, .. } => {
            expr_paths(expr, out);
            if let Some(g) = in_expr {
                expr_paths(g, out);
            }
        }
        ExprKind::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_paths(cond, out);
            expr_paths(then_expr, out);
            expr_paths(else_expr, out);
        }
        ExprKind::Set(items) => items.iter().for_each(|x| expr_paths(x, out)),
        ExprKind::Record(entries) => entries.iter().for_each(|(_, v)| expr_paths(v, out)),
        ExprKind::Call { args, .. } => args.iter().for_each(|a| expr_paths(a, out)),
        ExprKind::MethodCall { receiver, args, .. } => {
            expr_paths(receiver, out);
            args.iter().for_each(|a| expr_paths(a, out));
        }
    }
}

/// [`expr_paths`] for a temporal condition.
fn cond_paths(c: &tast::Condition, out: &mut Vec<Vec<String>>) {
    use tast::ConditionKind as K;
    match &c.kind {
        K::And { left, right } | K::Or { left, right } | K::Since { left, right, .. } => {
            cond_paths(left, out);
            cond_paths(right, out);
        }
        K::Not { inner } => cond_paths(inner, out),
        K::Formerly { body, .. } | K::Previous { body, .. } | K::Exists { body, .. } => {
            cond_paths(body, out)
        }
        K::Predicate(p) => {
            for arg in &p.args {
                out.push(arg.field_path());
                term_paths(&arg.value, out);
            }
        }
        K::Comparison { left, right, .. } => {
            term_paths(left, out);
            term_paths(right, out);
        }
        K::Tp { .. } | K::Call(_) | K::SigilRef { .. } | K::Refine { .. } => {}
    }
}

/// [`expr_paths`] for a temporal term.
fn term_paths(t: &tast::Term, out: &mut Vec<Vec<String>>) {
    use tast::Term as T;
    match t {
        T::ContextField(path) => out.push(path.clone()),
        T::Array(items) => items.iter().for_each(|i| term_paths(i, out)),
        T::Arith { left, right, .. } => {
            term_paths(left, out);
            term_paths(right, out);
        }
        T::Agg(agg) => match &agg.kind {
            tast::AggExprKind::Count { body, .. } | tast::AggExprKind::Sum { body, .. } => {
                cond_paths(body, out)
            }
            tast::AggExprKind::Call(_) => {}
        },
        _ => {}
    }
}

/// The event schema's pins as one sentence when every kind pins the same
/// fields ("Only past events from this request's principal count."), else
/// one such sentence per pinning kind, or `None` if nothing is pinned.
fn pin_preamble(schema: &EventSchema) -> Option<Phrase> {
    let per_kind: Vec<(String, Vec<(String, &PinValue)>)> = schema
        .decls
        .iter()
        .map(|d| (d.kind.clone(), declared_pins(&d.fields)))
        .collect();
    if per_kind.is_empty() || per_kind.iter().all(|(_, pins)| pins.is_empty()) {
        return None;
    }
    let first = &per_kind[0].1;
    let universal = per_kind.iter().all(|(_, pins)| {
        pins.len() == first.len()
            && pins.iter().zip(first.iter()).all(|((n1, p1), (n2, p2))| {
                n1 == n2 && p1.context_path == p2.context_path && p1.root == p2.root
            })
    });
    if universal && !first.is_empty() {
        return Some(Phrase::leaf(pin_sentence("past events", first), None));
    }
    let children: Vec<Phrase> = per_kind
        .iter()
        .filter(|(_, pins)| !pins.is_empty())
        .map(|(kind, pins)| Phrase::leaf(pin_sentence(&format!("past {kind} events"), pins), None))
        .collect();
    // One row per kind: Block layout with no header text puts each child on
    // its own row at the same depth.
    Some(Phrase::block(slots(children.len(), " "), children, None))
}

/// "Only past events from this request's principal and with this request's
/// x count." A pin that compares an event field with the request's
/// same-named value reads "… this request's f"; any other pin reads "whose f
/// is v".
fn pin_sentence(events: &str, pins: &[(String, &PinValue)]) -> String {
    let mut same = Vec::new();
    let mut whose = Vec::new();
    for (field, pin) in pins {
        match same_as_request(field, pin) {
            Some(s) => same.push(s),
            None => whose.push(format!("whose {field} is {}", pin_ref(pin))),
        }
    }
    let parts: Vec<String> = same.into_iter().chain(whose).collect();
    format!("Only {events} {} count.", parts.join(" and "))
}

/// The "this request's" phrasing of a pin, when it has one: the default
/// schema's `callerPrincipal = principal` / `callerResource = resource` read
/// "from this request's principal" / "on this request's resource", and a
/// context pin onto the request's same-named field (`input.` dropped, as
/// elsewhere) reads "with this request's f".
fn same_as_request(field: &str, pin: &PinValue) -> Option<String> {
    let path = pin.context_path.as_slice();
    match pin.root {
        PinRoot::Scope => match (field, path) {
            ("callerPrincipal", [root]) if root == "principal" => {
                Some("from this request's principal".to_string())
            }
            ("callerResource", [root]) if root == "resource" => {
                Some("on this request's resource".to_string())
            }
            _ => None,
        },
        PinRoot::Context => {
            let request_field = short_input_name(path).unwrap_or_else(|| path.join("."));
            (request_field == field).then(|| format!("with this request's {field}"))
        }
    }
}

fn declared_pins(fields: &[FieldSpec]) -> Vec<(String, &PinValue)> {
    let mut pins = Vec::new();
    collect_pins(fields, "", &mut pins);
    pins
}

/// Every pin in `fields`, in declaration order, named by its dotted path.
/// Recurses into record-typed fields, so a pin nested in a group
/// (`__drupe: { pin session_id: … }`) is reported as `__drupe.session_id`
/// rather than dropped: the engine enforces it all the same.
fn collect_pins<'a>(fields: &'a [FieldSpec], prefix: &str, out: &mut Vec<(String, &'a PinValue)>) {
    for f in fields {
        let FieldSpec::Named { name, ty, pin, .. } = f else {
            continue;
        };
        let path = if prefix.is_empty() {
            name.clone()
        } else {
            format!("{prefix}.{name}")
        };
        if let Some(pin) = pin {
            out.push((path.clone(), pin));
        }
        if let TypeExpr::Record(inner) = ty {
            collect_pins(inner, &path, out);
        }
    }
}

fn pin_ref(pin: &PinValue) -> String {
    match pin.root {
        PinRoot::Scope => scope_path_phrase(&pin.context_path),
        PinRoot::Context => context_path_phrase(&pin.context_path),
    }
}

// ─── Policy ─────────────────────────────────────────────────────────────

/// Informalize one rule: header (label, effect, scope), then one child per
/// annotation other than `@id` and per `when`/`unless` clause, in source order.
pub(crate) fn informalize_policy(policy: &Policy, index: usize, facts: &SchemaFacts) -> Phrase {
    // The rule's label on its own row: `@id("x")` in source form, so it is
    // unmistakably the annotation, or `Rule N` when there is none.
    let id_line = policy
        .annotations
        .iter()
        .find(|a| a.key == "id")
        .and_then(|a| a.value.as_deref())
        .map(|v| format!("@id({})", quote(v)))
        .unwrap_or_else(|| format!("Rule {}", index + 1));
    let effect = match policy.effect {
        Effect::Permit => "PERMIT",
        Effect::Forbid => "FORBID",
    };

    let view = PolicyScope::from_scope(&policy.scope);
    let principal = scope_phrase(view.principal().into(), "principal", facts);
    let action = action_phrase(view.action(), facts);
    let resource = scope_phrase(view.resource().into(), "resource", facts);

    let mut children: Vec<Phrase> = Vec::new();
    for ann in &policy.annotations {
        if ann.key == "id" {
            continue;
        }
        children.push(annotation_phrase(ann));
    }
    for cond in &policy.conditions {
        children.push(clause_phrase(cond, facts));
    }

    // The header is two rows — the id line, then the effect/scope line — so
    // the label stands apart. The clauses follow as block children.
    let header = esc(&format!(
        "{id_line}\n{effect} {principal} to perform {action} on {resource}",
    ));
    let mut template = header;
    for i in 0..children.len() {
        template.push_str(&format!(" {{{i}}}"));
    }
    Phrase::block(template, children, sp(policy.span))
}

fn annotation_phrase(ann: &Annotation) -> Phrase {
    match &ann.value {
        Some(v) => Phrase::leaf(format!("(@{}: {})", ann.key, quote(v)), None),
        None => Phrase::leaf(format!("(@{})", ann.key), None),
    }
}

// ─── Scope ──────────────────────────────────────────────────────────────

/// A principal or resource constraint, viewed uniformly (the two enums share a
/// shape) so one phrasing routine serves both.
enum Por<'a> {
    Any,
    In(Option<&'a cedar_policy::EntityUid>),
    Eq(Option<&'a cedar_policy::EntityUid>),
    Is(&'a cedar_policy::EntityTypeName),
    IsIn(
        &'a cedar_policy::EntityTypeName,
        Option<&'a cedar_policy::EntityUid>,
    ),
}

impl<'a> From<&'a PrincipalConstraint> for Por<'a> {
    fn from(c: &'a PrincipalConstraint) -> Self {
        match c {
            PrincipalConstraint::Any => Por::Any,
            PrincipalConstraint::In(u) => Por::In(u.as_ref()),
            PrincipalConstraint::Eq(u) => Por::Eq(u.as_ref()),
            PrincipalConstraint::Is(t) => Por::Is(t),
            PrincipalConstraint::IsIn(t, u) => Por::IsIn(t, u.as_ref()),
        }
    }
}

impl<'a> From<&'a ResourceConstraint> for Por<'a> {
    fn from(c: &'a ResourceConstraint) -> Self {
        match c {
            ResourceConstraint::Any => Por::Any,
            ResourceConstraint::In(u) => Por::In(u.as_ref()),
            ResourceConstraint::Eq(u) => Por::Eq(u.as_ref()),
            ResourceConstraint::Is(t) => Por::Is(t),
            ResourceConstraint::IsIn(t, u) => Por::IsIn(t, u.as_ref()),
        }
    }
}

/// Phrase a principal or resource constraint; `role` is "principal" or
/// "resource" and also names the `?role` template slot. An unconstrained
/// scope reads "any principal" / "any resource"; the schema's `appliesTo`
/// types are not listed.
fn scope_phrase(c: Por<'_>, role: &str, facts: &SchemaFacts) -> String {
    let ty = |t: &cedar_policy::EntityTypeName| facts.strip_ns(&t.to_string());
    let any = format!("any {role}");
    match c {
        Por::Any => any,
        Por::Eq(Some(uid)) => format!("the {role} {}", public_uid(uid, facts)),
        Por::Eq(None) => format!("the {role} given by the ?{role} slot"),
        Por::In(Some(uid)) => format!("{any} in {}", public_uid(uid, facts)),
        Por::In(None) => format!("{any} in the ?{role} slot"),
        Por::Is(t) => format!("any {}", ty(t)),
        Por::IsIn(t, Some(uid)) => format!("any {} in {}", ty(t), public_uid(uid, facts)),
        Por::IsIn(t, None) => format!("any {} in the ?{role} slot", ty(t)),
    }
}

fn action_phrase(c: &ActionConstraint, facts: &SchemaFacts) -> String {
    match c {
        ActionConstraint::Any => "any action".to_string(),
        ActionConstraint::Eq(uid) => public_uid(uid, facts),
        ActionConstraint::In(uids) => action_in_phrase(uids, facts),
    }
}

/// `action in X` / `action in [X, Y]` reads "any action in X, Y, or Z",
/// mirroring Cedar's `in` (which matches each listed action itself and
/// every action grouped under it, at any depth). The names are kept as
/// written.
fn action_in_phrase(uids: &[cedar_policy::EntityUid], facts: &SchemaFacts) -> String {
    let items: Vec<String> = uids.iter().map(|u| public_uid(u, facts)).collect();
    format!("any action in {}", join_or(&items))
}

/// `A`, `A or B`, `A, B, or C`.
fn join_or(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [one] => one.clone(),
        [a, b] => format!("{a} or {b}"),
        [init @ .., last] => format!("{}, or {last}", init.join(", ")),
    }
}

/// A public entity uid: an action (`Drupe::Action::"Read"`) reads as its bare
/// id (`Read`) when the namespace is droppable; any other entity reads as
/// `Type "id"`. Undroppable namespaces keep the full Cedar spelling.
fn public_uid(uid: &cedar_policy::EntityUid, facts: &SchemaFacts) -> String {
    uid_phrase(&uid.type_name().to_string(), uid.id().unescaped(), facts)
}

fn uid_phrase(type_name: &str, id: &str, facts: &SchemaFacts) -> String {
    let stripped = facts.strip_ns(type_name);
    if stripped != type_name && stripped == "Action" {
        return id.to_string();
    }
    if stripped != type_name {
        return format!("{stripped} {}", quote(id));
    }
    // Not droppable: the full Cedar spelling.
    format!("{type_name}::{}", quote(id))
}

// ─── Clauses ────────────────────────────────────────────────────────────

fn clause_phrase(cond: &Cond, facts: &SchemaFacts) -> Phrase {
    let kw = match cond.keyword {
        CondKeyword::When => "when",
        CondKeyword::Unless => "unless",
    };
    match &cond.body.kind {
        // A bare `when temporal { … }` clause.
        ExprKind::Extension(Extension::Temporal(t)) => {
            let body = with_binder_renames(&t.condition, || {
                temporal_condition(&t.condition, t.span.start, Scan::Current, facts)
            });
            Phrase::block(format!("{kw}: {{0}}"), vec![body], sp(cond.span))
        }
        _ => {
            let body = cedar_expr(&cond.body, facts);
            Phrase::hanging(format!("{kw}: {{0}}"), vec![body], sp(cond.span))
        }
    }
}

// ─── Cedar expressions ────────────────────────────────────────────────────

fn cedar_expr(e: &Expr, facts: &SchemaFacts) -> Phrase {
    let span = sp(e.span);
    match &e.kind {
        ExprKind::Lit(lit) => Phrase::leaf(literal_phrase(lit, facts), span),
        ExprKind::Var(var) => Phrase::leaf(var_phrase(*var), span),
        ExprKind::Slot(slot) => Phrase::leaf(format!("the {slot} slot"), span),
        ExprKind::Extension(Extension::Temporal(t)) => {
            // Transparent: the temporal phrases say "occurred within …"
            // themselves; as an operand it is fenced by `cedar_operand`.
            let body = with_binder_renames(&t.condition, || {
                temporal_condition(&t.condition, t.span.start, Scan::Current, facts)
            });
            Phrase::inline("{0}", vec![body], span)
        }

        ExprKind::UnaryApp { op, expr } => {
            // `not ({0})` already fences its operand. A negation's operand
            // is atomic for other operators, but a negation of a negation
            // (or of a negative literal) would read "--x": fence it.
            let inner = match op {
                UnOp::Not => cedar_expr(expr, facts),
                UnOp::Neg
                    if matches!(
                        expr.kind,
                        ExprKind::UnaryApp { op: UnOp::Neg, .. }
                            | ExprKind::Lit(cedar_ast::Literal::Long(i64::MIN..0))
                    ) =>
                {
                    Phrase::inline("({0})", vec![cedar_expr(expr, facts)], None)
                }
                _ => cedar_operand(expr, facts),
            };
            Phrase::inline(unary_template(*op), vec![inner], span)
        }
        ExprKind::BinaryApp { op, left, right } => match op {
            // `&&` / `||` operands sit on their own rows, so the layout
            // already shows the grouping.
            BinOp::And | BinOp::Or => {
                let l = cedar_expr(left, facts);
                let r = cedar_expr(right, facts);
                let template = if *op == BinOp::And {
                    "{0} and {1}"
                } else {
                    "{0} or {1}"
                };
                Phrase::block(template, vec![l, r], span)
            }
            // `x == true` / `x != false` / `true == x`: "x is true".
            BinOp::Eq | BinOp::NotEq if let Some((x, b)) = bool_comparison(left, right) => {
                let negated = *op == BinOp::NotEq;
                Phrase::inline(
                    format!("{{0}} is {}{b}", if negated { "not " } else { "" }),
                    vec![cedar_operand(x, facts)],
                    span,
                )
            }
            _ => {
                let l = comparison_or_operand(*op, left, facts);
                let r = comparison_or_operand(*op, right, facts);
                Phrase::inline(binary_template(*op), vec![l, r], span)
            }
        },
        ExprKind::GetAttr { .. } => {
            // A path rooted at a request variable is one noun phrase ("the
            // request's user"); anything else is "the <attr> field of <expr>"
            // ("the flagged field of Text::Scan(…)").
            if let Some((root, path)) = var_path(e) {
                return Phrase::leaf(rooted_path_phrase(root, &path), span);
            }
            let ExprKind::GetAttr { expr, attr } = &e.kind else {
                unreachable!()
            };
            let inner = cedar_operand(expr, facts);
            Phrase::inline(
                format!("the {} field of {{0}}", esc(attr)),
                vec![inner],
                span,
            )
        }
        ExprKind::HasAttr { expr, attrs } => {
            let inner = cedar_operand(expr, facts);
            Phrase::inline(
                format!("{{0}} has {}", esc(&attrs.join("."))),
                vec![inner],
                span,
            )
        }
        ExprKind::Like { expr, pattern } => {
            let inner = cedar_operand(expr, facts);
            let pat = cedar_ast::Pattern::from(pattern.clone()).to_string();
            Phrase::inline(
                format!("{{0}} matches the pattern \"{}\"", esc(&pat)),
                vec![inner],
                span,
            )
        }
        ExprKind::Is {
            expr,
            entity_type,
            in_expr,
        } => {
            let inner = cedar_operand(expr, facts);
            let ty = esc(&facts.strip_ns(&entity_type.to_string()));
            let art = article_for(&ty);
            match in_expr {
                Some(g) => {
                    let group = cedar_operand(g, facts);
                    Phrase::inline(
                        format!("{{0}} is {art} {ty} in {{1}}"),
                        vec![inner, group],
                        span,
                    )
                }
                None => Phrase::inline(format!("{{0}} is {art} {ty}"), vec![inner], span),
            }
        }
        ExprKind::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => {
            // "then" and ", otherwise" fence the condition and the
            // then-branch, except against a nested `if` whose own
            // ", otherwise" would be read as this one's. The else-branch
            // runs to the end of the phrase, so an `else if` chain reads
            // naturally and needs no parentheses; the whole `if` is fenced
            // wherever it is itself an operand (see `cedar_operand`).
            let fence_if = |x: &Expr| {
                if matches!(x.kind, ExprKind::IfThenElse { .. }) {
                    cedar_operand(x, facts)
                } else {
                    cedar_expr(x, facts)
                }
            };
            Phrase::inline(
                "if {0} then {1}, otherwise {2}",
                vec![
                    fence_if(cond),
                    fence_if(then_expr),
                    cedar_expr(else_expr, facts),
                ],
                span,
            )
        }
        ExprKind::Set(elems) => {
            let children: Vec<Phrase> = elems.iter().map(|x| cedar_expr(x, facts)).collect();
            Phrase::inline(format!("[{}]", slots(children.len(), ", ")), children, span)
        }
        ExprKind::Record(entries) => {
            let mut template_parts = Vec::new();
            let mut children = Vec::new();
            for (i, (k, v)) in entries.iter().enumerate() {
                template_parts.push(format!("{}: {{{i}}}", esc(k)));
                children.push(cedar_expr(v, facts));
            }
            Phrase::inline(
                format!("{{{{ {} }}}}", template_parts.join(", ")),
                children,
                span,
            )
        }
        ExprKind::Call { name, args } => {
            // Post-expansion, a call is an information-provider invocation
            // (`Ns::Fn(args)`); its name is kept literally.
            let children: Vec<Phrase> = args.iter().map(|a| cedar_expr(a, facts)).collect();
            Phrase::inline(
                format!(
                    "{}({})",
                    esc(&name.to_string()),
                    slots(children.len(), ", ")
                ),
                children,
                span,
            )
        }
        ExprKind::MethodCall {
            receiver,
            method,
            args,
        } => {
            let mut children = vec![cedar_operand(receiver, facts)];
            children.extend(args.iter().map(|a| cedar_expr(a, facts)));
            let arg_slots: Vec<String> = (1..children.len()).map(|i| format!("{{{i}}}")).collect();
            Phrase::inline(
                format!(
                    "{{0}}.{}({})",
                    esc(&method.to_string()),
                    arg_slots.join(", ")
                ),
                children,
                span,
            )
        }
        ExprKind::ParamRef { name } => {
            panic!("informalize: unexpanded macro parameter `?{name}` in expression position")
        }
    }
}

/// An operand of an inline Cedar phrase (an operator, `.attr`, `has`, `like`,
/// `is`, a method receiver): the operand's phrase, parenthesized when the
/// operand is compound, so the prose can never be regrouped into a different
/// expression — `(a + 1) * 2` reads "(a + 1) * 2", not "a + 1 * 2". Leaves,
/// request paths, calls, sets and records are self-delimiting and stay bare.
/// Like [`crate::render`], this fences by shape rather than by precedence,
/// so a precedence mistake here is structurally impossible.
fn cedar_operand(e: &Expr, facts: &SchemaFacts) -> Phrase {
    let p = cedar_expr(e, facts);
    if is_compound(e) {
        Phrase::inline("({0})", vec![p], None)
    } else {
        p
    }
}

/// An operand of binary operator `op`. The one exception to fencing every
/// compound operand: arithmetic directly under a comparison stays bare
/// (`a + 1 <= 10`), which is unambiguous and matches how the temporal side
/// renders `Comparison` over `Arith` terms.
fn comparison_or_operand(op: BinOp, e: &Expr, facts: &SchemaFacts) -> Phrase {
    let is_cmp = matches!(
        op,
        BinOp::Eq | BinOp::NotEq | BinOp::Less | BinOp::LessEq | BinOp::Greater | BinOp::GreaterEq
    );
    let is_arith = matches!(
        e.kind,
        ExprKind::BinaryApp {
            op: BinOp::Add | BinOp::Sub | BinOp::Mul,
            ..
        }
    );
    if is_cmp && is_arith {
        cedar_expr(e, facts)
    } else {
        cedar_operand(e, facts)
    }
}

/// Whether `e`'s phrase has an operator or keyword at its top level that an
/// enclosing phrase could regroup. `-x` is atomic: it binds tighter than any
/// infix operator, and its own operand is fenced. So are the prefix noun
/// forms (`the decimal "0.5"`, `the date of x`): they open with their
/// keyword and end at their fenced operand. Postfix forms (`x is empty`,
/// `x in seconds`) are compound.
fn is_compound(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Lit(_)
        | ExprKind::Var(_)
        | ExprKind::Slot(_)
        | ExprKind::GetAttr { .. }
        | ExprKind::Set(_)
        | ExprKind::Record(_)
        | ExprKind::Call { .. }
        | ExprKind::MethodCall { .. }
        | ExprKind::UnaryApp {
            op:
                UnOp::Neg
                | UnOp::Decimal
                | UnOp::Datetime
                | UnOp::Duration
                | UnOp::Ip
                | UnOp::ToDate
                | UnOp::ToTime,
            ..
        } => false,
        ExprKind::UnaryApp { .. }
        | ExprKind::BinaryApp { .. }
        | ExprKind::HasAttr { .. }
        | ExprKind::Like { .. }
        | ExprKind::Is { .. }
        | ExprKind::IfThenElse { .. }
        | ExprKind::Extension(_) => true,
        ExprKind::ParamRef { name } => {
            panic!("informalize: unexpanded macro parameter `?{name}` in expression position")
        }
    }
}

/// `(x, b)` when one side of an equality is the boolean literal `b` and the
/// other is `x`.
fn bool_comparison<'a>(left: &'a Expr, right: &'a Expr) -> Option<(&'a Expr, bool)> {
    match (&left.kind, &right.kind) {
        (_, ExprKind::Lit(cedar_ast::Literal::Bool(b))) => Some((left, *b)),
        (ExprKind::Lit(cedar_ast::Literal::Bool(b)), _) => Some((right, *b)),
        _ => None,
    }
}

/// `{0}, {1}, …` — `n` slots joined by `sep`.
fn slots(n: usize, sep: &str) -> String {
    (0..n)
        .map(|i| format!("{{{i}}}"))
        .collect::<Vec<_>>()
        .join(sep)
}

fn literal_phrase(lit: &cedar_ast::Literal, facts: &SchemaFacts) -> String {
    match lit {
        cedar_ast::Literal::Bool(b) => b.to_string(),
        cedar_ast::Literal::Long(n) => n.to_string(),
        cedar_ast::Literal::String(s) => quote(s),
        cedar_ast::Literal::EntityUID(uid) => {
            uid_phrase(&uid.entity_type().to_string(), uid.eid().as_ref(), facts)
        }
    }
}

fn var_phrase(var: cedar_ast::Var) -> String {
    match var {
        cedar_ast::Var::Principal => "the principal".to_string(),
        cedar_ast::Var::Action => "the action".to_string(),
        cedar_ast::Var::Resource => "the resource".to_string(),
        cedar_ast::Var::Context => "the request context".to_string(),
    }
}

/// If `e` is a chain of attribute accesses rooted at a request variable
/// (`context.input.user`, `principal.dept`), the root and the attribute path.
fn var_path(e: &Expr) -> Option<(cedar_ast::Var, Vec<String>)> {
    let mut path = Vec::new();
    let mut cur = e;
    loop {
        match &cur.kind {
            ExprKind::GetAttr { expr, attr } => {
                path.push(attr.clone());
                cur = expr;
            }
            ExprKind::Var(v) => {
                path.reverse();
                return Some((*v, path));
            }
            _ => return None,
        }
    }
}

fn rooted_path_phrase(root: cedar_ast::Var, path: &[String]) -> String {
    match root {
        cedar_ast::Var::Context => context_path_phrase(path),
        cedar_ast::Var::Principal => scope_path_phrase_of("principal", path),
        cedar_ast::Var::Resource => scope_path_phrase_of("resource", path),
        cedar_ast::Var::Action => scope_path_phrase_of("action", path),
    }
}

/// `context.<path>` as a noun phrase: the default `input` group is dropped
/// ("the request's user"), any other group is kept as a word ("the request's
/// output balance", "the request's system now").
fn context_path_phrase(path: &[String]) -> String {
    match path {
        [] => "the request context".to_string(),
        [single] => format!("the request's {single}"),
        _ if let Some(name) = short_input_name(path) => format!("the request's {name}"),
        [group, rest @ ..] => format!("the request's {group} {}", rest.join(".")),
    }
}

/// `principal` / `principal.dept` (path *including* the root segment) as a
/// noun phrase.
fn scope_path_phrase(path_with_root: &[String]) -> String {
    match path_with_root.split_first() {
        Some((root, rest)) => scope_path_phrase_of(root, rest),
        None => String::new(),
    }
}

fn scope_path_phrase_of(root: &str, rest: &[String]) -> String {
    if rest.is_empty() {
        format!("the {root}")
    } else {
        format!("the {root}'s {}", rest.join("."))
    }
}

fn unary_template(op: UnOp) -> &'static str {
    match op {
        UnOp::Not => "not ({0})",
        UnOp::Neg => "-{0}",
        UnOp::IsEmpty => "{0} is empty",
        UnOp::Decimal => "the decimal {0}",
        UnOp::Datetime => "the datetime {0}",
        UnOp::Duration => "the duration {0}",
        UnOp::Ip => "the IP address {0}",
        UnOp::IsIpv4 => "{0} is an IPv4 address",
        UnOp::IsIpv6 => "{0} is an IPv6 address",
        UnOp::IsLoopback => "{0} is a loopback address",
        UnOp::IsMulticast => "{0} is a multicast address",
        UnOp::ToDate => "the date of {0}",
        UnOp::ToTime => "the time of day of {0}",
        UnOp::ToMilliseconds => "{0} in milliseconds",
        UnOp::ToSeconds => "{0} in seconds",
        UnOp::ToMinutes => "{0} in minutes",
        UnOp::ToHours => "{0} in hours",
        UnOp::ToDays => "{0} in days",
    }
}

fn binary_template(op: BinOp) -> &'static str {
    match op {
        BinOp::Eq => "{0} == {1}",
        BinOp::NotEq => "{0} != {1}",
        BinOp::Less => "{0} < {1}",
        BinOp::LessEq => "{0} <= {1}",
        BinOp::Greater => "{0} > {1}",
        BinOp::GreaterEq => "{0} >= {1}",
        BinOp::Add => "{0} + {1}",
        BinOp::Sub => "{0} - {1}",
        BinOp::Mul => "{0} * {1}",
        BinOp::In => "{0} is in {1}",
        BinOp::Contains => "{0} contains {1}",
        BinOp::ContainsAll => "{0} contains all of {1}",
        BinOp::ContainsAny => "{0} contains any of {1}",
        BinOp::GetTag => "the tag {1} of {0}",
        BinOp::HasTag => "{0} has the tag {1}",
        BinOp::IsInRange => "{0} is in the range {1}",
        BinOp::Offset => "{0} offset by {1}",
        BinOp::DurationSince => "the duration of {0} since {1}",
        BinOp::DecimalLessThan => "{0} is less than {1}",
        BinOp::DecimalLessEq => "{0} is at most {1}",
        BinOp::DecimalGreater => "{0} is greater than {1}",
        BinOp::DecimalGreaterEq => "{0} is at least {1}",
        BinOp::And | BinOp::Or => unreachable!("handled as block phrases"),
    }
}

// ─── Temporal conditions ────────────────────────────────────────────────

/// Which timepoint a temporal sub-condition is matched at: the current
/// (decision) event, or the past event a `formerly`/`previous`/`since` scans.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Scan {
    Current,
    Past,
}

/// Rebase a block-relative temporal span into the `.dw` source.
fn tsp(span: crate::error::Span, base: usize) -> Option<Span2> {
    Some((base + span.start, base + span.end))
}

fn temporal_condition(c: &tast::Condition, base: usize, scan: Scan, facts: &SchemaFacts) -> Phrase {
    use tast::ConditionKind as K;
    let span = tsp(c.span, base);
    match &c.kind {
        K::And { left, right } => {
            // `P && tp(t)`: the predicate matched at the timepoint bound to `t`.
            if let (K::Predicate(p), K::Tp { var }) = (&left.kind, &right.kind) {
                let noun = predicate_noun(p, base, facts, Article::Indefinite);
                let t = binder_name(var);
                let template = match scan {
                    Scan::Current => format!("the current event, at timepoint {t}, is {{0}}"),
                    Scan::Past => format!("the event at timepoint {t} is {{0}}"),
                };
                return Phrase::inline(template, vec![noun], span);
            }
            let l = temporal_condition(left, base, scan, facts);
            let r = temporal_condition(right, base, scan, facts);
            Phrase::block("{0} and {1}", vec![l, r], span)
        }
        K::Or { left, right } => {
            let l = temporal_condition(left, base, scan, facts);
            let r = temporal_condition(right, base, scan, facts);
            Phrase::block("{0} or {1}", vec![l, r], span)
        }
        K::Not { inner } => {
            let i = temporal_condition(inner, base, scan, facts);
            Phrase::inline("not ({0})", vec![i], span)
        }
        K::Formerly { within, body } => {
            let w = window_phrase(within);
            match &body.kind {
                K::Predicate(p) => {
                    let noun = predicate_noun(p, base, facts, Article::Indefinite);
                    Phrase::inline(
                        format!("{{0}} occurred within the last {w}"),
                        vec![noun],
                        span,
                    )
                }
                K::And { left, right }
                    if matches!((&left.kind, &right.kind), (K::Predicate(_), K::Tp { .. })) =>
                {
                    let K::Predicate(p) = &left.kind else {
                        unreachable!()
                    };
                    let K::Tp { var } = &right.kind else {
                        unreachable!()
                    };
                    let noun = predicate_noun(p, base, facts, Article::Indefinite);
                    Phrase::inline(
                        format!(
                            "{{0}} occurred at some timepoint {} within the last {w}",
                            binder_name(var)
                        ),
                        vec![noun],
                        span,
                    )
                }
                _ => {
                    let b = temporal_condition(body, base, Scan::Past, facts);
                    Phrase::hanging(
                        format!("within the last {w}, at some point: {{0}}"),
                        vec![b],
                        span,
                    )
                }
            }
        }
        K::Previous { within, body } => {
            let w = window_phrase(within);
            match &body.kind {
                K::Predicate(p) => {
                    let noun = predicate_noun(p, base, facts, Article::Indefinite);
                    Phrase::inline(
                        format!("the immediately preceding event, at most {w} ago, was {{0}}"),
                        vec![noun],
                        span,
                    )
                }
                _ => {
                    let b = temporal_condition(body, base, Scan::Past, facts);
                    Phrase::hanging(
                        format!(
                            "the immediately preceding event, at most {w} ago, satisfies: {{0}}"
                        ),
                        vec![b],
                        span,
                    )
                }
            }
        }
        K::Since {
            left,
            within,
            right,
        } => {
            let w = window_phrase(within);
            // Read in time order: first the anchor (the right operand, which
            // happened within the window), then what has (or has not) held
            // at every step since — "a Grant … occurred within the last 1
            // hour / and no Revoke … has occurred since then". Each row is a
            // complete statement, and the window attaches to the anchor it
            // bounds.
            let anchor = match &right.kind {
                K::Predicate(p) => {
                    let noun = predicate_noun(p, base, facts, Article::Indefinite);
                    Phrase::inline(
                        format!("{{0}} occurred within the last {w}"),
                        vec![noun],
                        tsp(right.span, base),
                    )
                }
                _ => {
                    let b = temporal_condition(right, base, Scan::Past, facts);
                    Phrase::hanging(
                        format!("at some point within the last {w}: {{0}}"),
                        vec![b],
                        tsp(right.span, base),
                    )
                }
            };
            let held = match &left.kind {
                // `!P since Q` — the "has not happened since" idiom.
                K::Not { inner } => match &inner.kind {
                    K::Predicate(p) => {
                        let same_as = since_back_ref(p, right);
                        let noun =
                            predicate_noun_with(p, base, facts, Article::None, same_as, None);
                        Phrase::inline(
                            "no {0} has occurred since then",
                            vec![noun],
                            tsp(left.span, base),
                        )
                    }
                    _ => {
                        let i = temporal_condition(inner, base, Scan::Past, facts);
                        Phrase::hanging("at no step since then: {0}", vec![i], tsp(left.span, base))
                    }
                },
                K::Predicate(p) => {
                    let same_as = since_back_ref(p, right);
                    let noun =
                        predicate_noun_with(p, base, facts, Article::Indefinite, same_as, None);
                    Phrase::inline(
                        "every event since then has been {0}",
                        vec![noun],
                        tsp(left.span, base),
                    )
                }
                _ => {
                    let l = temporal_condition(left, base, Scan::Past, facts);
                    Phrase::hanging(
                        "at every step since then: {0}",
                        vec![l],
                        tsp(left.span, base),
                    )
                }
            };
            Phrase::block("{0} and {1}", vec![anchor, held], span)
        }
        K::Predicate(p) => {
            let noun = predicate_noun(p, base, facts, Article::Indefinite);
            let template = match scan {
                Scan::Current => "the current event is {0}",
                Scan::Past => "the event is {0}",
            };
            Phrase::inline(template, vec![noun], span)
        }
        K::Comparison { op, left, right } => {
            // `(agg) == x` / `x == (agg)`: the binding equality reads "x = agg".
            if *op == tast::CmpOp::Eq {
                if let (tast::Term::Agg(agg), tast::Term::Var(v)) = (left, right) {
                    let a = agg_phrase(agg, base, scan, facts);
                    return Phrase::inline(format!("{} = {{0}}", binder_display(v)), vec![a], span);
                }
                if let (tast::Term::Var(v), tast::Term::Agg(agg)) = (left, right) {
                    let a = agg_phrase(agg, base, scan, facts);
                    return Phrase::inline(format!("{} = {{0}}", binder_display(v)), vec![a], span);
                }
            }
            // `x == true` / `x != false`: "x is true" / "x is not false".
            if matches!(op, tast::CmpOp::Eq | tast::CmpOp::NotEq) {
                let bool_side = match (left, right) {
                    (x, tast::Term::Bool(b)) | (tast::Term::Bool(b), x) => Some((x, *b)),
                    _ => None,
                };
                if let Some((x, b)) = bool_side {
                    let not = if *op == tast::CmpOp::NotEq {
                        "not "
                    } else {
                        ""
                    };
                    let x = cmp_operand_phrase(x, base, scan, facts);
                    return Phrase::inline(format!("{{0}} is {not}{b}"), vec![x], span);
                }
            }
            let l = cmp_operand_phrase(left, base, scan, facts);
            let r = cmp_operand_phrase(right, base, scan, facts);
            Phrase::inline(format!("{{0}} {} {{1}}", cmp_symbol(*op)), vec![l, r], span)
        }
        K::Exists { var, body } => {
            if let Some(phrase) = aggregate_binding_idiom(var, body, base, scan, facts, span) {
                return phrase;
            }
            if let Some(phrase) = field_filter_idiom(var, body, base, scan, facts, span) {
                return phrase;
            }
            let b = temporal_condition(body, base, scan, facts);
            // Named after the field it is bound to ("for some user u") when
            // every predicate field bound to it has the same name, else after
            // its type ("for some number n", "for some OAuthUser pr").
            let mut fields = BTreeSet::new();
            bound_fields(body, var.name(), &mut fields);
            let word = match fields.len() {
                // Not when the binder has the field's own name ("for some
                // user user").
                1 if !fields.contains(var.name()) => fields.into_iter().next().expect("one field"),
                _ => type_word(&var.ty, facts),
            };
            Phrase::hanging(
                format!("for some {} {}: {{0}}", esc(&word), binder_name(&var.slot)),
                vec![b],
                span,
            )
        }
        K::Tp { var } => {
            let t = binder_name(var);
            let text = match scan {
                Scan::Current => format!("the current timepoint is {t}"),
                Scan::Past => format!("that timepoint is {t}"),
            };
            Phrase::leaf(text, span)
        }

        K::Call(_) => panic!("informalize: unexpanded temporal macro call"),
        K::SigilRef { name, .. } => {
            panic!("informalize: unexpanded temporal sigil reference `{name}`")
        }
        K::Refine { .. } => panic!("informalize: temporal `Refine` is pre-expansion"),
    }
}

/// `exists (n: T). (agg == n && n op x)` (either side of each comparison;
/// the binding conjunct comes first, as the language requires), where `n` is
/// used nowhere else: `n` only names the
/// aggregate for one comparison, so this reads as that comparison, "agg op
/// x" — "the number of SellShares requests … within the last 1 hour <= 3".
/// A general-form aggregate is parenthesized (see [`agg_operand_phrase`]).
fn aggregate_binding_idiom(
    var: &tast::TypedBinder,
    body: &tast::Condition,
    base: usize,
    scan: Scan,
    facts: &SchemaFacts,
    span: Option<Span2>,
) -> Option<Phrase> {
    use tast::ConditionKind as K;
    use tast::Term as T;
    let n = var.name();
    let K::And { left, right } = &body.kind else {
        return None;
    };
    // The binding equality `agg == n` / `n == agg`.
    let binding = |c: &'_ tast::Condition| -> bool {
        matches!(&c.kind, K::Comparison { op: tast::CmpOp::Eq, left: l, right: r }
            if matches!((l, r), (T::Agg(_), T::Var(v)) | (T::Var(v), T::Agg(_)) if v == n))
    };
    if !binding(left) {
        return None;
    }
    let (bind, filter) = (left, right);
    let K::Comparison {
        left: bl,
        right: br,
        ..
    } = &bind.kind
    else {
        return None;
    };
    let agg = match (bl, br) {
        (T::Agg(a), _) | (_, T::Agg(a)) => a,
        _ => return None,
    };
    let K::Comparison {
        op,
        left: fl,
        right: fr,
    } = &filter.kind
    else {
        return None;
    };
    // `n op x` or `x op n`, with `n` nowhere in `x` or the aggregate.
    let (n_first, other) = match (fl, fr) {
        (T::Var(v), x) if v == n => (true, x),
        (x, T::Var(v)) if v == n => (false, x),
        _ => return None,
    };
    if term_uses(other, n) || agg_uses(agg, n) {
        return None;
    }
    let a = agg_operand_phrase(agg, base, scan, facts);
    let x = term_phrase(other, base, scan, facts);
    let template = format!("{{0}} {} {{1}}", cmp_symbol(*op));
    Some(if n_first {
        Phrase::inline(template, vec![a, x], span)
    } else {
        Phrase::inline(template, vec![x, a], span)
    })
}

thread_local! {
    /// Field filters folded into a predicate arg by [`field_filter_idiom`]:
    /// while its body is phrased, an arg whose value is one of these
    /// variables reads "f op x" instead of "f = v". Innermost last.
    static FIELD_FILTERS: std::cell::RefCell<Vec<(String, tast::CmpOp, Phrase)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// `exists (a: T). (L && a op x)` (or `x op a`), where `a` occurs in `L`
/// exactly once — as the value of one predicate arg `f: a`, reached only
/// through `&&`, `formerly`, `previous` and other `exists` — and not in `x`.
/// `a` then only carries that field's value to the comparison, so the
/// comparison moves into the event: "a Transfer request with amount > 100"
/// instead of "there is some number a such that / … amount = a … / and a >
/// 100". Exact: the event that binds `a` is the one whose field is compared.
fn field_filter_idiom(
    var: &tast::TypedBinder,
    body: &tast::Condition,
    base: usize,
    scan: Scan,
    facts: &SchemaFacts,
    span: Option<Span2>,
) -> Option<Phrase> {
    use tast::ConditionKind as K;
    use tast::Term as T;
    let a = var.name();
    let K::And { left, right } = &body.kind else {
        return None;
    };
    let K::Comparison {
        op,
        left: cl,
        right: cr,
    } = &right.kind
    else {
        return None;
    };
    let (op, x) = match (cl, cr) {
        (T::Var(v), x) if v == a => (*op, x),
        (x, T::Var(v)) if v == a => (flip_cmp(*op), x),
        _ => return None,
    };
    if term_uses(x, a) || arg_binding_uses(left, a) != Some(1) {
        return None;
    }
    // Phrased in the caller's scan, like the rest of the body: under a past
    // operator an aggregate operand reads "the event", not "the current
    // event".
    let x = cmp_operand_phrase(x, base, scan, facts);
    FIELD_FILTERS.with(|f| f.borrow_mut().push((a.to_string(), op, x)));
    // Popped on drop, so a panic while phrasing the body cannot leave the
    // filter active for a later call on the same thread.
    let _pop = OnDrop(Some(|| {
        FIELD_FILTERS.with(|f| f.borrow_mut().pop());
    }));
    let phrase = temporal_condition(left, base, scan, facts);
    Some(Phrase { span, ..phrase })
}

/// How often `name` is bound as a whole predicate-arg value (`f: name`) in
/// `c`, through `&&`, `formerly`, `previous` and non-shadowing `exists`
/// only; `None` if it occurs anywhere else (under a negation, in a
/// comparison, an aggregate, arithmetic, …).
fn arg_binding_uses(c: &tast::Condition, name: &str) -> Option<usize> {
    use tast::ConditionKind as K;
    match &c.kind {
        K::And { left, right } => {
            Some(arg_binding_uses(left, name)? + arg_binding_uses(right, name)?)
        }
        K::Formerly { body, .. } | K::Previous { body, .. } => arg_binding_uses(body, name),
        K::Exists { var, body } if var.name() != name => arg_binding_uses(body, name),
        K::Predicate(p) => {
            let mut n = 0;
            for arg in &p.args {
                match &arg.value {
                    tast::Term::Var(v) if v == name => n += 1,
                    other if term_uses(other, name) => return None,
                    _ => {}
                }
            }
            Some(n)
        }
        _ if cond_uses(c, name) => None,
        _ => Some(0),
    }
}

/// `x op y` ⇔ `y (flip op) x`.
fn flip_cmp(op: tast::CmpOp) -> tast::CmpOp {
    use tast::CmpOp as C;
    match op {
        C::Lt => C::Gt,
        C::Le => C::Ge,
        C::Gt => C::Lt,
        C::Ge => C::Le,
        C::Eq => C::Eq,
        C::NotEq => C::NotEq,
    }
}

/// The display names of every predicate field anywhere in `c` whose value
/// is the variable `name` (`input.user: u` → `user`), including inside
/// aggregates.
fn bound_fields(c: &tast::Condition, name: &str, out: &mut BTreeSet<String>) {
    use tast::ConditionKind as K;
    let in_term = |t: &tast::Term, out: &mut BTreeSet<String>| {
        if let tast::Term::Agg(agg) = t {
            // An aggregate that declares its own `name` shadows the outer one.
            let (for_vars, bound, body) = match &agg.kind {
                tast::AggExprKind::Count { for_vars, body } => (for_vars, None, body),
                tast::AggExprKind::Sum {
                    bound_var,
                    for_vars,
                    body,
                } => (for_vars, Some(bound_var), body),
                tast::AggExprKind::Call(_) => return,
            };
            let shadows = for_vars.iter().any(|b| b.name() == name)
                || bound.is_some_and(|b| b.name() == name);
            if !shadows {
                bound_fields(body, name, out);
            }
        }
    };
    match &c.kind {
        K::And { left, right } | K::Or { left, right } | K::Since { left, right, .. } => {
            bound_fields(left, name, out);
            bound_fields(right, name, out);
        }
        K::Not { inner } => bound_fields(inner, name, out),
        K::Formerly { body, .. } | K::Previous { body, .. } => bound_fields(body, name, out),
        K::Exists { var, body } if var.name() != name => bound_fields(body, name, out),
        K::Predicate(p) => {
            for arg in &p.args {
                if matches!(&arg.value, tast::Term::Var(v) if v == name) {
                    out.insert(field_display(&arg.field_path()));
                }
            }
        }
        K::Comparison { left, right, .. } => {
            in_term(left, out);
            in_term(right, out);
        }
        _ => {}
    }
}

/// Whether the variable `name` occurs anywhere in `t`.
fn term_uses(t: &tast::Term, name: &str) -> bool {
    use tast::Term as T;
    match t {
        T::Var(v) => v == name,
        T::Array(items) => items.iter().any(|i| term_uses(i, name)),
        T::Arith { left, right, .. } => term_uses(left, name) || term_uses(right, name),
        T::Agg(agg) => agg_uses(agg, name),
        _ => false,
    }
}

/// Whether the variable `name` occurs anywhere in `agg` (conservatively,
/// including as one of its own binders).
fn agg_uses(agg: &tast::AggExpr, name: &str) -> bool {
    use tast::AggExprKind as A;
    match &agg.kind {
        A::Count { for_vars, body } => {
            for_vars.iter().any(|b| b.name() == name) || cond_uses(body, name)
        }
        A::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            bound_var.name() == name
                || for_vars.iter().any(|b| b.name() == name)
                || cond_uses(body, name)
        }
        A::Call(_) => true,
    }
}

/// Whether the variable `name` occurs anywhere in `c` (conservatively,
/// including as a binder).
fn cond_uses(c: &tast::Condition, name: &str) -> bool {
    use tast::ConditionKind as K;
    match &c.kind {
        K::And { left, right } | K::Or { left, right } => {
            cond_uses(left, name) || cond_uses(right, name)
        }
        K::Since { left, right, .. } => cond_uses(left, name) || cond_uses(right, name),
        K::Not { inner } => cond_uses(inner, name),
        K::Formerly { body, .. } | K::Previous { body, .. } => cond_uses(body, name),
        K::Predicate(p) => p.args.iter().any(|a| term_uses(&a.value, name)),
        K::Comparison { left, right, .. } => term_uses(left, name) || term_uses(right, name),
        K::Exists { var, body } => var.name() == name || cond_uses(body, name),
        K::Tp { var } => var.name() == name,
        K::Call(_) | K::SigilRef { .. } | K::Refine { .. } => true,
    }
}

/// "a Login request with user = …, output result = true" — the predicate as a
/// noun phrase. Args are children in source order.
fn predicate_noun(
    p: &tast::Predicate,
    base: usize,
    facts: &SchemaFacts,
    article: Article,
) -> Phrase {
    predicate_noun_with(p, base, facts, article, SameAs::ThisRequest, None)
}

/// How a predicate's "same as the request" fields are phrased: "with this
/// request's user and stock", or — when an earlier row already stated that
/// set — the back-reference "for that user and stock".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SameAs {
    ThisRequest,
    That,
}

/// [`predicate_noun`] with an explicit [`SameAs`]. All of the predicate's
/// same-as-the-request fields are merged into one phrase, placed where the
/// first of them appears ("with this request's user and stock and output
/// approved = true"); the other args keep their order.
///
/// `skip` leaves out the arg at that index — one whose field an enclosing
/// phrase already names ("the total amount of Transfer requests").
fn predicate_noun_with(
    p: &tast::Predicate,
    base: usize,
    facts: &SchemaFacts,
    article: Article,
    same_as: SameAs,
    skip: Option<usize>,
) -> Phrase {
    let head = predicate_head(p, facts);
    let kind = kind_word(&p.kind);
    let mut lead = match article {
        Article::Indefinite => format!("{} {head} {kind}", article_for(&head)),
        Article::None => format!("{head} {kind}"),
        Article::Plural => format!("{head} {}", kind_plural(&p.kind)),
    };
    let same = same_as_fields(p);
    if same_as == SameAs::That && !same.is_empty() {
        lead.push_str(&format!(" for that {}", join_and(&same)));
    }
    let lead = esc(&lead);

    let mut children: Vec<Phrase> = Vec::new();
    let mut merged_placed = false;
    for (i, arg) in p.args.iter().enumerate() {
        if skip == Some(i) {
            continue;
        }
        if is_same_as_request(arg) {
            if !merged_placed && same_as == SameAs::ThisRequest {
                children.push(Phrase::leaf(
                    format!("this request's {}", join_and(&same)),
                    None,
                ));
            }
            merged_placed = true;
        } else {
            children.push(named_arg_phrase(arg, base, facts));
        }
    }
    if children.is_empty() {
        // `lead` is already escaped; `leaf` would escape it twice.
        return Phrase::inline(lead, Vec::new(), tsp(p.span, base));
    }
    Phrase::inline(
        format!("{lead} with {}", slots(children.len(), " and ")),
        children,
        tsp(p.span, base),
    )
}

/// Whether `arg` compares the event's field with the request's field at the
/// same path (`input.user: context.input.user`).
fn is_same_as_request(arg: &tast::NamedArg) -> bool {
    matches!(&arg.value, tast::Term::ContextField(ctx) if *ctx == arg.field_path())
}

/// The display names of `p`'s same-as-the-request fields, in source order.
fn same_as_fields(p: &tast::Predicate) -> Vec<String> {
    p.args
        .iter()
        .filter(|a| is_same_as_request(a))
        .map(|a| field_display(&a.field_path()))
        .collect()
}

/// `a`, `a and b`, `a, b, and c`.
fn join_and(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [one] => one.clone(),
        [a, b] => format!("{a} and {b}"),
        [init @ .., last] => format!("{}, and {last}", init.join(", ")),
    }
}

/// For a `since` whose left predicate `p` compares exactly the same fields
/// with the request as its anchor `right` (a predicate), the left row refers
/// back ("for that user and resource") instead of repeating "with this
/// request's …".
fn since_back_ref(p: &tast::Predicate, right: &tast::Condition) -> SameAs {
    let tast::ConditionKind::Predicate(anchor) = &right.kind else {
        return SameAs::ThisRequest;
    };
    // Compared by full field path, not display name: `input.user` and a
    // top-level `user` are different fields that may display alike.
    let paths = |q: &tast::Predicate| -> BTreeSet<Vec<String>> {
        q.args
            .iter()
            .filter(|a| is_same_as_request(a))
            .map(|a| a.field_path())
            .collect()
    };
    let mine = paths(p);
    if !mine.is_empty() && mine == paths(anchor) {
        SameAs::That
    } else {
        SameAs::ThisRequest
    }
}

/// Whether a predicate noun phrase carries its indefinite article ("a Login
/// request"), none ("no Login request …"), or is plural ("the number of
/// Login requests …").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Article {
    Indefinite,
    None,
    Plural,
}

/// The plural of [`kind_word`]: `requests`, `responses`, `errors`, or
/// "`<kind>` events".
fn kind_plural(kind: &str) -> String {
    match kind {
        "request" | "response" | "error" => format!("{kind}s"),
        other => format!("{other} events"),
    }
}

/// The action part of a predicate head: `Drupe::Action::"Login"` → `Login`
/// when the namespace is droppable, else the full spelling.
fn predicate_head(p: &tast::Predicate, facts: &SchemaFacts) -> String {
    let qualified_type = p.namespace.join("::");
    uid_phrase(&qualified_type, &p.action, facts)
}

/// `request` / `response` / `error` are words; any other kind reads as
/// "`<kind>` event".
fn kind_word(kind: &str) -> String {
    match kind {
        "request" | "response" | "error" => kind.to_string(),
        other => format!("{other} event"),
    }
}

fn article_for(word: &str) -> &'static str {
    match word.chars().next() {
        Some(c) if "AEIOUaeiou".contains(c) => "an",
        _ => "a",
    }
}

/// One predicate arg (other than a same-as-the-request field, which
/// [`predicate_noun_with`] merges). The field's `input.` group is dropped;
/// `output.` is kept as a word; other (injected) fields keep their name. A
/// wildcard reads "any f".
fn named_arg_phrase(arg: &tast::NamedArg, base: usize, facts: &SchemaFacts) -> Phrase {
    let path = arg.field_path();
    let field = field_display(&path);
    match &arg.value {
        tast::Term::Wildcard => Phrase::leaf(format!("any {field}"), None),
        // A variable whose comparison `field_filter_idiom` folded in here.
        tast::Term::Var(v)
            if let Some((op, x)) = FIELD_FILTERS.with(|f| {
                f.borrow()
                    .iter()
                    .rev()
                    .find(|(name, _, _)| name == v)
                    .map(|(_, op, x)| (*op, x.clone()))
            }) =>
        {
            // A folded equality reads like a field value written directly
            // in the predicate ("ok = true", not "ok == true").
            let symbol = if op == tast::CmpOp::Eq {
                "="
            } else {
                cmp_symbol(op)
            };
            Phrase::inline(format!("{} {symbol} {{0}}", esc(&field)), vec![x], None)
        }
        value => {
            let v = term_phrase(value, base, Scan::Current, facts);
            Phrase::inline(format!("{} = {{0}}", esc(&field)), vec![v], None)
        }
    }
}

fn field_display(path: &[String]) -> String {
    if let Some(name) = short_input_name(path) {
        return name;
    }
    match path {
        [group, rest @ ..] if (group == "output" || group == "input") && !rest.is_empty() => {
            format!("{group} {}", rest.join("."))
        }
        _ => path.join("."),
    }
}

fn term_phrase(t: &tast::Term, base: usize, scan: Scan, facts: &SchemaFacts) -> Phrase {
    use tast::Term as T;
    match t {
        T::Entity { ty, id } => Phrase::leaf(uid_phrase(ty, id, facts), None),
        T::Integer(n) => Phrase::leaf(n.to_string(), None),
        T::Decimal(s) => Phrase::leaf(format!("decimal({})", quote(s)), None),
        T::String(s) => Phrase::leaf(quote(s), None),
        T::Bool(b) => Phrase::leaf(b.to_string(), None),
        T::ContextField(path) => Phrase::leaf(context_path_phrase(path), None),
        T::ScopeField(path) => Phrase::leaf(scope_path_phrase(path), None),
        T::Var(v) => Phrase::leaf(binder_display(v), None),
        T::Wildcard => Phrase::leaf("any value", None),
        T::Array(items) => {
            let children: Vec<Phrase> = items
                .iter()
                .map(|i| term_phrase(i, base, scan, facts))
                .collect();
            Phrase::inline(format!("[{}]", slots(children.len(), ", ")), children, None)
        }
        T::Agg(agg) => agg_phrase(agg, base, scan, facts),
        // Arithmetic keeps its operator symbol; a nested arithmetic or
        // aggregate operand is parenthesized, as in `render.rs`.
        T::Arith { op, left, right } => {
            let l = arith_operand_phrase(left, base, scan, facts);
            let r = arith_operand_phrase(right, base, scan, facts);
            Phrase::inline(format!("{{0}} {} {{1}}", op.token()), vec![l, r], None)
        }
        T::ParamRef(p) => panic!("informalize: unexpanded macro parameter `?{p}` in term position"),
        T::BinderRef(b) => panic!("informalize: unexpanded macro binder `${b}` in term position"),
    }
}

/// A comparison operand; an aggregate is fenced as in [`agg_operand_phrase`].
fn cmp_operand_phrase(t: &tast::Term, base: usize, scan: Scan, facts: &SchemaFacts) -> Phrase {
    match t {
        tast::Term::Agg(agg) => agg_operand_phrase(agg, base, scan, facts),
        _ => term_phrase(t, base, scan, facts),
    }
}

/// An aggregate as an operand. A phrase that ends in a noun phrase ("the
/// number of P within the last W", "the total f of P within the last W")
/// stays bare. One that ends in a clause is parenthesized, so what follows
/// cannot attach to that clause: the general form ("… and that timepoint is
/// t") and the current-event count ("…, counting only this request itself").
fn agg_operand_phrase(agg: &tast::AggExpr, base: usize, scan: Scan, facts: &SchemaFacts) -> Phrase {
    let a = agg_phrase(agg, base, scan, facts);
    if agg_idiom(agg, base, scan, facts).is_some() && !is_current_event_count(agg) {
        a
    } else {
        Phrase::inline("({0})", vec![a], None)
    }
}

/// Whether `agg` is `count for (t: Timepoint). where (P && tp(t))` with no
/// past operator: the shape [`agg_idiom`] reads as "the number of P,
/// counting only this request itself".
fn is_current_event_count(agg: &tast::AggExpr) -> bool {
    match &agg.kind {
        tast::AggExprKind::Count { for_vars, body } => match for_vars.as_slice() {
            [t] => t.ty == tast::Type::Timepoint && tagged_predicate(body, t.name()).is_some(),
            _ => false,
        },
        _ => false,
    }
}

/// An arithmetic operand; a nested `Arith` or `Agg` is parenthesized.
fn arith_operand_phrase(t: &tast::Term, base: usize, scan: Scan, facts: &SchemaFacts) -> Phrase {
    match t {
        tast::Term::Arith { .. } | tast::Term::Agg(_) => {
            let inner = term_phrase(t, base, scan, facts);
            Phrase::inline("({0})", vec![inner], None)
        }
        _ => term_phrase(t, base, scan, facts),
    }
}

fn agg_phrase(agg: &tast::AggExpr, base: usize, scan: Scan, facts: &SchemaFacts) -> Phrase {
    use tast::AggExprKind as A;
    let span = tsp(agg.span, base);
    if let Some(phrase) = agg_idiom(agg, base, scan, facts) {
        return phrase;
    }
    match &agg.kind {
        A::Count { for_vars, body } => {
            let b = temporal_condition(body, base, scan, facts);
            let template = match for_vars.as_slice() {
                [single] if single.ty == tast::Type::Timepoint => {
                    format!(
                        "the number of timepoints {} at which {{0}}",
                        binder_name(&single.slot)
                    )
                }
                [single] => format!(
                    "the number of distinct values {} for which {{0}}",
                    binder_name(&single.slot)
                ),
                many => format!(
                    "the number of distinct ({}) for which {{0}}",
                    binder_list(many)
                ),
            };
            Phrase::inline(template, vec![b], span)
        }
        A::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            let b = temporal_condition(body, base, scan, facts);
            let domain = match for_vars.as_slice() {
                [single] => format!("values {}", binder_name(&single.slot)),
                many => format!("({})", binder_list(many)),
            };
            Phrase::inline(
                format!(
                    "the sum of {} over the distinct {domain} for which {{0}}",
                    binder_name(bound_var)
                ),
                vec![b],
                span,
            )
        }
        A::Call(_) => panic!("informalize: unexpanded aggregation macro call"),
    }
}

/// The common aggregate shapes over a timepoint binder `t`, where `t` only
/// makes each event count once, phrased without it:
///
/// * `count for (t: Timepoint). where formerly within W (P && tp(t))` —
///   "the number of P within the last W";
/// * `sum a for (a: T), (t: Timepoint). where formerly within W (P{f: a} &&
///   tp(t))`, with `a` used only as `f` — "the total f of P within the last
///   W" (exact because `t` keeps one row per event, so equal values are not
///   deduplicated);
/// * `count for (t: Timepoint). where (P && tp(t))` — the body has no past
///   operator, so it is matched at the event being evaluated only: "the
///   number of P, counting only this request itself" ("that event" under a
///   past operator).
///
/// Any other shape returns `None` and keeps the general phrasing.
fn agg_idiom(agg: &tast::AggExpr, base: usize, scan: Scan, facts: &SchemaFacts) -> Option<Phrase> {
    use tast::AggExprKind as A;
    let span = tsp(agg.span, base);

    let timepoint = |b: &tast::TypedBinder| b.ty == tast::Type::Timepoint;

    match &agg.kind {
        A::Count { for_vars, body } => {
            let [t] = for_vars.as_slice() else {
                return None;
            };
            if !timepoint(t) {
                return None;
            }
            if let Some((w, p)) = windowed_tagged(body, t.name()) {
                let noun =
                    predicate_noun_with(p, base, facts, Article::Plural, SameAs::ThisRequest, None);
                return Some(Phrase::inline(
                    format!("the number of {{0}} within the last {w}"),
                    vec![noun],
                    span,
                ));
            }
            let p = tagged_predicate(body, t.name())?;
            let noun =
                predicate_noun_with(p, base, facts, Article::Plural, SameAs::ThisRequest, None);
            let at = match scan {
                Scan::Current => "counting only this request itself",
                Scan::Past => "counting only that event itself",
            };
            Some(Phrase::inline(
                format!("the number of {{0}}, {at}"),
                vec![noun],
                span,
            ))
        }
        A::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            let a = bound_var.name();
            let [x, y] = for_vars.as_slice() else {
                return None;
            };
            let t = match (x.name() == a, y.name() == a) {
                (true, false) if timepoint(y) => y,
                (false, true) if timepoint(x) => x,
                _ => return None,
            };
            let (w, p) = windowed_tagged(body, t.name())?;
            // `a` bound by exactly one arg, and used nowhere else in P (not
            // inside another arg's array or arithmetic either, which would
            // print `a` without introducing it).
            let uses: Vec<usize> = p
                .args
                .iter()
                .enumerate()
                .filter(|(_, arg)| matches!(&arg.value, tast::Term::Var(v) if v == a))
                .map(|(i, _)| i)
                .collect();
            let [i] = uses.as_slice() else {
                return None;
            };
            if p.args
                .iter()
                .enumerate()
                .any(|(j, arg)| j != *i && term_uses(&arg.value, a))
            {
                return None;
            }
            let field = field_display(&p.args[*i].field_path());
            let noun = predicate_noun_with(
                p,
                base,
                facts,
                Article::Plural,
                SameAs::ThisRequest,
                Some(*i),
            );
            Some(Phrase::inline(
                format!("the total {} of {{0}} within the last {w}", esc(&field)),
                vec![noun],
                span,
            ))
        }
        A::Call(_) => None,
    }
}

/// `P && tp(t)`, with `t` not used by P itself: the predicate P.
fn tagged_predicate<'a>(c: &'a tast::Condition, t: &str) -> Option<&'a tast::Predicate> {
    use tast::ConditionKind as K;
    let K::And { left, right } = &c.kind else {
        return None;
    };
    let (K::Predicate(p), K::Tp { var }) = (&left.kind, &right.kind) else {
        return None;
    };
    let uses_t = p.args.iter().any(|a| term_uses(&a.value, t));
    (var.name() == t && !uses_t).then_some(p)
}

/// `formerly within W (P && tp(t))`: the window phrase and P.
fn windowed_tagged<'a>(c: &'a tast::Condition, t: &str) -> Option<(String, &'a tast::Predicate)> {
    let tast::ConditionKind::Formerly { within, body } = &c.kind else {
        return None;
    };
    Some((window_phrase(within), tagged_predicate(body, t)?))
}

fn binder_list(binders: &[tast::TypedBinder]) -> String {
    binders
        .iter()
        .map(|b| binder_name(&b.slot))
        .collect::<Vec<_>>()
        .join(", ")
}

fn binder_name(slot: &tast::BinderSlot) -> String {
    match slot {
        tast::BinderSlot::Name(s) => binder_display(s),
        tast::BinderSlot::ParamRef(p) => {
            panic!("informalize: unexpanded macro parameter `?{p}` in binder position")
        }
        tast::BinderSlot::BinderRef(b) => {
            panic!("informalize: unexpanded macro binder `${b}` in binder position")
        }
    }
}

/// The English word for a binder's type: Cedar primitives get a word,
/// entity types stay literal (namespace rule applied).
fn type_word(ty: &tast::Type, facts: &SchemaFacts) -> String {
    match ty {
        tast::Type::Timepoint => "timepoint".to_string(),
        tast::Type::Named(path) => match path.join("::").as_str() {
            "Long" => "number".to_string(),
            "String" => "string".to_string(),
            "Bool" => "boolean".to_string(),
            "Decimal" => "decimal".to_string(),
            other => facts.strip_ns(other),
        },
    }
}

fn window_phrase(w: &tast::WithinSpec) -> String {
    match w {
        tast::WithinSpec::Concrete(i) => interval_phrase(*i),
        tast::WithinSpec::ParamRef(p) => {
            panic!("informalize: unexpanded window parameter `?{p}`")
        }
    }
}

fn interval_phrase(i: tast::Interval) -> String {
    let unit = match i.unit {
        tast::TimeUnit::Seconds => "second",
        tast::TimeUnit::Minutes => "minute",
        tast::TimeUnit::Hours => "hour",
        tast::TimeUnit::Days => "day",
    };
    if i.amount == 1 {
        format!("1 {unit}")
    } else {
        format!("{} {unit}s", i.amount)
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
