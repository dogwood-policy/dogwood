//! The Dogwood surface AST.
//!
//! The AST mirrors the grammar. A [`PolicySet`] is a sequence of
//! [`Policy`] rules; each rule has annotations, an effect
//! (`permit`/`forbid`), a Cedar-shaped [`Scope`], and a list of
//! condition clauses ([`Cond`]).
//!
//! Each condition clause is a `when`/`unless` block whose body is an
//! [`Expr`] — a structured Cedar expression tree. [`Expr`] duplicates
//! Cedar's expression *structure* (the recursive spine: `&&`, `||`,
//! comparisons, attribute access, `if/then/else`, sets, records, …) but
//! adds one variant Cedar has no analogue for: [`Expr::Extension`], the
//! hole that carries a `temporal { … }` / `provider { … }` marker. Cedar's
//! own expression trees cannot carry such a hole, which is why we mirror the
//! structure rather than reuse a Cedar expression type directly.
//!
//! Where a node is *not* recursive into [`Expr`] (literals, variables,
//! pattern elements, entity types) we reuse Cedar's `cedar_policy_core::ast`
//! leaf types verbatim; operators are the exception — those use Dogwood's own
//! surface [`BinOp`] / [`UnOp`] enums (see [`ExprKind`] for why). So the spine
//! and operators are ours (transformable, hold the hole) while the value
//! leaves are Cedar's, and lowering (`crate::cedarify`) is near-identity on
//! those leaves.
//!
//! Every [`Expr`] carries a `span` (source byte range); `cedarify` reads it to
//! stamp a `.dw` source location onto each lowered `ast` node, so a Cedar
//! diagnostic points back at the precise sub-expression. Some *other* nodes
//! carry a `span` not yet read by any consumer — retained for future error
//! reporting — hence the module-level `allow(dead_code)`.
#![allow(dead_code)]

use std::collections::BTreeMap;

use cedar_policy_core::ast as cedar_ast;

use crate::error::Span;
use crate::extension::Extension;

/// A parsed Dogwood policy set: the whole `.dw` source.
#[derive(Debug, Clone)]
pub struct PolicySet {
    pub policies: Vec<Policy>,
    /// Top-level `def cedar` / `def temporal` macro declarations.
    /// The macro expansion pass consumes these and substitutes calls in
    /// the policies; post-expansion this list is no longer needed.
    pub defs: Vec<MacroDef>,
}

/// A macro definition: `def <kind> <name>(<params>) { <body> } ;`. The
/// `kind` selects the body parser (cedar vs. temporal); the body shape
/// records which language it parsed under.
#[derive(Debug, Clone)]
pub struct MacroDef {
    pub span: Span,
    pub name: String,
    pub params: Vec<MacroParam>,
    pub body: MacroBody,
}

/// One parameter slot in a macro definition. Macro parameters are
/// always `?`-style (value parameters); a body's local fresh binders
/// (`$t`) are introduced inline and not declared in the param list.
#[derive(Debug, Clone)]
pub struct MacroParam {
    pub span: Span,
    pub name: String,
}

/// The body of a macro definition, parsed under the appropriate
/// sub-language. The variant tags the syntactic category — at call
/// sites the demanded category dictates kind-compatibility (a cedar
/// macro is callable only in cedar-expression position; a
/// temporal-condition macro only in condition slot; an aggregation
/// macro only in `let r = <agg> in BODY`'s value slot).
#[derive(Debug, Clone)]
pub enum MacroBody {
    Cedar(Expr),
    TemporalCondition(crate::extension::temporal::ast::Condition),
    TemporalAgg(crate::extension::temporal::ast::AggExpr),
}

/// Permit or forbid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Effect {
    Permit,
    Forbid,
}

/// A single Dogwood rule.
#[derive(Debug, Clone)]
pub struct Policy {
    pub span: Span,
    /// `@id("...")`-style annotations, as `(key, value)` pairs.
    pub annotations: Vec<Annotation>,
    pub effect: Effect,
    /// The policy head (`principal, action, resource` with optional
    /// constraints), structured into `cedar_ast` scope constraints — see
    /// [`Scope`].
    pub scope: Scope,
    pub conditions: Vec<Cond>,
}

/// One `@key("value")` annotation.
#[derive(Debug, Clone)]
pub struct Annotation {
    pub key: String,
    pub value: Option<String>,
}

/// A policy scope (`principal, action, resource` with optional
/// constraints), structured into the three `cedar_ast` scope-constraint
/// types.
///
/// Like the condition body, the scope is structured rather than verbatim
/// text: `cedarify` assembles the policy head directly from these
/// constraints, and the rule's scoped action (needed to type hoisted
/// extension fields) is read off `action` rather than re-parsed from text.
///
/// The constraints are `cedar_ast` (not `pst`) so their entity UIDs carry a
/// `.dw` source `Loc`: Cedar's RBAC validator reports scope errors
/// (`UnrecognizedEntityType` / `UnrecognizedActionId` /
/// `InvalidActionApplication`) against the euid's own location, so a
/// mistyped scope action/type points at that token in the `.dw` source
/// rather than the whole rule.
#[derive(Debug, Clone)]
pub struct Scope {
    pub span: Span,
    pub principal: cedar_ast::PrincipalConstraint,
    pub action: cedar_ast::ActionConstraint,
    pub resource: cedar_ast::ResourceConstraint,
}

/// A `when`/`unless` condition clause: a keyword and a structured body.
#[derive(Debug, Clone)]
pub struct Cond {
    pub span: Span,
    pub keyword: CondKeyword,
    /// The clause body — a Cedar expression tree, possibly containing
    /// [`Expr::Extension`] leaves. A clause that is a single bare marker
    /// block (`when temporal { … }`) parses to a top-level
    /// [`Expr::Extension`].
    pub body: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CondKeyword {
    When,
    Unless,
}

/// A Cedar condition expression, with an extension hole.
///
/// Every node carries its originating `.dw` source [`Span`] alongside its
/// [`ExprKind`]. The span is what lets `cedarify` stamp a
/// `cedar_policy_core::ast` source location onto each lowered node, so a
/// Cedar validation diagnostic points back at the precise sub-expression
/// in the `.dw` source (not merely the enclosing rule). This wrapper shape
/// mirrors the temporal sub-language's `Condition { span, kind }`.
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    /// Byte range into the original `.dw` source that this node spans.
    pub span: Span,
}

impl Expr {
    /// Build an [`Expr`] node from its [`ExprKind`] and `.dw` [`Span`].
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Expr { kind, span }
    }
}

/// The shape of a Cedar condition expression node.
///
/// This is Dogwood's **surface** expression tree — it preserves what the
/// user wrote (surface operators like `!=` / `>` and extension *methods*
/// like `.lessThan(…)`), mirroring the role Cedar's own CST plays. The leaf
/// *value* payloads (literals, vars, slots, entity types, patterns) reuse
/// `cedar_policy_core::ast` types directly, since those have no surface-vs-
/// evaluation distinction. The *operators*, however, use Dogwood's own
/// [`BinOp`] / [`UnOp`] enums rather than an `ast` op type: `ast`'s op enums
/// are the *desugared* set (no `!=`/`>`, extension methods modeled as
/// `ExtensionFunctionApp`), so they cannot represent surface syntax. The
/// `cedarify` lowering (`to_ast`) desugars these surface ops into `ast` via
/// Cedar's `ExprBuilder` — the same primitive Cedar's `cst_to_ast` uses —
/// so the desugaring lives in one lowering pass, not the parser.
///
/// [`ExprKind::Extension`] is the one variant with no `ast` analogue — it
/// carries a parsed `temporal`/`provider` marker, which `cedarify` hoists to
/// a `context.<name>` reference before lowering.
#[derive(Debug, Clone)]
pub enum ExprKind {
    /// A literal: `true`, `42`, `"hi"`, `User::"alice"`.
    Lit(cedar_ast::Literal),
    /// A built-in variable: `principal` / `action` / `resource` /
    /// `context`.
    Var(cedar_ast::Var),
    /// A template slot: `?principal` / `?resource`.
    Slot(cedar_ast::SlotId),
    /// An extension marker block — the hole Cedar's expression AST lacks.
    Extension(Extension),

    /// A unary application: `!e`, `-e`, `decimal("…")`, `e.isEmpty()`, …
    /// The [`UnOp`] tag covers the boolean/arith negations, the extension
    /// constructors (`decimal`/`datetime`/`duration`/`ip`), and the
    /// zero-argument extension *methods* (`isEmpty`, `isIpv4`, `toDate`, …).
    UnaryApp { op: UnOp, expr: Box<Expr> },
    /// A binary application: `l < r`, `l && r`, `l.contains(r)`,
    /// `l.lessThan(r)`, … The [`BinOp`] tag covers the comparison/boolean/
    /// arith operators and the one-argument extension methods.
    BinaryApp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    /// Attribute access: `e.attr`.
    GetAttr { expr: Box<Expr>, attr: String },
    /// Attribute existence: `e has a` / `e has a.b.c` (non-empty path).
    HasAttr { expr: Box<Expr>, attrs: Vec<String> },
    /// Pattern match: `e like "*.jpg"`.
    Like {
        expr: Box<Expr>,
        pattern: Vec<cedar_ast::PatternElem>,
    },
    /// Entity-type test: `e is User` / `e is User in g`.
    Is {
        expr: Box<Expr>,
        entity_type: cedar_ast::EntityType,
        in_expr: Option<Box<Expr>>,
    },
    /// Conditional: `if c then t else f`.
    IfThenElse {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    /// Set literal: `[a, b, c]`.
    Set(Vec<Expr>),
    /// Record literal: `{ k1: v1, k2: v2 }`.
    Record(BTreeMap<String, Expr>),

    /// An unresolved function-shape call (`name(arg1, arg2, …)`) that
    /// the parser could not match against a Cedar built-in. The macro
    /// expansion pass resolves it: a name registered as a `def cedar`
    /// macro is substituted with its body; otherwise the call is
    /// rejected. Never reaches lowering. (The call's source span lives on
    /// the enclosing [`Expr`].)
    Call { name: String, args: Vec<Expr> },
    /// A method call the parser could not match against a Cedar built-in
    /// method (`isEmpty`, `contains`, `lessThan`, …): `receiver.name(args…)`.
    /// The built-in methods are desugared to [`UnOp`] / [`BinOp`] at parse
    /// time; a name outside that fixed set is *not* an error here, because
    /// it may be a **provider output method** (`Ns::Fn(x).classify()`,
    /// `.maxConfidenceScore()`) whose validity can only be judged once the
    /// provider declarations are known. So the parser defers it as this
    /// node and lowering (`crate::cedarify`) resolves it: if the chain's
    /// base is a declared information provider, the method chain is hoisted
    /// and evaluated out of band; otherwise lowering rejects it as an
    /// unknown method. (The call's source span lives on the enclosing
    /// [`Expr`].)
    MethodCall {
        receiver: Box<Expr>,
        method: String,
        args: Vec<Expr>,
    },
    /// `?p` macro parameter reference. Cedar already lexes `?<ident>` as
    /// a template slot ([`ExprKind::Slot`]); inside the body of a `def cedar`
    /// macro, the registry-building pass rewrites slot references that
    /// match a declared parameter into this variant so the expander can
    /// substitute them. Outside a macro body the variant is never
    /// produced; downstream lowering rejects it.
    ParamRef { name: String },
}

/// Dogwood's **surface** binary operators — what the user writes, before
/// Cedar's desugaring. Covers the core relational/boolean/arithmetic
/// operators (including `!=` / `>` / `>=`, which Cedar's evaluation AST
/// lacks), the set/entity/tag operators, and the one-argument extension
/// *methods* (decimal comparisons, `isInRange`, `offset`, `durationSince`).
/// `cedarify::to_ast` maps each to the matching `ExprBuilder` method, which
/// performs Cedar's desugaring.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Core operators.
    Eq,
    NotEq,
    Less,
    LessEq,
    Greater,
    GreaterEq,
    And,
    Or,
    Add,
    Sub,
    Mul,
    In,
    // Set / entity / tag operators (method syntax, native Cedar ops).
    Contains,
    ContainsAll,
    ContainsAny,
    GetTag,
    HasTag,
    // One-argument extension methods (lowered to `ExtensionFunctionApp`).
    IsInRange,
    Offset,
    DurationSince,
    DecimalLessThan,
    DecimalLessEq,
    DecimalGreater,
    DecimalGreaterEq,
}

/// Dogwood's **surface** unary operators. Covers boolean/arithmetic negation
/// and `isEmpty`, the extension *constructors* (`decimal`/`datetime`/
/// `duration`/`ip`), and the zero-argument extension *methods* (IP tests,
/// datetime accessors). `cedarify::to_ast` maps each to the matching
/// `ExprBuilder` method or `ExtensionFunctionApp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    // Core unary operators.
    Not,
    Neg,
    IsEmpty,
    // Extension constructors.
    Decimal,
    Datetime,
    Duration,
    Ip,
    // Zero-argument extension methods.
    IsIpv4,
    IsIpv6,
    IsLoopback,
    IsMulticast,
    ToDate,
    ToTime,
    ToMilliseconds,
    ToSeconds,
    ToMinutes,
    ToHours,
    ToDays,
}

// ─── Pre-lowering diagnostic walks ───────────────────────────────────
//
// Read-only traversals of a parsed, macro-expanded policy, backing the
// diagnostic accessors on
// [`ParsedPolicySet`](crate::policy_set::ParsedPolicySet). They answer
// structural questions ("how many temporal blocks", "which providers are
// invoked") without exposing this AST. Run after macro expansion, so they
// see the effective post-expansion tree (a macro that expands to a temporal
// block or a provider call is counted).

impl Policy {
    /// The number of `temporal { … }` blocks in this policy — one per
    /// [`Extension::Temporal`] leaf, wherever it appears (a bare clause body
    /// or nested mid-expression). This is the unit a per-policy temporal
    /// quota is measured in, and matches the count of hoisted
    /// `context.<id>` temporal fields the lowered policy would reference.
    pub(crate) fn temporal_block_count(&self) -> usize {
        let mut n = 0;
        for cond in &self.conditions {
            cond.body.for_each_node(&mut |e| {
                if matches!(e.kind, ExprKind::Extension(Extension::Temporal(_))) {
                    n += 1;
                }
            });
        }
        n
    }

    /// The `.dw` source spans of each `temporal { … }` block in this policy,
    /// in source order. Each span covers the entire extension expression node.
    /// Used by pre-lowering rejection diagnostics to point at the offending
    /// block(s).
    pub(crate) fn temporal_block_spans(&self) -> Vec<Span> {
        let mut spans = Vec::new();
        for cond in &self.conditions {
            cond.body.for_each_node(&mut |e| {
                if matches!(e.kind, ExprKind::Extension(Extension::Temporal(_))) {
                    spans.push(e.span);
                }
            });
        }
        spans
    }

    /// The parsed condition of each `temporal { … }` block in this policy —
    /// one per [`Extension::Temporal`] leaf counted by
    /// [`temporal_block_count`](Policy::temporal_block_count), in source
    /// order. Runs after macro expansion, so a macro that expands to a
    /// temporal block contributes its condition. A read-only view of the
    /// authored (pre-lowering) temporal AST, for structural diagnostics that
    /// need no schema.
    pub(crate) fn temporal_conditions(&self) -> Vec<&crate::extension::temporal::ast::Condition> {
        let mut out = Vec::new();
        for cond in &self.conditions {
            cond.body.for_each_node(&mut |e| {
                if let ExprKind::Extension(Extension::Temporal(temporal)) = &e.kind {
                    out.push(&temporal.condition);
                }
            });
        }
        out
    }

    /// The information-provider invocation names in this policy, by
    /// declaration key (`Ns::Fn`), in source order with multiplicity.
    ///
    /// Recognized structurally via
    /// [`crate::extension::provider::is_provider_name`] — the same rule
    /// lowering uses — so this agrees with what `cedarify` would hoist. A
    /// method-chained invocation (`Ns::Fn(x).m()`) still bottoms out at the
    /// `Ns::Fn(...)` [`ExprKind::Call`], so counting `::`-calls captures every
    /// invocation site exactly once.
    pub(crate) fn provider_invocation_names(&self) -> Vec<String> {
        let mut names = Vec::new();
        for cond in &self.conditions {
            cond.body.for_each_node(&mut |e| {
                if let ExprKind::Call { name, .. } = &e.kind
                    && crate::extension::provider::is_provider_name(name)
                {
                    names.push(name.clone());
                }
            });
        }
        names
    }

    /// The information-provider invocations in this policy as structured
    /// [`Invocation`]s (name + resolved argument list), in source order with
    /// multiplicity — the same invocation sites
    /// [`provider_invocation_names`](Policy::provider_invocation_names) counts,
    /// each carrying its [`Arg`]s.
    ///
    /// Each invocation's arguments are extracted through
    /// [`cedar_call_to_invocation`](crate::cedarify::cedar_call_to_invocation)
    /// — the very conversion lowering uses — so the arguments reported here are
    /// exactly what lowering would hoist. This is why the walk is **fallible**:
    /// an argument outside the provider-argument grammar (an attribute path
    /// rooted at `context`/`principal`/`resource`, a literal, or a set of those
    /// — not arbitrary arithmetic or `if`) is rejected here with the same span
    /// and message lowering would give, rather than being silently reshaped.
    ///
    /// Recognized structurally (a `::`-qualified [`ExprKind::Call`]), matching
    /// `provider_invocation_names`; a method-chained invocation
    /// (`Ns::Fn(x).m()`) bottoms out at its base `Ns::Fn(...)` call, so it is
    /// captured once, without the trailing method chain.
    pub(crate) fn provider_invocations(
        &self,
    ) -> Result<Vec<crate::extension::provider::ast::Invocation>, crate::error::RawCedarifyError>
    {
        let mut out = Vec::new();
        let mut err = None;
        for cond in &self.conditions {
            cond.body.for_each_node(&mut |e| {
                if err.is_some() {
                    return;
                }
                if let ExprKind::Call { name, args } = &e.kind
                    && crate::extension::provider::is_provider_name(name)
                {
                    match crate::cedarify::cedar_call_to_invocation(name, args, e.span) {
                        Ok(inv) => out.push(inv),
                        Err(e) => err = Some(e),
                    }
                }
            });
            if let Some(e) = err {
                return Err(e);
            }
        }
        Ok(out)
    }
}

impl Expr {
    /// Visit this node and every descendant [`Expr`] (pre-order), applying
    /// `f`. Recurses through every recursive `ExprKind` variant so a marker
    /// or call nested anywhere in the tree is reached. Leaf payloads that are
    /// not [`Expr`]s (literals, patterns, entity types) are not recursed
    /// into — they hold no sub-expressions.
    pub(crate) fn for_each_node<'a>(&'a self, f: &mut impl FnMut(&'a Expr)) {
        f(self);
        match &self.kind {
            // Leaves — no sub-expressions.
            ExprKind::Lit(_)
            | ExprKind::Var(_)
            | ExprKind::Slot(_)
            | ExprKind::Extension(_)
            | ExprKind::ParamRef { .. } => {}

            ExprKind::UnaryApp { expr, .. } => expr.for_each_node(f),
            ExprKind::BinaryApp { left, right, .. } => {
                left.for_each_node(f);
                right.for_each_node(f);
            }
            ExprKind::GetAttr { expr, .. } | ExprKind::HasAttr { expr, .. } => {
                expr.for_each_node(f)
            }
            ExprKind::Like { expr, .. } => expr.for_each_node(f),
            ExprKind::Is { expr, in_expr, .. } => {
                expr.for_each_node(f);
                if let Some(in_e) = in_expr {
                    in_e.for_each_node(f);
                }
            }
            ExprKind::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.for_each_node(f);
                then_expr.for_each_node(f);
                else_expr.for_each_node(f);
            }
            ExprKind::Set(elems) => {
                for e in elems {
                    e.for_each_node(f);
                }
            }
            ExprKind::Record(entries) => {
                for e in entries.values() {
                    e.for_each_node(f);
                }
            }
            ExprKind::Call { args, .. } => {
                for a in args {
                    a.for_each_node(f);
                }
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                receiver.for_each_node(f);
                for a in args {
                    a.for_each_node(f);
                }
            }
        }
    }
}
