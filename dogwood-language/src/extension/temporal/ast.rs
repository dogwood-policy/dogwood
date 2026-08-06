//! The temporal sub-language AST.
//!
//! This mirrors the BNF of the temporal condition grammar
//! (`grammar.pest`): a [`Condition`] is a conjunction of conjuncts,
//! each of which may be a past-only temporal operator (`formerly`,
//! `previous`), a `since`, a negation (`!`), a predicate match, a
//! comparison, an aggregation, or a parenthesized sub-condition. The
//! shape deliberately follows the
//! existing temporal frontend so the evaluator and the regression
//! corpus agree on semantics.
//!
//! Spans are byte ranges into the *temporal block body* (the text
//! between the `temporal { … }` braces); the extension rebases them
//! into the original `.dw` source when reporting errors.

use crate::error::Span;

/// A temporal condition: top-level conjunction of conjuncts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Condition {
    pub span: Span,
    pub kind: ConditionKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConditionKind {
    /// `a && b` — both must hold.
    And {
        left: Box<Condition>,
        right: Box<Condition>,
    },
    /// `a || b` — at least one holds. **Internal-only**: the surface
    /// grammar has no disjunction, so the parser never produces this
    /// node. It is synthesized exclusively by the pin-relativization
    /// rewrite (`event_schema::relativize`), which needs "an event of
    /// any declared kind of mine" (μ) — a disjunction over the event
    /// schema's kinds. In a relational (aggregation) context it is the
    /// set union of the two branches' satisfying rows (deduplicated),
    /// mirroring the temporal engine's `UNION`. Range-restriction invariant:
    /// the rewrite only emits `Or` whose branches have identical free
    /// variables, each range-restricted within its own branch (per-branch
    /// wildcards are existentially closed inside the branch).
    Or {
        left: Box<Condition>,
        right: Box<Condition>,
    },
    /// `!a` — `a` does not hold. The negation of a conjunct; in a
    /// relational (aggregation) `where` body it acts as an anti-join
    /// filter (keep a row iff `a` does not hold under its bindings).
    Not { inner: Box<Condition> },
    /// `formerly within <interval> <body>` — `body` held at some past
    /// timepoint within the window.
    Formerly {
        within: WithinSpec,
        body: Box<Condition>,
    },
    /// `previous within <interval> <body>` — `body` held at the
    /// immediately preceding in-window timepoint.
    Previous {
        within: WithinSpec,
        body: Box<Condition>,
    },
    /// `<left> since within <interval> <right>`: `right` held within the
    /// window and `left` has held at every step since. The negative
    /// ("left has *not* held since") form is written `!left since …`,
    /// which builds a [`ConditionKind::Not`] around the left operand —
    /// there is no dedicated flag.
    Since {
        left: Box<Condition>,
        within: WithinSpec,
        right: Box<Condition>,
    },
    /// A predicate match against an event of a given kind:
    /// `Namespace::Action::"x"::kind{ field: term, … }`. Request and
    /// response events are both ordinary predicates distinguished by
    /// their `kind` segment; there is no separate resolved-predicate form.
    Predicate(Predicate),
    /// A comparison between two terms: `term <op> term`. Either term may
    /// be an aggregate ([`Term::Agg`]) — the comparison-operand-only rule
    /// (an aggregate must be the immediate operand of a comparison, not a
    /// predicate-arg value) is enforced by validation (`check`), not the
    /// grammar. An `<agg> == x` / `x == <agg>` form range-restricts `x` to
    /// the aggregate's value (see the evaluator).
    Comparison { op: CmpOp, left: Term, right: Term },
    /// `exists (x: T). φ` — holds iff `φ` has at least one satisfying
    /// assignment (with `x` range-restricted by a positive atom in `φ`:
    /// a predicate field `P{f:x}`, a `tp(x)`, or an equality against a
    /// computed term `(agg) == x`). The **sole binder** of the temporal
    /// sub-language: `let n = A in B` is expressed
    /// `exists (n: T). ((A) == n && B)`. `exists` is a binding form and
    /// extends its scope maximally to the right (greedy-right), stopping
    /// only at an enclosing `)` — the grammar realizes this by making the
    /// body a full `condition`.
    Exists {
        var: TypedBinder,
        body: Box<Condition>,
    },
    /// `tp(t)` — holds at the timepoint currently being evaluated, binding
    /// `t` to that timepoint's index. Conjoining `tp(t)` under a temporal
    /// scan unifies `t` to the timepoint the scan is visiting, so an
    /// aggregation domain can range over distinct timepoints.
    Tp { var: BinderSlot },
    /// `name(arg, …)` — an unresolved macro invocation that produces a
    /// condition. Resolved by the macro expansion pass; never reaches the
    /// evaluator (post-expansion every call has been substituted away).
    Call(Call),
    /// `?p` or `$t` standing for an entire condition. The macro expander
    /// substitutes the call-site argument's condition AST here. Only
    /// produced when parsing a macro body; the post-expansion AST
    /// contains none.
    SigilRef { sigil: Sigil, name: String },
    /// `base{ field: term, … }` — a trailing field-block that *refines* a
    /// predicate-valued base by injecting extra named args. The point is
    /// the macro case: a condition parameter bound to a predicate can be
    /// refined at the call site (`?s{ status: "approved" }`), forcing an
    /// otherwise-unmentioned field to a value.
    ///
    /// Transient. The macro expansion pass substitutes `base` (resolving a
    /// `?s` to a concrete [`Predicate`]) and then folds the injected
    /// `fields` onto that predicate's `args` (append = conjoin), replacing
    /// the `Refine` node with the augmented predicate. It never reaches
    /// the evaluator or the schema validator; those arms are `unreachable`.
    /// `base` must resolve to a single [`Predicate`] — refining any other
    /// shape (a conjunction, a `formerly`, a comparison) is a static error.
    Refine {
        base: Box<Condition>,
        fields: Vec<NamedArg>,
        span: Span,
    },
}

/// Which sigil a parameter/binder reference carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sigil {
    /// `?p` — value parameter reference.
    Param,
    /// `$t` — fresh-binder reference.
    Binder,
}

/// An aggregation expression — a numeric term (yielding `Long`). Carried
/// as a [`Term::Agg`]; the comparison-operand-only rule is enforced
/// by validation, not the grammar. A macro whose body *is* an aggregation
/// is spliced into a `Term::Agg` at its call site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AggExpr {
    pub span: Span,
    pub kind: AggExprKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AggExprKind {
    /// `sum v for (g1: T1), …, (gn: Tn). where <cond>` — the relation of
    /// satisfying assignments of `body` is projected onto `for_vars`,
    /// deduplicated, and then summed over `bound_var`. Distinctness is the
    /// user's visible choice: include a `tp`-bound variable in `for_vars`
    /// to keep per-timepoint rows, omit it to dedup equal values across
    /// time.
    ///
    /// `bound_var` is a *use* of a `for`-declared variable (bare — it is
    /// not itself a declaration site), so it stays a [`BinderSlot`]; the
    /// `for_vars` are the declaration sites and carry types.
    Sum {
        bound_var: BinderSlot,
        for_vars: Vec<TypedBinder>,
        body: Box<Condition>,
    },
    /// `count for (g1: T1), …, (gn: Tn). where <cond>` — sum-of-1 over the
    /// (projected, deduped) rows; see [`AggExprKind::Sum`] for `for_vars`
    /// semantics.
    Count {
        for_vars: Vec<TypedBinder>,
        body: Box<Condition>,
    },
    /// `name(arg, …)` — an unresolved macro invocation that produces an
    /// aggregation value. Resolved by the macro expansion pass.
    Call(Call),
}

/// A predicate: a qualified action name, an event kind, plus named
/// arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Predicate {
    pub span: Span,
    /// Qualified action, e.g. `["Drupe", "Action"]` + `"Login"`.
    pub namespace: Vec<String>,
    pub action: String,
    /// The event kind segment, e.g. `request` / `response` in
    /// `Drupe::Action::"Login"::request`. Mandatory in source (the
    /// grammar requires a trailing `::kind`); event kinds are
    /// author-defined, not a fixed set.
    pub kind: String,
    pub args: Vec<NamedArg>,
}

/// A `name: term` binding inside a predicate. The `name` is a field
/// path: a bare field (`user`) or a dotted path into a nested group
/// (`input.user`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedArg {
    pub name: String,
    pub value: Term,
}

impl NamedArg {
    /// The field name as a path (`"input.user"` → `["input", "user"]`).
    /// A bare name is a single-segment path.
    pub fn field_path(&self) -> Vec<String> {
        self.name.split('.').map(str::to_string).collect()
    }

    /// The field name as written, for diagnostics (`"input.user"`).
    pub fn field_name(&self) -> &str {
        &self.name
    }
}

/// A within-interval window: `within <n> <unit>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    pub amount: i64,
    pub unit: TimeUnit,
}

impl Interval {
    /// The window length in seconds, **saturating** on overflow.
    ///
    /// `amount` comes from untrusted policy text with no magnitude bound in the
    /// grammar, so `amount * unit.seconds()` can overflow i64 (e.g.
    /// `within 9223372036854775807d`). A plain `*` would panic in a debug build
    /// and — worse — silently *wrap* in a release build, potentially wrapping a
    /// huge window to a small or negative value that then slips under a
    /// `max_window` cap or makes a guard match nothing (a fail-open). Saturating
    /// to `i64::MAX` instead keeps an over-large window meaning "effectively
    /// unbounded", which is the safe (fail-closed) direction. Callers that need
    /// to *reject* an overflowing window use [`checked_seconds`](Interval::checked_seconds).
    pub fn seconds(&self) -> i64 {
        self.amount.saturating_mul(self.unit.seconds())
    }

    /// The window length in seconds, or `None` if `amount * unit.seconds()`
    /// overflows i64. The validator uses this to reject an over-large window at
    /// validation time with a clear error, rather than silently saturating.
    pub fn checked_seconds(&self) -> Option<i64> {
        self.amount.checked_mul(self.unit.seconds())
    }

    /// Render back to source syntax (`24h`, `30m`), for diagnostics.
    pub fn render(&self) -> String {
        format!("{}{}", self.amount, self.unit.token())
    }
}

/// A `within` window specification — either a concrete interval (after
/// parsing or after macro expansion) or a macro `?w` parameter
/// reference (only inside an unexpanded macro body). Post-expansion the
/// `ParamRef` variant is gone.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WithinSpec {
    Concrete(Interval),
    ParamRef(String),
}

impl WithinSpec {
    /// The concrete interval, panicking on a still-sigil spec.
    /// Use only on post-expansion AST.
    pub fn interval(&self) -> Interval {
        match self {
            WithinSpec::Concrete(i) => *i,
            WithinSpec::ParamRef(p) => panic!(
                "WithinSpec::interval: still a ?{p} after expansion (parser bug or pre-expansion call)"
            ),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimeUnit {
    Seconds,
    Minutes,
    Hours,
    Days,
}

impl TimeUnit {
    pub fn seconds(self) -> i64 {
        match self {
            TimeUnit::Seconds => 1,
            TimeUnit::Minutes => 60,
            TimeUnit::Hours => 3600,
            TimeUnit::Days => 86_400,
        }
    }

    pub fn from_token(tok: &str) -> Option<TimeUnit> {
        match tok {
            "s" => Some(TimeUnit::Seconds),
            "m" => Some(TimeUnit::Minutes),
            "h" => Some(TimeUnit::Hours),
            "d" => Some(TimeUnit::Days),
            _ => None,
        }
    }

    /// The source token for this unit (`s` / `m` / `h` / `d`).
    pub fn token(self) -> &'static str {
        match self {
            TimeUnit::Seconds => "s",
            TimeUnit::Minutes => "m",
            TimeUnit::Hours => "h",
            TimeUnit::Days => "d",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
    NotEq,
}

/// A term: a literal, a reference to a bound variable / context field,
/// or a structured value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// `Type::"id"` entity reference.
    Entity {
        ty: String,
        id: String,
    },
    Integer(i64),
    /// `decimal("1.5")` — payload kept as text (validated downstream).
    Decimal(String),
    String(String),
    Bool(bool),
    /// `context.input.foo` field access into the request **context** record,
    /// kept as the dotted path (the leading `context` is stripped, so
    /// `context.input.foo` is `["input", "foo"]`). This is Cedar's `context`
    /// variable — a plain record. It carries **no** special meaning for a
    /// `principal` / `resource` head segment: `context.principal` is an
    /// ordinary field named `principal` in the context record (as in Cedar,
    /// where `context.principal` is `GetAttr(context, "principal")`), *not* the
    /// request scope. The scope entities are [`Term::ScopeField`].
    ContextField(Vec<String>),
    /// `principal` / `resource` (optionally with an attribute tail:
    /// `principal.dept`, `resource.owner.zone`), kept as the dotted path with
    /// the `principal` / `resource` root as its first segment (`principal.dept`
    /// is `["principal", "dept"]`; a bare `principal` is `["principal"]`).
    ///
    /// This is Cedar's `principal` / `resource` request **variable** — an
    /// entity, distinct from the `context` record. A bare root is the scope
    /// entity itself (an identity comparison); an attribute tail reads that
    /// entity's attribute from the current request's entity store, with
    /// `.id` / `.type` projecting the uid — the temporal analog of a Cedar
    /// `principal.dept` and of the provider-arg `principal.dept`. It resolves
    /// against the **current request** at every timepoint the enclosing
    /// operator scans (a decision-time reference, never a matched past event).
    ScopeField(Vec<String>),
    /// A bare identifier (a bound variable name).
    Var(String),
    /// `*` wildcard (matches anything in a predicate arg position).
    Wildcard,
    Array(Vec<Term>),
    /// An aggregate value: `count for … where φ` / `sum a for … where φ`,
    /// yielding `Long`. A term syntactically, but the
    /// comparison-operand-only rule — an aggregate must be the
    /// immediate operand of a comparison, never a predicate-arg value or a
    /// nested term — is enforced by validation (`check`), not the grammar.
    Agg(Box<AggExpr>),
    /// `?p` — a macro value-parameter reference. Replaced during macro
    /// expansion by the literal call-site argument. Only legal inside a
    /// macro body; the post-expansion AST contains none.
    ParamRef(String),
    /// `$t` — a macro fresh-binder reference. Replaced during macro
    /// expansion by a deterministic gensym (`<name>$<call-span>`). Only
    /// legal inside a macro body; the post-expansion AST contains none.
    BinderRef(String),
}

/// A type annotation on a declaration-site binder. Drawn from the
/// event-schema concrete-type vocabulary (`Long`, `String`, entity types
/// like `Drupe::OAuthUser`) plus the temporal-only [`Type::Timepoint`].
///
/// Annotations are **parsed and carried through the AST but not yet
/// checked** against the schema — typed validation is deferred. The
/// distinct `Timepoint` type lets future
/// validation forbid nonsensical mixes (summing timepoints, comparing a
/// timepoint to an amount) that a plain `Long` would silently allow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// The timepoint-domain type of a `tp`-bound variable. Distinct from
    /// `Long` even though a timepoint index is an `i64` at runtime.
    Timepoint,
    /// A concrete named type: a single segment (`Long`, `String`) or a
    /// qualified entity type (`Drupe::OAuthUser`).
    Named(Vec<String>),
}

impl Type {
    /// Render the type back to source syntax (`Timepoint`,
    /// `Drupe::OAuthUser`), for diagnostics and macro expansion.
    pub fn render(&self) -> String {
        match self {
            Type::Timepoint => "Timepoint".to_string(),
            Type::Named(path) => path.join("::"),
        }
    }
}

/// A declaration-site binder: a [`BinderSlot`] paired with its mandatory
/// type annotation. Used wherever a variable is *introduced* — each `for`
/// list element (`for (a: Long), (t: Timepoint).`) and, in the redesign,
/// `exists (x: T)`. A *use* of the variable elsewhere (a `sum a`
/// reference, `tp(t)`, a predicate arg, a comparison operand) stays a bare
/// [`BinderSlot`] / [`Term::Var`] — it is not re-annotated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedBinder {
    pub slot: BinderSlot,
    pub ty: Type,
}

impl TypedBinder {
    /// The binder's underlying name, panicking if the slot is still a
    /// macro sigil. Use only on post-expansion AST.
    pub fn name(&self) -> &str {
        self.slot.name()
    }
}

/// A binder slot: a position that names a binder (a `for` list element,
/// the bound variable of `sum`, the variable of `tp(...)`). In ordinary
/// source it is a concrete identifier ([`BinderSlot::Name`]); inside a
/// macro body it may be a macro sigil to be substituted by expansion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinderSlot {
    Name(String),
    /// `?p` in binder position — at expansion the call-site argument
    /// must be a single identifier, spliced literally here.
    ParamRef(String),
    /// `$t` in binder position — gensym'd at expansion.
    BinderRef(String),
}

impl BinderSlot {
    /// The underlying name, panicking if the slot is still a macro
    /// sigil. Use only on post-expansion AST.
    pub fn name(&self) -> &str {
        match self {
            BinderSlot::Name(s) => s.as_str(),
            BinderSlot::ParamRef(p) => panic!(
                "BinderSlot::name: still a ?{p} after expansion (parser bug or pre-expansion call)"
            ),
            BinderSlot::BinderRef(b) => panic!(
                "BinderSlot::name: still a ${b} after expansion (parser bug or pre-expansion call)"
            ),
        }
    }
}

/// A macro invocation: a name and a list of arguments. The same shape is
/// used in condition position and in aggregation-value position; the
/// surrounding [`ConditionKind::Call`] / [`AggExprKind::Call`] wrapper
/// indicates which.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call {
    pub span: Span,
    pub name: String,
    pub args: Vec<CallArg>,
}

/// A macro call argument. Tagged with the syntactic category it parsed
/// as so the expander can check it against the parameter's usage in the
/// macro body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallArg {
    /// A temporal condition argument (`recent_login(1h, Foo{…})`'s
    /// second arg).
    Condition(Condition),
    /// A window argument: a bare interval literal at the call site
    /// (`recent_login(1h, …)`'s first arg), which fills a `within ?w`
    /// hole in the macro body. Note there is no `within` keyword on the
    /// argument — the keyword lives with the temporal operator.
    Within(Interval),
    /// A bare term — typically used to supply a single identifier as a
    /// binder-position argument, e.g. `sum_formerly(a, 1h, P(a))`'s
    /// first arg.
    Term(Term),
}
