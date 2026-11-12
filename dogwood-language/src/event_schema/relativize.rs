//! Pin relativization: rewrite temporal conditions so that, whenever the
//! event schema pins a field **universally and symmetrically**, evaluation is
//! provably confined to the sub-trace of events agreeing with the current
//! request on the pinned field(s) — making it *safe to partition* storage and
//! evaluation by those fields.
//!
//! # The guarantee this pass manufactures
//!
//! Pin injection ([`super::pin`]) already conjoins `f = context.<f>` onto
//! every predicate, so no *predicate* can match an event of another key
//! ("foreign" event). That confines every existential position (`formerly`
//! bodies, `since` anchors, aggregation rows). What it cannot confine are the
//! two **universally quantified** positions, where a foreign event influences
//! a verdict *by occupying a trace position* rather than by matching:
//!
//! * `previous` — "the event at position `i-1`" may be foreign;
//! * the left of `since` — "`left` held at **every** step `(j, i]`" is
//!   broken by a foreign event at any step (a pinned `left` cannot match it).
//!
//! This pass rewrites those constructs (and guards degenerate bodies) so the
//! formula's verdict over the **global** trace equals the original formula's
//! verdict over the **key-local sub-trace**. Partitioned storage then
//! implements the same semantics at zero cost: within a partition every event
//! is "mine", so the guards are tautological.
//!
//! # When it runs
//!
//! Only when the event schema declares at least one **universal symmetric
//! pin** — a field pinned on *every* declared event kind whose pin value is
//! the field's own path on the current request (`pin f: T = context.f`, or
//! the reserved scope aliases `pin callerPrincipal = principal` /
//! `pin callerResource = resource`). Schemas without such pins are
//! untouched — the rewrite is opt-in by schema. The default schema declares
//! one (on `callerPrincipal`), so its leaves are relativized; verdicts are
//! unchanged because the rewrite is verdict-preserving.
//!
//! # The encodings (and why they are range-restricted)
//!
//! Let μ ("mine") be the disjunction, over every declared event kind, of a
//! predicate carrying exactly the pinned correlations — "an event of any
//! kind agreeing with the current request on every pinned field". Every
//! μ-branch is a positive predicate, so μ is range-restricted branch-wise,
//! and all branches share the same correlation variables.
//!
//! * **Guarded bodies** — a temporal-scope body that does not already imply
//!   μ (no positive predicate conjunct) becomes `μ ∧ body`, so a foreign
//!   position can never witness it.
//! * **`previous within W φ`** becomes "the *most recent mine* position
//!   satisfies φ, within W" — tp-encoded with an exact window:
//!
//!   ```text
//!   ∃ti ∃tj. tp(ti) ∧ formerly[0,W](B ∧ tp(tj)) ∧ tj < ti
//!          ∧ ¬(∃tk. formerly[0,W](μ ∧ tp(tk))
//!               ∧ formerly[0,W](B ∧ tp(tj)) ∧ tp(ti)   ← local re-derivation
//!               ∧ tj < tk ∧ tk < ti)
//!   ```
//!
//!   where `B` is the (guarded) body. Every binder is restricted by a
//!   positive atom before any filter uses it (`ti` by `tp`, `tj`/`tk` by the
//!   `formerly` atoms); the comparisons appear after their restrictors in
//!   the same `&&` chain, satisfying both the language's conjunct-order rule
//!   and the temporal engine's local-filter rule. The window is measured from
//!   the decision point by the `formerly`, so it is exact.
//! * **`L since[0,W] A`** with a left that is *not* the confined negated
//!   idiom becomes "some in-window mine anchor `tj`, and every mine position
//!   in `(tj, ti]` satisfies `L`" — the continuity expressed as a **count
//!   equality** (`L`-satisfying mine positions = all mine positions in the
//!   range), since an anti-join cannot see `L`'s outer-bound variables:
//!
//!   ```text
//!   ∃ti ∃tj ∃n1 ∃n2. tp(ti) ∧ formerly[0,W](A' ∧ tp(tj))
//!     ∧ (count tk.  where formerly[0,W](μ ∧ tp(tk))       ∧ R) == n1
//!     ∧ (count tk2. where formerly[0,W]((μ ∧ L') ∧ tp(tk2)) ∧ R) == n2
//!     ∧ n1 == n2
//!   ```
//!
//!   with `R` the locally re-derived range (`formerly[0,W](A' ∧ tp(tj)) ∧
//!   tp(ti) ∧ tj < tk ∧ tk ≤ ti`). The negated-left idiom `!X since A` with
//!   a mine-confined `X` needs no encoding: a foreign position cannot
//!   satisfy the pinned `X`, so `¬X` holds there vacuously and the native
//!   `since` machinery already computes the local semantics.
//!
//! Every synthesized variable is fresh (`__pin_*<n>`), typed at its binder
//! (`Timepoint` / `Long`), and used only after a restricting atom.

use dogwood_syntax::{BudgetExhausted, NodeBudget};

use super::ast::PinRoot;
use super::derive::{DerivedEvent, DerivedEventSchema, Pin};
use crate::error::Span;
use crate::extension::temporal::ast::{
    AggExpr, AggExprKind, CmpOp, Condition, ConditionKind, NamedArg, Predicate, Term, Type,
    TypedBinder, WithinSpec,
};

/// A universal symmetric pin — the partition-key declaration this pass keys
/// on. `field_path` is the pinned leaf's dotted path; `context_path` its
/// (symmetric) request-side path; `root` selects which request term that path
/// resolves against (scope entity vs context field), mirroring pin injection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UniversalPin {
    pub field_path: Vec<String>,
    pub context_path: Vec<String>,
    pub root: PinRoot,
}

/// Compute the universal symmetric pins of a derived event schema: the pins
/// declared (identically) on **every** event kind whose context path is
/// *symmetric* — the field's own path, or the reserved principal/resource
/// scope alias. Returns an empty vec when the schema has no events (nothing
/// is universally pinned over an empty schema) or no qualifying pin.
pub fn universal_pins(schema: &DerivedEventSchema) -> Vec<UniversalPin> {
    let Some((first, rest)) = schema.events.split_first() else {
        return Vec::new();
    };
    first
        .pins
        .iter()
        .filter(|pin| is_symmetric(pin))
        .filter(|pin| rest.iter().all(|ev| ev.pins.contains(pin)))
        .map(|pin| UniversalPin {
            field_path: pin.field_path.clone(),
            context_path: pin.context_path.clone(),
            root: pin.root,
        })
        .collect()
}

/// Is a pin *symmetric* — does its request-side value resolve, on the current
/// decision event, to the pinned field's own value? True for `pin f = context.f`
/// (a context field at the field's own path) and for the reserved scope-alias
/// pairs (`callerPrincipal` ↔ `principal`, `callerResource` ↔ `resource`),
/// whose field the engine populates from the request scope. The alias case
/// requires a *scope* root: `callerPrincipal = context.principal` reads a
/// context field literally named `principal` (Cedar-consistent), not the scope
/// entity, so it is not the reserved alias and is not symmetric.
fn is_symmetric(pin: &Pin) -> bool {
    if pin.root == PinRoot::Context && pin.context_path == pin.field_path {
        return true;
    }
    if pin.root == PinRoot::Scope {
        let field = pin.field_path.join(".");
        let scope = pin.context_path.join(".");
        return (field == "callerPrincipal" && scope == "principal")
            || (field == "callerResource" && scope == "resource");
    }
    false
}

/// The error from [`relativize_condition`]: rewriting the leaf would create
/// more nodes than are left in the budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RelativizeError {
    /// The limit of the budget the rewrite was charged to.
    pub max_nodes: usize,
}

/// Rewrite one temporal leaf condition for the given universal pins.
/// No-op (returns a clone) when `pins` is empty.
///
/// Every node the rewrite creates (`Condition`, `Term`, and aggregation
/// nodes, cloned subtrees counted node by node) is charged to `budget` before
/// it is built; the caller shares one budget across all the leaves of one
/// policy set. The rewrite copies the rewritten body of a `previous` twice and
/// the anchor of a general `since` three times, so a nested `previous` grows
/// as 2^n and a right-nested `since` as 3^n; once the next node would pass the
/// budget it stops, before building it, with [`RelativizeError`]. What a
/// failed rewrite charged stays spent.
pub fn relativize_condition(
    cond: &Condition,
    schema: &DerivedEventSchema,
    pins: &[UniversalPin],
    budget: &mut NodeBudget,
) -> Result<Condition, RelativizeError> {
    let max_nodes = budget.limit();
    let mut cx = Cx {
        schema,
        pins,
        next_fresh: 0,
        budget,
    };
    let rewritten = if pins.is_empty() {
        cx.clone_cond(cond)
    } else {
        cx.rewrite(cond)
    };
    rewritten.map_err(|BudgetExhausted| RelativizeError { max_nodes })
}

/// A rewrite step's result: the node built, or the budget ran out first.
type Built<T> = Result<T, BudgetExhausted>;

struct Cx<'a> {
    schema: &'a DerivedEventSchema,
    pins: &'a [UniversalPin],
    next_fresh: u64,
    /// What is left of the policy set's node budget; every node the rewrite
    /// creates is charged to it before it is built.
    budget: &'a mut NodeBudget,
}

impl Cx<'_> {
    fn fresh(&mut self, stem: &str) -> String {
        let n = self.next_fresh;
        self.next_fresh += 1;
        format!("__pin_{stem}{n}")
    }

    // ── the node budget ──────────────────────────────────────────────

    /// Charge `n` nodes about to be built.
    fn charge(&mut self, n: usize) -> Built<()> {
        self.budget.charge(n)
    }

    /// A copy of `c`, its nodes charged before the copy is made.
    fn clone_cond(&mut self, c: &Condition) -> Built<Condition> {
        self.charge(crate::parser::condition_size(c))?;
        Ok(c.clone())
    }

    /// A copy of `t`, its nodes charged before the copy is made.
    fn clone_term(&mut self, t: &Term) -> Built<Term> {
        self.charge(crate::parser::term_size(t))?;
        Ok(t.clone())
    }

    // ── μ ────────────────────────────────────────────────────────────

    /// One μ-branch: a predicate for `event` carrying exactly the pinned
    /// correlations (every declared kind has every universal pin's field).
    fn mu_branch(&mut self, event: &DerivedEvent, span: Span) -> Built<Condition> {
        // The predicate and one term per pin.
        self.charge(1 + self.pins.len())?;
        let args = self
            .pins
            .iter()
            .map(|pin| NamedArg {
                name: pin.field_path.join("."),
                // Mirror `super::pin::inject_into_predicate`: a scope pin
                // (`= principal` / `= resource`) reads the request scope
                // entity, a context pin (`= context.<path>`) a context field.
                // Building the wrong term here reads a field the event never
                // carries, so no μ-branch matches and every relativized leaf
                // silently denies.
                value: match pin.root {
                    PinRoot::Scope => Term::ScopeField(pin.context_path.clone()),
                    PinRoot::Context => Term::ContextField(pin.context_path.clone()),
                },
            })
            .collect();
        Ok(Condition {
            span,
            kind: ConditionKind::Predicate(Predicate {
                span,
                namespace: event.namespace.clone(),
                action: event.action.clone(),
                kind: event.kind.clone(),
                args,
            }),
        })
    }

    /// μ — "an event of any declared kind of mine": the disjunction of one
    /// branch per derived event. Every branch is a positive predicate whose
    /// only terms are current-request references (scope entities or context
    /// fields, per each pin's root), so each branch is range-restricted and
    /// the branches bind no variables.
    ///
    /// The disjunction keeps branch order and has depth ⌈log₂ n⌉. μ has one
    /// branch per derived event, so a left-deep fold would nest as deep as
    /// the action schema is wide and overflow recursive consumers on wide
    /// schemas.
    fn mu(&mut self, span: Span) -> Built<Condition> {
        let schema = self.schema;
        let mut level: Vec<Condition> = schema
            .events
            .iter()
            .map(|ev| self.mu_branch(ev, span))
            .collect::<Built<_>>()?;
        while level.len() > 1 {
            let mut next = Vec::with_capacity(level.len().div_ceil(2));
            let mut it = level.into_iter();
            while let Some(left) = it.next() {
                next.push(match it.next() {
                    Some(right) => self.or(span, left, right)?,
                    None => left,
                });
            }
            level = next;
        }
        Ok(level
            .pop()
            .expect("universal_pins is empty for an event-less schema; rewrite not entered"))
    }

    // ── structural recursion ─────────────────────────────────────────

    fn rewrite(&mut self, c: &Condition) -> Built<Condition> {
        let span = c.span;
        Ok(match &c.kind {
            ConditionKind::And { left, right } => {
                let left = self.rewrite(left)?;
                let right = self.rewrite(right)?;
                self.and(span, left, right)?
            }
            ConditionKind::Or { left, right } => {
                let left = self.rewrite(left)?;
                let right = self.rewrite(right)?;
                self.or(span, left, right)?
            }
            ConditionKind::Not { inner } => {
                let inner = self.rewrite(inner)?;
                self.not(span, inner)?
            }
            ConditionKind::Exists { var, body } => {
                let body = self.rewrite(body)?;
                self.exists(span, var.clone(), body)?
            }
            ConditionKind::Comparison { op, left, right } => {
                let left = self.rewrite_term(left)?;
                let right = self.rewrite_term(right)?;
                self.comparison(span, *op, left, right)?
            }
            // `formerly` is existential: recursing + guarding the body is
            // sufficient (a pinned predicate cannot match a foreign event,
            // and the window is anchored at the decision point either way).
            ConditionKind::Formerly { within, body } => {
                let rewritten = self.rewrite(body)?;
                let guarded = self.guard_mine(rewritten)?;
                self.formerly(span, within.clone(), guarded)?
            }
            ConditionKind::Previous { within, body } => {
                self.rewrite_previous(span, within, body)?
            }
            ConditionKind::Since {
                left,
                within,
                right,
            } => self.rewrite_since(span, left, within, right)?,
            // Predicates are already pinned; tp is position-only.
            ConditionKind::Predicate(_) | ConditionKind::Tp { .. } => self.clone_cond(c)?,
            // Transient macro nodes never survive expansion, which runs
            // before this pass; pass them through untouched (downstream
            // arms treat them as unreachable).
            ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => self.clone_cond(c)?,
            ConditionKind::Refine {
                base,
                fields,
                span: rspan,
            } => {
                let base = self.rewrite(base)?;
                self.refine(span, base, fields, *rspan)?
            }
        })
    }

    fn rewrite_term(&mut self, t: &Term) -> Built<Term> {
        Ok(match t {
            Term::Agg(agg) => {
                let kind = match &agg.kind {
                    AggExprKind::Sum {
                        bound_var,
                        for_vars,
                        body,
                    } => AggExprKind::Sum {
                        bound_var: bound_var.clone(),
                        for_vars: for_vars.clone(),
                        body: Box::new(self.rewrite(body)?),
                    },
                    AggExprKind::Count { for_vars, body } => AggExprKind::Count {
                        for_vars: for_vars.clone(),
                        body: Box::new(self.rewrite(body)?),
                    },
                    // Macro residue never survives expansion; copied as is.
                    AggExprKind::Call(_) => return self.clone_term(t),
                };
                self.agg(agg.span, kind)?
            }
            Term::Array(items) => {
                let items = items
                    .iter()
                    .map(|i| self.rewrite_term(i))
                    .collect::<Built<Vec<_>>>()?;
                self.array(items)?
            }
            other => self.clone_term(other)?,
        })
    }

    // ── guards ───────────────────────────────────────────────────────

    /// Conjoin μ onto `body` unless it already implies "mine" (contains a
    /// positive predicate conjunct — pinned, so only a mine event matches).
    /// μ goes on the LEFT so it is the chain's restrictor.
    fn guard_mine(&mut self, body: Condition) -> Built<Condition> {
        if implies_mine(&body) {
            return Ok(body);
        }
        let span = body.span;
        let mu = self.mu(span)?;
        self.and(span, mu, body)
    }

    // ── `previous` ───────────────────────────────────────────────────

    fn rewrite_previous(
        &mut self,
        span: Span,
        within: &WithinSpec,
        body: &Condition,
    ) -> Built<Condition> {
        let b = self.rewrite(body)?;
        let b = self.guard_mine(b)?;
        let ti = self.fresh("ti");
        let tj = self.fresh("tj");
        let tk = self.fresh("tk");

        // formerly[0,W](B ∧ tp(tj))
        let tp_tj = self.tp(span, &tj)?;
        let b_at_tj = self.and(span, b, tp_tj)?;
        let anchor = self.formerly(span, within.clone(), b_at_tj)?;

        // ¬(∃tk. formerly[0,W](μ ∧ tp(tk)) ∧ <local tj/ti re-derivation>
        //        ∧ tj < tk ∧ tk < ti)
        let mu = self.mu(span)?;
        let tp_tk = self.tp(span, &tk)?;
        let mine_at_tk = self.and(span, mu, tp_tk)?;
        let between_parts = vec![
            self.formerly(span, within.clone(), mine_at_tk)?,
            self.clone_cond(&anchor)?,
            self.tp(span, &ti)?,
            self.cmp(span, CmpOp::Lt, &tj, &tk)?,
            self.cmp(span, CmpOp::Lt, &tk, &ti)?,
        ];
        let between_body = self.ands(span, between_parts)?;
        let between = self.exists_tp(span, &tk, between_body)?;

        let body_parts = vec![
            self.tp(span, &ti)?,
            anchor,
            self.cmp(span, CmpOp::Lt, &tj, &ti)?,
            self.not(span, between)?,
        ];
        let body = self.ands(span, body_parts)?;
        let inner = self.exists_tp_inner(span, &tj, body)?;
        self.exists_tp(span, &ti, inner)
    }

    // ── `since` ──────────────────────────────────────────────────────

    fn rewrite_since(
        &mut self,
        span: Span,
        left: &Condition,
        within: &WithinSpec,
        right: &Condition,
    ) -> Built<Condition> {
        let anchor_body = self.rewrite(right)?;
        let anchor_body = self.guard_mine(anchor_body)?;

        // Fast path — the negated-left idiom `!X since A` with a
        // mine-confined X: a foreign position cannot satisfy the pinned X,
        // so ¬X holds there vacuously and the native since already computes
        // the key-local semantics. (An unconfined X — e.g. a double
        // negation — falls through to the general encoding.)
        if let ConditionKind::Not { inner } = &left.kind
            && implies_mine(inner)
        {
            let l = self.rewrite(inner)?;
            let not_l = self.not(span, l)?;
            return self.since(span, not_l, within.clone(), anchor_body);
        }

        // General encoding: continuity over mine positions as a count
        // equality. `L` may bind variables in the original ∀-side; under
        // the count encoding those bindings stay internal to the count
        // body (grouped per outer correlation), which matches the ∀-side's
        // non-binding role in MFOTL since.
        let l = self.rewrite(left)?;
        let ti = self.fresh("ti");
        let tj = self.fresh("tj");
        // Distinct stems for the two count-body timepoint binders. They must
        // never alias (they range independently inside the two `count`s); using
        // distinct stems makes that self-evident rather than resting on
        // `fresh`'s monotonic counter incrementing between the two calls.
        let tk_all = self.fresh("tk_all");
        let tk_left = self.fresh("tk_left");
        let n1 = self.fresh("n");
        let n2 = self.fresh("n");

        // formerly[0,W](A' ∧ tp(tj)) — the anchor, exact window from now.
        let tp_tj = self.tp(span, &tj)?;
        let anchor_at_tj = self.and(span, anchor_body, tp_tj)?;
        let anchor = self.formerly(span, within.clone(), anchor_at_tj)?;

        // n1 = count of ALL μ positions in the range: count tk_all where
        // formerly[0,W](μ ∧ tp(tk_all)) ∧ range.
        let mu = self.mu(span)?;
        let tp_tk_all = self.tp(span, &tk_all)?;
        let mine_at = self.and(span, mu, tp_tk_all)?;
        let mut n1_parts = vec![self.formerly(span, within.clone(), mine_at)?];
        n1_parts.extend(self.range(span, &anchor, &ti, &tj, &tk_all)?);
        let n1_body = self.ands(span, n1_parts)?;
        let n1_count = self.count_agg(span, &tk_all, n1_body)?;

        // n2 = count of μ positions in the range that ALSO satisfy the left:
        // count tk_left where formerly[0,W]((μ ∧ L') ∧ tp(tk_left)) ∧ range.
        // Continuity ("left held at every μ position in (tj, ti]") is then
        // `n1 == n2` below.
        let mu = self.mu(span)?;
        let mine_l = self.and(span, mu, l)?;
        let tp_tk_left = self.tp(span, &tk_left)?;
        let mine_l_at = self.and(span, mine_l, tp_tk_left)?;
        let mut n2_parts = vec![self.formerly(span, within.clone(), mine_l_at)?];
        n2_parts.extend(self.range(span, &anchor, &ti, &tj, &tk_left)?);
        let n2_body = self.ands(span, n2_parts)?;
        let n2_count = self.count_agg(span, &tk_left, n2_body)?;

        let body_parts = vec![
            self.tp(span, &ti)?,
            self.clone_cond(&anchor)?,
            self.cmp_agg_eq(span, n1_count, &n1)?,
            self.cmp_agg_eq(span, n2_count, &n2)?,
            self.cmp_vars(span, CmpOp::Eq, &n1, &n2)?,
        ];
        let body = self.ands(span, body_parts)?;

        let body = self.exists_long(span, &n2, body)?;
        let body = self.exists_long(span, &n1, body)?;
        let body = self.exists_tp_inner(span, &tj, body)?;
        self.exists_tp(span, &ti, body)
    }

    /// The shared local range re-derivation for both `since` count bodies:
    /// the MFOTL `since` range **(tj, ti]** — strictly after the anchor `tj`,
    /// up to and INCLUDING the decision point `ti`. The strict lower / non-
    /// strict upper boundary (`tj < tk ∧ tk ≤ ti`) mirrors the native
    /// interpreter exactly (`eval_since` checks `left` over `(j+1)..=i`);
    /// changing either boundary's strictness silently misclassifies the
    /// anchor position or the decision point, so keep them as written.
    fn range(
        &mut self,
        span: Span,
        anchor: &Condition,
        ti: &str,
        tj: &str,
        tkv: &str,
    ) -> Built<Vec<Condition>> {
        Ok(vec![
            self.clone_cond(anchor)?,
            self.tp(span, ti)?,
            self.cmp(span, CmpOp::Lt, tj, tkv)?,
            self.cmp_le(span, tkv, ti)?,
        ])
    }
}

/// The only place the rewriter builds nodes. Each constructor charges the
/// budget for the nodes it creates before building them, so a node is paid
/// for before it exists.
impl Cx<'_> {
    fn and(&mut self, span: Span, left: Condition, right: Condition) -> Built<Condition> {
        self.charge(1)?;
        Ok(Condition {
            span,
            kind: ConditionKind::And {
                left: Box::new(left),
                right: Box::new(right),
            },
        })
    }

    fn or(&mut self, span: Span, left: Condition, right: Condition) -> Built<Condition> {
        self.charge(1)?;
        Ok(Condition {
            span,
            kind: ConditionKind::Or {
                left: Box::new(left),
                right: Box::new(right),
            },
        })
    }

    fn ands(&mut self, span: Span, parts: Vec<Condition>) -> Built<Condition> {
        let mut it = parts.into_iter();
        let first = it.next().expect("ands: non-empty");
        it.try_fold(first, |acc, p| self.and(span, acc, p))
    }

    fn not(&mut self, span: Span, inner: Condition) -> Built<Condition> {
        self.charge(1)?;
        Ok(Condition {
            span,
            kind: ConditionKind::Not {
                inner: Box::new(inner),
            },
        })
    }

    fn exists(&mut self, span: Span, var: TypedBinder, body: Condition) -> Built<Condition> {
        self.charge(1)?;
        Ok(Condition {
            span,
            kind: ConditionKind::Exists {
                var,
                body: Box::new(body),
            },
        })
    }

    fn comparison(&mut self, span: Span, op: CmpOp, left: Term, right: Term) -> Built<Condition> {
        self.charge(1)?;
        Ok(Condition {
            span,
            kind: ConditionKind::Comparison { op, left, right },
        })
    }

    /// `base` refined by copies of `fields`; the field terms are charged with
    /// the refinement node.
    fn refine(
        &mut self,
        span: Span,
        base: Condition,
        fields: &[NamedArg],
        refine_span: Span,
    ) -> Built<Condition> {
        let field_nodes: usize = fields
            .iter()
            .map(|f| crate::parser::term_size(&f.value))
            .sum();
        self.charge(1 + field_nodes)?;
        Ok(Condition {
            span,
            kind: ConditionKind::Refine {
                base: Box::new(base),
                fields: fields.to_vec(),
                span: refine_span,
            },
        })
    }

    fn since(
        &mut self,
        span: Span,
        left: Condition,
        within: WithinSpec,
        right: Condition,
    ) -> Built<Condition> {
        self.charge(1)?;
        Ok(Condition {
            span,
            kind: ConditionKind::Since {
                left: Box::new(left),
                within,
                right: Box::new(right),
            },
        })
    }

    fn tp(&mut self, span: Span, var: &str) -> Built<Condition> {
        self.charge(1)?;
        Ok(Condition {
            span,
            kind: ConditionKind::Tp {
                var: crate::extension::temporal::ast::BinderSlot::Name(var.to_string()),
            },
        })
    }

    fn formerly(&mut self, span: Span, within: WithinSpec, body: Condition) -> Built<Condition> {
        self.charge(1)?;
        Ok(Condition {
            span,
            kind: ConditionKind::Formerly {
                within,
                body: Box::new(body),
            },
        })
    }

    fn cmp(&mut self, span: Span, op: CmpOp, a: &str, b: &str) -> Built<Condition> {
        self.cmp_vars(span, op, a, b)
    }

    fn cmp_le(&mut self, span: Span, a: &str, b: &str) -> Built<Condition> {
        self.cmp_vars(span, CmpOp::Le, a, b)
    }

    fn cmp_vars(&mut self, span: Span, op: CmpOp, a: &str, b: &str) -> Built<Condition> {
        // The comparison and its two variable terms.
        self.charge(3)?;
        Ok(Condition {
            span,
            kind: ConditionKind::Comparison {
                op,
                left: Term::Var(a.to_string()),
                right: Term::Var(b.to_string()),
            },
        })
    }

    /// `(count …) == n` — the aggregate on the LEFT, the (fresh, exists-bound)
    /// result variable `n` on the RIGHT. Operand order is load-bearing: the
    /// evaluator's direct-binding rule (`eval::eq_binding`) binds whichever side
    /// is an *unbound* `Var` to the other side's value. Here `n` is unbound and
    /// the aggregate is a `Term::Agg` (never a bare var), so it binds `n` to the
    /// evaluated count — the effect this rewrite depends on. `n` must not be bound
    /// before this comparison (it is introduced by the enclosing `exists_long`
    /// solely for this binding), and the aggregate must stay on the left; swapping
    /// the operands or pre-binding `n` would turn this into a plain equality
    /// filter that never binds.
    fn cmp_agg_eq(&mut self, span: Span, agg: Term, n: &str) -> Built<Condition> {
        // The comparison and the variable term.
        self.charge(2)?;
        Ok(Condition {
            span,
            kind: ConditionKind::Comparison {
                op: CmpOp::Eq,
                left: agg,
                right: Term::Var(n.to_string()),
            },
        })
    }

    /// An aggregate term over `kind`.
    fn agg(&mut self, span: Span, kind: AggExprKind) -> Built<Term> {
        // The term and its aggregation.
        self.charge(2)?;
        Ok(Term::Agg(Box::new(AggExpr { span, kind })))
    }

    /// `count for (tk: Timepoint). where body` as a comparison operand.
    fn count_agg(&mut self, span: Span, over: &str, body: Condition) -> Built<Term> {
        self.agg(
            span,
            AggExprKind::Count {
                for_vars: vec![typed_tp(over)],
                body: Box::new(body),
            },
        )
    }

    fn array(&mut self, items: Vec<Term>) -> Built<Term> {
        self.charge(1)?;
        Ok(Term::Array(items))
    }

    fn exists_tp(&mut self, span: Span, var: &str, body: Condition) -> Built<Condition> {
        self.exists(span, typed_tp(var), body)
    }

    /// Alias of [`exists_tp`](Cx::exists_tp) for the inner (`tj`) binder —
    /// kept separate for readability at call sites.
    fn exists_tp_inner(&mut self, span: Span, var: &str, body: Condition) -> Built<Condition> {
        self.exists_tp(span, var, body)
    }

    fn exists_long(&mut self, span: Span, var: &str, body: Condition) -> Built<Condition> {
        self.exists(span, typed_long(var), body)
    }
}

/// Does this condition *imply* it matched a (pinned) event — i.e. does its
/// top-level positive structure contain a predicate conjunct? A pinned
/// predicate cannot match a foreign event, so any position witnessing the
/// condition is a mine position. Descends conjunctions (either side),
/// positive `exists`, and requires **both** branches of a disjunction.
fn implies_mine(c: &Condition) -> bool {
    match &c.kind {
        ConditionKind::Predicate(_) => true,
        ConditionKind::And { left, right } => implies_mine(left) || implies_mine(right),
        ConditionKind::Or { left, right } => implies_mine(left) && implies_mine(right),
        ConditionKind::Exists { body, .. } => implies_mine(body),
        _ => false,
    }
}

// ── binders (not tree nodes; never charged) ──────────────────────────

fn typed_tp(name: &str) -> TypedBinder {
    TypedBinder {
        slot: crate::extension::temporal::ast::BinderSlot::Name(name.to_string()),
        ty: Type::Timepoint,
    }
}

fn typed_long(name: &str) -> TypedBinder {
    TypedBinder {
        slot: crate::extension::temporal::ast::BinderSlot::Name(name.to_string()),
        ty: Type::Named(vec!["Long".to_string()]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event_schema::derive::derive;
    use crate::event_schema::parse::parse_event_schema;
    use crate::extension::temporal::ast::{Interval, TimeUnit};

    const ACTION_SCHEMA: &str = r#"
        namespace Drupe {
            entity OAuthUser = { id: String };
            entity Gateway;
            type LoginInput = { user: String };
            action "Login" appliesTo {
                principal: [OAuthUser],
                resource: [Gateway],
                context: { input: LoginInput }
            };
        }
    "#;

    fn pins_of(dsl: &str) -> Vec<UniversalPin> {
        let parsed = parse_event_schema(dsl).unwrap();
        let derived = derive(&parsed, ACTION_SCHEMA).unwrap();
        universal_pins(&derived)
    }

    #[test]
    fn principal_pin_on_all_kinds_is_universal() {
        let pins = pins_of(
            r#"
            decision event <A>::request {
                ...inputs(A),
                pin callerPrincipal: principalType(A) = principal,
                requestId: String,
            }
            event <A>::response {
                ...inputs(A),
                pin callerPrincipal: principalType(A) = principal,
                requestId: String,
            }
            "#,
        );
        assert_eq!(
            pins,
            vec![UniversalPin {
                field_path: vec!["callerPrincipal".into()],
                context_path: vec!["principal".into()],
                root: PinRoot::Scope,
            }]
        );
    }

    #[test]
    fn partial_pin_is_not_universal() {
        // Pinned on `request` only — `response` predicates could match
        // cross-key events, so no partition guarantee.
        let pins = pins_of(
            r#"
            decision event <A>::request {
                ...inputs(A),
                pin callerPrincipal: principalType(A) = principal,
                requestId: String,
            }
            event <A>::response {
                ...inputs(A),
                callerPrincipal: principalType(A),
                requestId: String,
            }
            "#,
        );
        assert!(pins.is_empty(), "{pins:?}");
    }

    #[test]
    fn symmetric_field_pin_is_universal_and_asymmetric_is_not() {
        // `session_id = context.session_id` is symmetric; a pin whose
        // context path differs from its field path is not (storage key and
        // query key would diverge).
        let pins = pins_of(
            r#"
            decision event <A>::request {
                ...inputs(A),
                pin session_id: String = context.session_id,
                pin actor: principalType(A) = context.principal,
                requestId: String,
            }
            event <A>::response {
                ...inputs(A),
                pin session_id: String = context.session_id,
                pin actor: principalType(A) = context.principal,
                requestId: String,
            }
            "#,
        );
        // `session_id` qualifies (context path == field path); `actor =
        // context.principal` does not — its context path differs from its
        // field path, and the reserved scope-alias pairing applies only to
        // the reserved field name with a *scope* root (`= principal`).
        assert_eq!(
            pins,
            vec![UniversalPin {
                field_path: vec!["session_id".into()],
                context_path: vec!["session_id".into()],
                root: PinRoot::Context,
            }]
        );
    }

    #[test]
    fn no_pins_means_no_rewrite() {
        let pins = pins_of(
            r#"
            decision event <A>::request { ...inputs(A), requestId: String }
            event <A>::response { ...inputs(A), requestId: String }
            "#,
        );
        assert!(pins.is_empty());
    }

    /// `previous within 1h Login::request{}`: a leaf the rewrite transforms
    /// under pins, so an accidental rewrite would be visible.
    fn previous_login() -> Condition {
        let span = Span::new(0, 0);
        Condition {
            span,
            kind: ConditionKind::Previous {
                within: WithinSpec::Concrete(Interval {
                    amount: 1,
                    unit: TimeUnit::Hours,
                }),
                body: Box::new(Condition {
                    span,
                    kind: ConditionKind::Predicate(Predicate {
                        span,
                        namespace: vec!["Drupe".into(), "Action".into()],
                        action: "Login".into(),
                        kind: "request".into(),
                        args: vec![],
                    }),
                }),
            },
        }
    }

    /// With no universal pins, `relativize_condition` is the identity — the
    /// authored leaf is returned unchanged. This is the structural counterpart
    /// to the "slice is the specification" claim the differential suites rely
    /// on: a schema without a qualifying pin keeps the global-trace semantics
    /// untouched. A regression that started rewriting
    /// unconditionally would fail here.
    #[test]
    fn empty_pins_relativize_is_identity() {
        let leaf = previous_login();

        // An events-bearing schema (so a bug can't be masked by an empty schema
        // early-return), but with NO pins → `universal_pins` is empty.
        let parsed = parse_event_schema(
            r#"
            decision event <A>::request { ...inputs(A), requestId: String }
            event <A>::response { ...inputs(A), requestId: String }
            "#,
        )
        .unwrap();
        let derived = derive(&parsed, ACTION_SCHEMA).unwrap();
        let pins = universal_pins(&derived);
        assert!(pins.is_empty(), "precondition: no universal pins");

        let out = relativize_condition(
            &leaf,
            &derived,
            &pins,
            &mut NodeBudget::new(dogwood_syntax::DEFAULT_MAX_NODES),
        )
        .expect("within budget");
        assert_eq!(out, leaf, "no-pin relativization must be the identity");
    }

    /// `is_symmetric` boundary table — the classifier that decides whether a
    /// pin activates the partition rewrite. The rows include the cases the
    /// Cedar-consistent split turns on: the reserved alias requires a *scope*
    /// root (`= principal`), while `= context.principal` (a context field
    /// literally named `principal`) is NOT the reserved alias.
    #[test]
    fn is_symmetric_boundary_table() {
        fn pin(field: &[&str], context: &[&str], root: PinRoot) -> Pin {
            Pin {
                field_path: field.iter().map(|s| s.to_string()).collect(),
                context_path: context.iter().map(|s| s.to_string()).collect(),
                root,
            }
        }
        use PinRoot::{Context, Scope};

        // (field, context_path, root, expected_symmetric, why)
        let cases: &[(&[&str], &[&str], PinRoot, bool, &str)] = &[
            // Reserved scope aliases — symmetric ONLY with a scope root.
            (
                &["callerPrincipal"],
                &["principal"],
                Scope,
                true,
                "principal scope alias",
            ),
            (
                &["callerResource"],
                &["resource"],
                Scope,
                true,
                "resource scope alias",
            ),
            // The exact pre-rebase footgun: `= context.principal` is a context
            // field named `principal`, NOT the scope entity → not the alias.
            (
                &["callerPrincipal"],
                &["principal"],
                Context,
                false,
                "context.principal is not the alias",
            ),
            (
                &["callerResource"],
                &["resource"],
                Context,
                false,
                "context.resource is not the alias",
            ),
            // Symmetric context pin: context path equals the field's own path.
            (
                &["session_id"],
                &["session_id"],
                Context,
                true,
                "context.session_id == field path",
            ),
            (
                &["__drupe", "session_id"],
                &["__drupe", "session_id"],
                Context,
                true,
                "nested symmetric context pin",
            ),
            // Asymmetric: context path differs from field path, non-reserved.
            (
                &["actor"],
                &["principal"],
                Context,
                false,
                "actor = context.principal is asymmetric",
            ),
            (
                &["session_id"],
                &["other_id"],
                Context,
                false,
                "context path differs from field path",
            ),
            // A scope-rooted attribute pin that is not a reserved alias.
            (
                &["dept"],
                &["principal", "dept"],
                Scope,
                false,
                "principal.dept is not a reserved alias",
            ),
        ];

        for (field, context, root, expected, why) in cases {
            let got = is_symmetric(&pin(field, context, *root));
            assert_eq!(got, *expected, "is_symmetric mismatch: {why}");
        }
    }

    /// Collect every predicate reachable under a condition (structural walk),
    /// so a test can inspect the synthesized μ-guard's args.
    fn predicates_in(c: &Condition, out: &mut Vec<Predicate>) {
        match &c.kind {
            ConditionKind::Predicate(p) => out.push(p.clone()),
            ConditionKind::And { left, right }
            | ConditionKind::Or { left, right }
            | ConditionKind::Since { left, right, .. } => {
                predicates_in(left, out);
                predicates_in(right, out);
            }
            ConditionKind::Not { inner }
            | ConditionKind::Formerly { body: inner, .. }
            | ConditionKind::Previous { body: inner, .. }
            | ConditionKind::Exists { body: inner, .. } => predicates_in(inner, out),
            _ => {}
        }
    }

    /// The μ-guard synthesized for a pin must read each pin's request-side value
    /// through the term type its `root` selects: a scope pin (`= principal`) as
    /// `Term::ScopeField`, a context pin (`= context.<path>`) as
    /// `Term::ContextField`. This is the exact discrimination `mu_branch` makes;
    /// emitting the wrong term reads a field the event never carries, so no
    /// μ-branch matches and every relativized leaf silently denies. (Regression
    /// guard for the pre-Cedar-consistent `ContextField`-always bug.)
    #[test]
    fn mu_branch_selects_term_type_by_pin_root() {
        // A two-pin schema mixing roots: `callerPrincipal = principal` (scope)
        // and a nested `__drupe.session_id = context.__drupe.session_id`
        // (context).
        let parsed = parse_event_schema(
            r#"
            decision event <A>::request {
                ...inputs(A),
                pin callerPrincipal: principalType(A) = principal,
                requestId: String,
                __drupe: { pin session_id: String = context.__drupe.session_id },
            }
            event <A>::response {
                ...inputs(A),
                pin callerPrincipal: principalType(A) = principal,
                requestId: String,
                __drupe: { pin session_id: String = context.__drupe.session_id },
            }
            "#,
        )
        .unwrap();
        let derived = derive(&parsed, ACTION_SCHEMA).unwrap();
        let pins = universal_pins(&derived);
        // Both pins qualify (one scope-alias, one symmetric context field).
        assert_eq!(pins.len(), 2, "expected two universal pins: {pins:?}");

        // Build μ directly (the disjunction of one branch per derived event).
        let span = Span::new(0, 0);
        let mut budget = NodeBudget::new(dogwood_syntax::DEFAULT_MAX_NODES);
        let mut cx = Cx {
            schema: &derived,
            pins: &pins,
            next_fresh: 0,
            budget: &mut budget,
        };
        let mu = cx.mu(span).expect("within budget");

        let mut preds = Vec::new();
        predicates_in(&mu, &mut preds);
        assert!(!preds.is_empty(), "μ produced no predicates");

        // Every μ-branch predicate must carry BOTH pin correlations, each with
        // the term type its root selects.
        for p in &preds {
            let principal = p
                .args
                .iter()
                .find(|a| a.name == "callerPrincipal")
                .unwrap_or_else(|| panic!("μ-branch missing callerPrincipal arg: {p:?}"));
            assert_eq!(
                principal.value,
                Term::ScopeField(vec!["principal".into()]),
                "scope pin must lower to ScopeField, not ContextField (Cedar-consistent)"
            );

            let session = p
                .args
                .iter()
                .find(|a| a.name == "__drupe.session_id")
                .unwrap_or_else(|| panic!("μ-branch missing session_id arg: {p:?}"));
            assert_eq!(
                session.value,
                Term::ContextField(vec!["__drupe".into(), "session_id".into()]),
                "context pin must lower to ContextField at its dotted path"
            );
        }
    }

    /// Nesting depth of the `Or` spine (non-`Or` nodes count as zero).
    fn or_depth(c: &Condition) -> usize {
        match &c.kind {
            ConditionKind::Or { left, right } => 1 + or_depth(left).max(or_depth(right)),
            _ => 0,
        }
    }

    /// μ over a wide action schema nests logarithmically, not linearly: a
    /// left-deep μ over 100 actions × 3 kinds would be ~300 `Or`s deep, deep
    /// enough to overflow recursive consumers. Branch order is preserved.
    #[test]
    fn mu_depth_is_logarithmic_in_branch_count() {
        let actions: String = (0..100)
            .map(|i| {
                format!(
                    r#"action "A{i}" appliesTo {{
                        principal: [OAuthUser], resource: [Gateway],
                        context: {{ input: LoginInput }}
                    }};"#
                )
            })
            .collect();
        let action_schema = format!(
            "namespace Drupe {{ entity OAuthUser = {{ id: String }}; entity Gateway; \
             type LoginInput = {{ user: String }}; {actions} }}"
        );
        let parsed = parse_event_schema(crate::DEFAULT_EVENT_SCHEMA).unwrap();
        let derived = derive(&parsed, &action_schema).unwrap();
        let pins = universal_pins(&derived);
        assert!(!pins.is_empty(), "default schema pins callerPrincipal");
        let mut budget = NodeBudget::new(dogwood_syntax::DEFAULT_MAX_NODES);
        let mut cx = Cx {
            schema: &derived,
            pins: &pins,
            next_fresh: 0,
            budget: &mut budget,
        };
        let mu = cx.mu(Span::new(0, 0)).expect("within budget");

        // One derived event per action × declared kind; wide enough that a
        // left-deep μ would be far deeper than the balanced one.
        let n = derived.events.len();
        assert_eq!(n, 100 * parsed.decls.len());
        assert!(n > 64, "too few branches to exercise depth: {n}");
        assert_eq!(or_depth(&mu), n.next_power_of_two().ilog2() as usize);

        let mut preds = Vec::new();
        predicates_in(&mu, &mut preds);
        let got: Vec<_> = preds.iter().map(|p| (&p.action, &p.kind)).collect();
        let want: Vec<_> = derived
            .events
            .iter()
            .map(|e| (&e.action, &e.kind))
            .collect();
        assert_eq!(got, want, "μ branches stay in derived-event order");

        // The balanced builder charges exactly the nodes it builds: a budget
        // of μ's size suffices and one node less does not.
        let size = crate::parser::condition_size(&mu);
        for (limit, fits) in [(size, true), (size - 1, false)] {
            let mut budget = NodeBudget::new(limit);
            let mut cx = Cx {
                schema: &derived,
                pins: &pins,
                next_fresh: 0,
                budget: &mut budget,
            };
            assert_eq!(cx.mu(Span::new(0, 0)).is_ok(), fits, "limit {limit}");
        }
    }

    /// Every constructor charges exactly the nodes it builds, so a whole
    /// rewrite charges the size of its output plus the nodes it builds and
    /// then drops: that budget suffices and one node less does not. The
    /// shapes between them reach every constructor.
    #[test]
    fn rewrite_charges_exactly_the_nodes_it_builds() {
        use crate::extension::temporal::parse::parse_condition;
        const LOGIN: &str = r#"Drupe::Action::"Login"::request{}"#;
        let parse = |src: &str| parse_condition(src).unwrap_or_else(|e| panic!("{src}: {e}"));
        let derived = derive_kinds(&["request", "response"]);
        let pins = universal_pins(&derived);
        assert_eq!(pins.len(), 1, "{pins:?}");

        // (shape, condition, nodes built but not in the output)
        let cases: Vec<(&str, Condition, usize)> = vec![
            ("or of predicates", or(parse(LOGIN), parse(LOGIN)), 0),
            (
                "exists",
                parse(&format!(
                    "exists (t: Timepoint). formerly within 1h ({LOGIN} && tp(t))"
                )),
                0,
            ),
            (
                "comparison, arith, array",
                parse("[(1 + 2 * 3), 4] == [5]"),
                0,
            ),
            ("refine", parse(&format!(r#"{LOGIN}{{ user: "u" }}"#)), 0),
            ("previous", parse(&format!("previous within 1h {LOGIN}")), 0),
            // The general `since` encoding builds the anchor
            // `formerly within 1h (A && tp(tj))` (4 nodes here), places only
            // three copies of it, and drops the original.
            (
                "positive since",
                parse(&format!("{LOGIN} since within 1h {LOGIN}")),
                4,
            ),
            (
                "negated-left since",
                parse(&format!("!{LOGIN} since within 1h {LOGIN}")),
                0,
            ),
            (
                "count",
                parse(&format!(
                    "0 < count for (t: Timepoint). where formerly within 1h ({LOGIN} && tp(t))"
                )),
                0,
            ),
        ];
        for (name, cond, dropped) in &cases {
            let out = relativize_condition(
                cond,
                &derived,
                &pins,
                &mut NodeBudget::new(dogwood_syntax::DEFAULT_MAX_NODES),
            )
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
            let built = crate::parser::condition_size(&out) + dropped;
            for (limit, fits) in [(built, true), (built - 1, false)] {
                let got = relativize_condition(cond, &derived, &pins, &mut NodeBudget::new(limit));
                assert_eq!(
                    got.is_ok(),
                    fits,
                    "{name}: limit {limit}, {built} nodes built"
                );
            }
        }
    }

    /// A pinned event schema with one event kind per name (the first is the
    /// decision event), derived over the single-action [`ACTION_SCHEMA`].
    fn derive_kinds(kinds: &[&str]) -> DerivedEventSchema {
        let decls: String = kinds
            .iter()
            .enumerate()
            .map(|(i, k)| {
                let decision = if i == 0 { "decision " } else { "" };
                format!(
                    "{decision}event <A>::{k} {{ ...inputs(A), \
                     pin callerPrincipal: principalType(A) = principal }}\n"
                )
            })
            .collect();
        derive(&parse_event_schema(&decls).unwrap(), ACTION_SCHEMA).unwrap()
    }

    fn or(left: Condition, right: Condition) -> Condition {
        Condition {
            span: Span::new(0, 0),
            kind: ConditionKind::Or {
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    /// Up to three alternatives the balanced μ is the left-nested fold, so
    /// relativized leaves over such schemas keep their shape (and any
    /// fingerprint of it).
    #[test]
    fn mu_shape_for_up_to_three_alternatives() {
        let span = Span::new(0, 0);
        for kinds in [&["a"][..], &["a", "b"], &["a", "b", "c"]] {
            let derived = derive_kinds(kinds);
            let pins = universal_pins(&derived);
            assert_eq!(pins.len(), 1, "{kinds:?}: {pins:?}");
            let mut budget = NodeBudget::new(dogwood_syntax::DEFAULT_MAX_NODES);
            let mut cx = Cx {
                schema: &derived,
                pins: &pins,
                next_fresh: 0,
                budget: &mut budget,
            };
            let b: Vec<_> = derived
                .events
                .iter()
                .map(|ev| cx.mu_branch(ev, span).expect("within budget"))
                .collect();
            let want = match b.as_slice() {
                [b0] => b0.clone(),
                [b0, b1] => or(b0.clone(), b1.clone()),
                [b0, b1, b2] => or(or(b0.clone(), b1.clone()), b2.clone()),
                _ => unreachable!("one derived event per kind"),
            };
            assert_eq!(cx.mu(span), Ok(want), "{kinds:?}");
        }
    }

    /// An event-less schema has no universal pins, so relativization is the
    /// identity and μ is never built.
    #[test]
    fn empty_schema_relativize_is_identity() {
        let parsed = parse_event_schema(crate::DEFAULT_EVENT_SCHEMA).unwrap();
        let derived = derive(&parsed, "namespace Drupe { entity Gateway; }").unwrap();
        assert!(derived.events.is_empty());
        let pins = universal_pins(&derived);
        assert!(pins.is_empty());
        let leaf = previous_login();
        let out = relativize_condition(
            &leaf,
            &derived,
            &pins,
            &mut NodeBudget::new(dogwood_syntax::DEFAULT_MAX_NODES),
        );
        assert_eq!(out, Ok(leaf));
    }
}
