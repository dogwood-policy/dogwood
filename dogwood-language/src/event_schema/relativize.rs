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

/// Rewrite one temporal leaf condition for the given universal pins.
/// No-op (returns a clone) when `pins` is empty.
pub fn relativize_condition(
    cond: &Condition,
    schema: &DerivedEventSchema,
    pins: &[UniversalPin],
) -> Condition {
    if pins.is_empty() {
        return cond.clone();
    }
    let mut cx = Cx {
        schema,
        pins,
        next_fresh: 0,
    };
    cx.rewrite(cond)
}

struct Cx<'a> {
    schema: &'a DerivedEventSchema,
    pins: &'a [UniversalPin],
    next_fresh: u64,
}

impl Cx<'_> {
    fn fresh(&mut self, stem: &str) -> String {
        let n = self.next_fresh;
        self.next_fresh += 1;
        format!("__pin_{stem}{n}")
    }

    // ── μ ────────────────────────────────────────────────────────────

    /// One μ-branch: a predicate for `event` carrying exactly the pinned
    /// correlations (every declared kind has every universal pin's field).
    fn mu_branch(&self, event: &DerivedEvent, span: Span) -> Condition {
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
        Condition {
            span,
            kind: ConditionKind::Predicate(Predicate {
                span,
                namespace: event.namespace.clone(),
                action: event.action.clone(),
                kind: event.kind.clone(),
                args,
            }),
        }
    }

    /// μ — "an event of any declared kind of mine": the disjunction of one
    /// branch per derived event. Every branch is a positive predicate whose
    /// only terms are current-request references (scope entities or context
    /// fields, per each pin's root), so each branch is range-restricted and
    /// the branches bind no variables.
    fn mu(&self, span: Span) -> Condition {
        let mut branches = self.schema.events.iter().map(|ev| self.mu_branch(ev, span));
        let first = branches
            .next()
            .expect("universal_pins is empty for an event-less schema; rewrite not entered");
        branches.fold(first, |acc, b| Condition {
            span,
            kind: ConditionKind::Or {
                left: Box::new(acc),
                right: Box::new(b),
            },
        })
    }

    // ── structural recursion ─────────────────────────────────────────

    fn rewrite(&mut self, c: &Condition) -> Condition {
        let span = c.span;
        match &c.kind {
            ConditionKind::And { left, right } => Condition {
                span,
                kind: ConditionKind::And {
                    left: Box::new(self.rewrite(left)),
                    right: Box::new(self.rewrite(right)),
                },
            },
            ConditionKind::Or { left, right } => Condition {
                span,
                kind: ConditionKind::Or {
                    left: Box::new(self.rewrite(left)),
                    right: Box::new(self.rewrite(right)),
                },
            },
            ConditionKind::Not { inner } => Condition {
                span,
                kind: ConditionKind::Not {
                    inner: Box::new(self.rewrite(inner)),
                },
            },
            ConditionKind::Exists { var, body } => Condition {
                span,
                kind: ConditionKind::Exists {
                    var: var.clone(),
                    body: Box::new(self.rewrite(body)),
                },
            },
            ConditionKind::Comparison { op, left, right } => Condition {
                span,
                kind: ConditionKind::Comparison {
                    op: *op,
                    left: self.rewrite_term(left),
                    right: self.rewrite_term(right),
                },
            },
            // `formerly` is existential: recursing + guarding the body is
            // sufficient (a pinned predicate cannot match a foreign event,
            // and the window is anchored at the decision point either way).
            ConditionKind::Formerly { within, body } => {
                let rewritten = self.rewrite(body);
                let guarded = self.guard_mine(rewritten);
                Condition {
                    span,
                    kind: ConditionKind::Formerly {
                        within: within.clone(),
                        body: Box::new(guarded),
                    },
                }
            }
            ConditionKind::Previous { within, body } => self.rewrite_previous(span, within, body),
            ConditionKind::Since {
                left,
                within,
                right,
            } => self.rewrite_since(span, left, within, right),
            // Predicates are already pinned; tp is position-only.
            ConditionKind::Predicate(_) | ConditionKind::Tp { .. } => c.clone(),
            // Transient macro nodes never survive expansion, which runs
            // before this pass; pass them through untouched (downstream
            // arms treat them as unreachable).
            ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => c.clone(),
            ConditionKind::Refine {
                base,
                fields,
                span: rspan,
            } => Condition {
                span,
                kind: ConditionKind::Refine {
                    base: Box::new(self.rewrite(base)),
                    fields: fields.clone(),
                    span: *rspan,
                },
            },
        }
    }

    fn rewrite_term(&mut self, t: &Term) -> Term {
        match t {
            Term::Agg(agg) => {
                let kind = match &agg.kind {
                    AggExprKind::Sum {
                        bound_var,
                        for_vars,
                        body,
                    } => AggExprKind::Sum {
                        bound_var: bound_var.clone(),
                        for_vars: for_vars.clone(),
                        body: Box::new(self.rewrite(body)),
                    },
                    AggExprKind::Count { for_vars, body } => AggExprKind::Count {
                        for_vars: for_vars.clone(),
                        body: Box::new(self.rewrite(body)),
                    },
                    AggExprKind::Call(c) => AggExprKind::Call(c.clone()),
                };
                Term::Agg(Box::new(AggExpr {
                    span: agg.span,
                    kind,
                }))
            }
            Term::Array(items) => Term::Array(items.iter().map(|i| self.rewrite_term(i)).collect()),
            other => other.clone(),
        }
    }

    // ── guards ───────────────────────────────────────────────────────

    /// Conjoin μ onto `body` unless it already implies "mine" (contains a
    /// positive predicate conjunct — pinned, so only a mine event matches).
    /// μ goes on the LEFT so it is the chain's restrictor.
    fn guard_mine(&mut self, body: Condition) -> Condition {
        if implies_mine(&body) {
            return body;
        }
        let span = body.span;
        Condition {
            span,
            kind: ConditionKind::And {
                left: Box::new(self.mu(span)),
                right: Box::new(body),
            },
        }
    }

    // ── `previous` ───────────────────────────────────────────────────

    fn rewrite_previous(&mut self, span: Span, within: &WithinSpec, body: &Condition) -> Condition {
        let b = self.rewrite(body);
        let b = self.guard_mine(b);
        let ti = self.fresh("ti");
        let tj = self.fresh("tj");
        let tk = self.fresh("tk");

        // formerly[0,W](B ∧ tp(tj))
        let anchor = formerly(span, within.clone(), and(span, b.clone(), tp(span, &tj)));

        // ¬(∃tk. formerly[0,W](μ ∧ tp(tk)) ∧ <local tj/ti re-derivation>
        //        ∧ tj < tk ∧ tk < ti)
        let mine_at_tk = and(span, self.mu(span), tp(span, &tk));
        let between = exists_tp(
            span,
            &tk,
            ands(
                span,
                vec![
                    formerly(span, within.clone(), mine_at_tk),
                    anchor.clone(),
                    tp(span, &ti),
                    cmp(span, CmpOp::Lt, &tj, &tk),
                    cmp(span, CmpOp::Lt, &tk, &ti),
                ],
            ),
        );

        let body = ands(
            span,
            vec![
                tp(span, &ti),
                anchor,
                cmp(span, CmpOp::Lt, &tj, &ti),
                not(span, between),
            ],
        );
        exists_tp(span, &ti, exists_tp_inner(span, &tj, body))
    }

    // ── `since` ──────────────────────────────────────────────────────

    fn rewrite_since(
        &mut self,
        span: Span,
        left: &Condition,
        within: &WithinSpec,
        right: &Condition,
    ) -> Condition {
        let anchor_body = self.rewrite(right);
        let anchor_body = self.guard_mine(anchor_body);

        // Fast path — the negated-left idiom `!X since A` with a
        // mine-confined X: a foreign position cannot satisfy the pinned X,
        // so ¬X holds there vacuously and the native since already computes
        // the key-local semantics. (An unconfined X — e.g. a double
        // negation — falls through to the general encoding.)
        if let ConditionKind::Not { inner } = &left.kind
            && implies_mine(inner)
        {
            let l = self.rewrite(inner);
            return Condition {
                span,
                kind: ConditionKind::Since {
                    left: Box::new(not(span, l)),
                    within: within.clone(),
                    right: Box::new(anchor_body),
                },
            };
        }

        // General encoding: continuity over mine positions as a count
        // equality. `L` may bind variables in the original ∀-side; under
        // the count encoding those bindings stay internal to the count
        // body (grouped per outer correlation), which matches the ∀-side's
        // non-binding role in MFOTL since.
        let l = self.rewrite(left);
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
        let anchor = formerly(span, within.clone(), and(span, anchor_body, tp(span, &tj)));

        // The shared local range re-derivation for both count bodies: the
        // MFOTL `since` range **(tj, ti]** — strictly after the anchor `tj`, up
        // to and INCLUDING the decision point `ti`. The strict lower / non-
        // strict upper boundary (`tj < tk ∧ tk ≤ ti`) mirrors the native
        // interpreter exactly (`eval_since` checks `left` over `(j+1)..=i`);
        // changing either boundary's strictness silently misclassifies the
        // anchor position or the decision point, so keep them as written.
        let range = |tkv: &str| {
            vec![
                anchor.clone(),
                tp(span, &ti),
                cmp(span, CmpOp::Lt, &tj, tkv),
                cmp_le(span, tkv, &ti),
            ]
        };

        // n1 = count of ALL μ positions in the range: count tk_all where
        // formerly[0,W](μ ∧ tp(tk_all)) ∧ range.
        let mine_at = and(span, self.mu(span), tp(span, &tk_all));
        let mut n1_parts = vec![formerly(span, within.clone(), mine_at)];
        n1_parts.extend(range(&tk_all));
        let n1_count = count_agg(span, &tk_all, ands(span, n1_parts));

        // n2 = count of μ positions in the range that ALSO satisfy the left:
        // count tk_left where formerly[0,W]((μ ∧ L') ∧ tp(tk_left)) ∧ range.
        // Continuity ("left held at every μ position in (tj, ti]") is then
        // `n1 == n2` below.
        let mine_l_at = and(span, and(span, self.mu(span), l), tp(span, &tk_left));
        let mut n2_parts = vec![formerly(span, within.clone(), mine_l_at)];
        n2_parts.extend(range(&tk_left));
        let n2_count = count_agg(span, &tk_left, ands(span, n2_parts));

        let body = ands(
            span,
            vec![
                tp(span, &ti),
                anchor.clone(),
                cmp_agg_eq(span, n1_count, &n1),
                cmp_agg_eq(span, n2_count, &n2),
                cmp_vars(span, CmpOp::Eq, &n1, &n2),
            ],
        );

        let body = exists_long(span, &n2, body);
        let body = exists_long(span, &n1, body);
        let body = exists_tp_inner(span, &tj, body);
        exists_tp(span, &ti, body)
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

// ── small constructors ───────────────────────────────────────────────

fn and(span: Span, left: Condition, right: Condition) -> Condition {
    Condition {
        span,
        kind: ConditionKind::And {
            left: Box::new(left),
            right: Box::new(right),
        },
    }
}

fn ands(span: Span, parts: Vec<Condition>) -> Condition {
    let mut it = parts.into_iter();
    let first = it.next().expect("ands: non-empty");
    it.fold(first, |acc, p| and(span, acc, p))
}

fn not(span: Span, inner: Condition) -> Condition {
    Condition {
        span,
        kind: ConditionKind::Not {
            inner: Box::new(inner),
        },
    }
}

fn tp(span: Span, var: &str) -> Condition {
    Condition {
        span,
        kind: ConditionKind::Tp {
            var: crate::extension::temporal::ast::BinderSlot::Name(var.to_string()),
        },
    }
}

fn formerly(span: Span, within: WithinSpec, body: Condition) -> Condition {
    Condition {
        span,
        kind: ConditionKind::Formerly {
            within,
            body: Box::new(body),
        },
    }
}

fn cmp(span: Span, op: CmpOp, a: &str, b: &str) -> Condition {
    cmp_vars(span, op, a, b)
}

fn cmp_le(span: Span, a: &str, b: &str) -> Condition {
    cmp_vars(span, CmpOp::Le, a, b)
}

fn cmp_vars(span: Span, op: CmpOp, a: &str, b: &str) -> Condition {
    Condition {
        span,
        kind: ConditionKind::Comparison {
            op,
            left: Term::Var(a.to_string()),
            right: Term::Var(b.to_string()),
        },
    }
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
fn cmp_agg_eq(span: Span, agg: Term, n: &str) -> Condition {
    Condition {
        span,
        kind: ConditionKind::Comparison {
            op: CmpOp::Eq,
            left: agg,
            right: Term::Var(n.to_string()),
        },
    }
}

/// `count for (tk: Timepoint). where body` as a comparison operand.
fn count_agg(span: Span, over: &str, body: Condition) -> Term {
    Term::Agg(Box::new(AggExpr {
        span,
        kind: AggExprKind::Count {
            for_vars: vec![typed_tp(over)],
            body: Box::new(body),
        },
    }))
}

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

fn exists_tp(span: Span, var: &str, body: Condition) -> Condition {
    Condition {
        span,
        kind: ConditionKind::Exists {
            var: typed_tp(var),
            body: Box::new(body),
        },
    }
}

/// Alias of [`exists_tp`] for the inner (`tj`) binder — kept separate for
/// readability at call sites.
fn exists_tp_inner(span: Span, var: &str, body: Condition) -> Condition {
    exists_tp(span, var, body)
}

fn exists_long(span: Span, var: &str, body: Condition) -> Condition {
    Condition {
        span,
        kind: ConditionKind::Exists {
            var: typed_long(var),
            body: Box::new(body),
        },
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

    /// With no universal pins, `relativize_condition` is the identity — the
    /// authored leaf is returned unchanged. This is the structural counterpart
    /// to the "slice is the specification" claim the differential suites rely
    /// on: a schema without a qualifying pin keeps the global-trace semantics
    /// untouched. A regression that started rewriting
    /// unconditionally would fail here.
    #[test]
    fn empty_pins_relativize_is_identity() {
        // A non-trivial leaf: `previous within 1h Login{...} since ...` shapes
        // exercise the arms that DO transform under pins, so an accidental
        // rewrite would be visible.
        let span = Span::new(0, 0);
        let leaf = Condition {
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
        };

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

        let out = relativize_condition(&leaf, &derived, &pins);
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
        let cx = Cx {
            schema: &derived,
            pins: &pins,
            next_fresh: 0,
        };
        let mu = cx.mu(span);

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
}
