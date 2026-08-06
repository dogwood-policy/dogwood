//! Static binding checks for the temporal sub-language, run at parse time
//! after the `Condition` tree is built (and re-run post-expansion once
//! macro-supplied structure is concrete). Three checks live here:
//!
//! 1. **Aggregation `for`-domain binding.** In `sum a for (g1: T1), ….
//!    where S` (and the `count` analogue), the binder list names the
//!    aggregation domain; every variable free in `S` must be bound — by
//!    this aggregation's `for` list or an enclosing binder. A variable
//!    used in `S` but bound nowhere (e.g. `p` in `sum a for (a: Long),
//!    (t: Timepoint). where (W(user: p, amount: a) ∧ tp(t))`) is a static
//!    error: the projection onto `{a, t}` would leave `p` dangling.
//!    Conversely, every `for` variable must occur in `S` **and** be
//!    range-restricted by a positive atom of `S` (see
//!    [`check_aggregation`]) — the monitorable fragment requires the
//!    body to denote a finite relation over the `for` domain.
//!    Additionally, the *summand* (`a` in `sum a …`) must itself be one of
//!    the `for` binders — not merely in scope — because the sum is computed
//!    over the relation projected onto the `for` columns; a summand outside
//!    that projection would silently sum to 0.
//!
//! 2. **`exists` range-restriction safety (§7).** `exists (x: T). φ` is
//!    monitorable only if `x` is range-restricted by a positive atom in
//!    `φ`. See `check_exists_safe`.
//!
//! 3. **Leaf closedness.** A temporal leaf must be *closed*: every variable
//!    bound by an `exists` or a `for` list. See [`check_leaf_closed`].
//!
//! 4. **Evaluation-order demands.** Within `&&` chains, every consumer
//!    (filter, binding-equality aggregate operand, since-left) must follow
//!    the restrictors of the variables it consumes; nested chains inherit
//!    the accumulator at their position. See [`check_demands`].

use std::collections::BTreeSet;

use super::ast::{
    AggExpr, AggExprKind, BinderSlot, Condition, ConditionKind, NamedArg, Predicate, Term,
    TypedBinder,
};

/// Check every explicit aggregation in `cond` for unbound `for`-domain
/// variables. `bound` is the set of variables already in scope from
/// enclosing binders (empty at the top level).
pub fn check_condition(cond: &Condition, bound: &BTreeSet<String>) -> Result<(), String> {
    match &cond.kind {
        ConditionKind::And { left, right } => {
            check_condition(left, bound)?;
            check_condition(right, bound)
            // Evaluation-order (demands) checking for `&&` chains lives in
            // the separate seeded top-down pass `check_demands`, run at the
            // leaf level alongside this scoping pass — nested chains inherit
            // the accumulator at their position, so it cannot run per-`And`
            // here.
        }
        ConditionKind::Not { inner } => check_condition(inner, bound),
        // Internal-only disjunction (pin-relativization): check each branch
        // independently — branch bindings do not escape a disjunction, so
        // there is no cross-branch conjunct-order to enforce.
        ConditionKind::Or { left, right } => {
            check_condition(left, bound)?;
            check_condition(right, bound)
        }
        ConditionKind::Formerly { body, .. } | ConditionKind::Previous { body, .. } => {
            check_condition(body, bound)
        }
        ConditionKind::Since { left, right, .. } => {
            check_condition(left, bound)?;
            check_condition(right, bound)
        }
        // A field-injection refinement (pre-expansion; e.g. a direct-write
        // `P{a}{b}`): the injected fields hold terms, not nested
        // aggregations, so only the base needs the aggregation check.
        ConditionKind::Refine { base, .. } => check_condition(base, bound),
        // `exists (x: T). φ` — reject a reserved binder name, check `x` is
        // range-restricted by a positive atom in φ (§7 basic safety), then
        // recurse with `x` in scope so a nested aggregation sees it as bound.
        ConditionKind::Exists { var, body } => {
            reject_reserved_binder(&var.slot)?;
            check_exists_safe(var, body)?;
            let mut inner = bound.clone();
            inner.insert(var.name().to_string());
            check_condition(body, &inner)
        }
        // A comparison operand may be a *top-level* aggregate (its `for`
        // domain is checked). Any aggregate NOT at the operand top level
        // (nested in an array, etc.) is rejected — the
        // comparison-operand-only rule, enforced here rather than by the
        // grammar.
        ConditionKind::Comparison { left, right, .. } => {
            check_operand(left, bound)?;
            check_operand(right, bound)
        }
        // A predicate's field values are ordinary terms — an aggregate is
        // never allowed there.
        ConditionKind::Predicate(p) => {
            for arg in &p.args {
                reject_nested_agg(&arg.value)?;
            }
            Ok(())
        }
        // `tp(t)` binds the timepoint variable `t`; reject a reserved name.
        // No aggregation to descend.
        ConditionKind::Tp { var } => reject_reserved_binder(var),
        // A `Call` and a `SigilRef` are opaque to this check; the macro
        // expansion pass owns checking macro arguments and the resulting body.
        ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => Ok(()),
    }
}

/// Check a comparison operand: a *top-level* aggregate operand has its
/// `for` domain checked; any other term must contain no aggregate (an
/// aggregate is legal only as the immediate operand of a comparison,
/// enforced here). A macro sigil term is opaque (expansion
/// re-checks the substituted form).
fn check_operand(operand: &Term, bound: &BTreeSet<String>) -> Result<(), String> {
    match operand {
        Term::Agg(agg) => check_agg_expr(agg, bound),
        other => reject_nested_agg(other),
    }
}

/// Reject any aggregate appearing anywhere inside `term` — used for every
/// term position that is not a direct comparison operand (predicate args,
/// array elements, an operand that is itself a compound term).
fn reject_nested_agg(term: &Term) -> Result<(), String> {
    match term {
        Term::Agg(_) => Err(
            "an aggregate (`sum`/`count`) may appear only as the immediate operand \
             of a comparison, not as a predicate-argument value or nested in another \
             term"
                .to_string(),
        ),
        Term::Array(items) => {
            for t in items {
                reject_nested_agg(t)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Cedar's four reserved request-variable names. Dogwood rejects them as
/// binder / `for` / `tp` variable names: a bare `principal` / `resource` /
/// `context` term always denotes the request scope entity or context record
/// (never a bound variable), and `action` has no term-level meaning in a
/// temporal condition — so a binder of any of these names binds something the
/// term syntax can never read back. Reserving all four mirrors Cedar, where
/// they are reserved words.
const RESERVED_BINDER_NAMES: [&str; 4] = ["principal", "action", "resource", "context"];

/// Reject a binder whose (concrete) name is a Cedar reserved request variable.
/// A macro-sigil slot (`?p` / `$t`) has no concrete name yet — expansion
/// re-runs this check on the substituted form — so it is passed through.
fn reject_reserved_binder(slot: &BinderSlot) -> Result<(), String> {
    let BinderSlot::Name(name) = slot else {
        return Ok(());
    };
    if RESERVED_BINDER_NAMES.contains(&name.as_str()) {
        return Err(format!(
            "`{name}` is a reserved word and cannot be used as a binder name; \
             `principal`, `action`, `resource`, and `context` are the Cedar \
             request variables — rename the `exists` / `for` / `tp` variable"
        ));
    }
    Ok(())
}

/// §7 basic safety: `exists (x: T). φ` is monitorable only if `x` is
/// **range-restricted** — some *positive* atom in φ constrains it to
/// finitely many values. We accept iff `x` occurs range-restricted by a
/// predicate field `P{f:x}`, a `tp(x)`, or an equality `(term/agg) == x`
/// / `x == (term/agg)`, all in positive (non-negated) position; we reject
/// an unrestricted `x` (e.g. `exists (x). (0 < x && x < 2)`), and the
/// classic unsafe shape `exists (x). !φ` where `x` is restricted only
/// under the negation. Anything the basic analysis cannot prove safe is
/// conservatively rejected (reject-if-unsure).
///
/// A macro sigil (`?s` SigilRef / unresolved `Call`) makes the body opaque
/// — its concrete atoms exist only after expansion — so we accept here and
/// let the post-expansion re-check enforce safety on the substituted form
/// (mirrors `check_aggregation`'s sigil punt).
fn check_exists_safe(var: &TypedBinder, body: &Condition) -> Result<(), String> {
    // Only concrete binders are analyzable; a `?p`/`$t` slot is resolved
    // by expansion, which re-runs this check.
    let name = match &var.slot {
        BinderSlot::Name(n) => n.as_str(),
        BinderSlot::ParamRef(_) | BinderSlot::BinderRef(_) => return Ok(()),
    };
    if body_has_sigil(body) {
        return Ok(());
    }
    let mut restricted = BTreeSet::new();
    collect_range_restricted(body, &mut restricted);
    if restricted.contains(name) {
        Ok(())
    } else {
        Err(format!(
            "existential variable `{name}` is not range-restricted by any \
             positive atom in the `exists` body; bind it with a predicate \
             field (`P{{ f: {name} }}`), a `tp({name})`, or an equality \
             (`(count …) == {name}`)"
        ))
    }
}

/// Order-sensitive conjunction rule for safe-range monitorability (see the
/// Evaluation-order (demands) rule for safe-range monitorability (see
/// the temporal monitoring literature). Every
/// conjunct of a `&&` chain has two independent attributes:
///
///   * **RR(c)** — the variables it *produces* (range-restricts) for later
///     conjuncts ([`collect_range_restricted`]);
///   * **demands(c)** — the variables it *consumes*: bindings that must
///     already be in the environment when `c` evaluates for its value to be
///     meaningful.
///
/// In standard safe-range terms each conjunct is a conditional restriction fact
/// `demands(c) → RR(c)`; the standard formulation discharges such facts order-independently, but
/// this evaluator binds left-to-right, so the chain must be a valid
/// discharge order: walking left to right with an accumulator ρ, require
/// `demands(cᵢ) ⊆ ρ`, then `ρ ∪= RR(cᵢ)`. The demanding conjuncts:
///
///   * a **pure filter** (ordering comparison, non-binding `==`, guarded
///     negation `!φ`) demands all its free variables — a fact with an empty
///     head (the classical safe-range condition);
///   * a **binding equality** `x == v` produces `x` but demands the value
///     side's outward free variables — for an aggregate operand, the
///     variables free in its `where` body and not in its `for` list (a
///     *correlated* aggregate is only per-`u` when `u` is already bound);
///   * a **`since`** produces RR(anchor) but demands `fv(left) \ RR(anchor)`
///     (the standard `free(β) ⊆ free(γ)` side condition, relaxed to "or restricted
///     earlier"): the left is a per-step condition evaluated under the
///     anchor's bindings and cannot bind anything itself.
///
/// Demands propagate through non-chain wrappers (`formerly`/`previous`
/// bodies, an `exists` body minus its binder) because the evaluator passes
/// the environment straight through them; nested `&&` chains are checked
/// self-contained, **seeded with ρ at their position** — the evaluator
/// threads every binding produced by preceding conjuncts into nested
/// structure (`match_occurrences`' `And` arm), so an enclosing-chain
/// restrictor genuinely discharges a nested demand. An enclosing *binder*
/// is still never a seed (a binder restricts nothing by itself), and a
/// shadowing binder removes its name from the inherited seed (the inner
/// variable is a fresh one; mirrors the evaluator's binder shedding).
///
/// A chain containing an unresolved macro sigil is opaque and punts to the
/// post-expansion re-check.
pub fn check_demands(cond: &Condition) -> Result<(), String> {
    check_chain(cond, &BTreeSet::new())
}

/// Walk one `&&` chain (or a single conjunct) left-to-right with seed `rho`,
/// checking each conjunct's demands, descending into nested chains with the
/// accumulator at their position, then folding in the conjunct's RR.
fn check_chain(cond: &Condition, rho: &BTreeSet<String>) -> Result<(), String> {
    let conjuncts = flatten_and(cond);
    if conjuncts.iter().any(|c| body_has_sigil(c)) {
        return Ok(());
    }
    let mut rho = rho.clone();
    for c in &conjuncts {
        check_conjunct_demands(c, &rho)?;
        descend_nested_chains(c, &rho)?;
        collect_range_restricted(c, &mut rho);
    }
    Ok(())
}

/// Check the demands of a single (non-`And`) conjunct against `rho`, with a
/// kind-specific diagnostic. Recurses through non-chain wrappers; a nested
/// `&&` chain contributes no demand here (it is checked self-contained by
/// [`descend_nested_chains`]).
fn check_conjunct_demands(c: &Condition, rho: &BTreeSet<String>) -> Result<(), String> {
    match &c.kind {
        ConditionKind::Comparison {
            op: super::ast::CmpOp::Eq,
            left,
            right,
        } if eq_restricted_var(left, right).is_some() => {
            // A binding equality: demands = the value side's outward free
            // variables (for an aggregate: fv(body) \ for-list).
            let bound = eq_restricted_var(left, right).expect("guard");
            let value_side = if matches!(left, Term::Var(n) if *n == bound) {
                right
            } else {
                left
            };
            let mut needs = BTreeSet::new();
            collect_term_var(value_side, &mut needs);
            if let Some(unmet) = needs.iter().find(|v| !rho.contains(*v)) {
                return Err(format!(
                    "the equality binding `{bound}` reads `{unmet}` inside its \
                     aggregate operand (`{unmet}` is used in the aggregation body \
                     but not bound by its `for` list), and `{unmet}` is not \
                     range-restricted by a preceding conjunct; place the conjunct \
                     that binds `{unmet}` before the equality, widening the \
                     `exists` scope if needed"
                ));
            }
            Ok(())
        }
        ConditionKind::Comparison { left, right, .. } => {
            // Ordering / non-binding comparison: a pure filter — demands all
            // its (outward) free variables.
            let mut fv = BTreeSet::new();
            collect_term_var(left, &mut fv);
            collect_term_var(right, &mut fv);
            reject_unmet_filter_var(&fv, rho)
        }
        // A guarded negation is a pure filter over its free variables.
        ConditionKind::Not { inner } => {
            let mut fv = BTreeSet::new();
            collect_free(inner, &mut fv);
            reject_unmet_filter_var(&fv, rho)
        }
        // `left since right`: demands fv(left) \ RR(right) — the anchor's
        // bindings are in scope when the left is checked per step, but the
        // left itself binds nothing.
        ConditionKind::Since { left, right, .. } => {
            let mut left_fv = BTreeSet::new();
            collect_free(left, &mut left_fv);
            let mut anchor_rr = BTreeSet::new();
            collect_range_restricted(right, &mut anchor_rr);
            if let Some(unmet) = left_fv
                .iter()
                .find(|v| !anchor_rr.contains(*v) && !rho.contains(*v))
            {
                return Err(format!(
                    "variable `{unmet}` is used in the left operand of a `since` \
                     but is restricted neither by the `since` anchor (its right \
                     operand) nor by a preceding conjunct; the left of a `since` \
                     is a per-step condition and cannot bind `{unmet}` — restrict \
                     it in the anchor or in a conjunct before the `since`"
                ));
            }
            Ok(())
        }
        // Non-chain wrappers pass the environment straight through at
        // evaluation, so their (non-`And`) bodies' demands surface here.
        ConditionKind::Formerly { body, .. } | ConditionKind::Previous { body, .. } => {
            if matches!(body.kind, ConditionKind::And { .. }) {
                Ok(()) // its chain is checked, seeded, by descent
            } else {
                check_conjunct_demands(body, rho)
            }
        }
        ConditionKind::Exists { var, body } => {
            if matches!(body.kind, ConditionKind::And { .. }) {
                Ok(())
            } else {
                let mut seed = rho.clone();
                if let BinderSlot::Name(name) = &var.slot {
                    seed.remove(name);
                }
                check_conjunct_demands(body, &seed)
            }
        }
        // Predicates, `tp`, refinements produce only; internal `Or` branches
        // and unresolved calls/sigils are handled by descent / the punt.
        _ => Ok(()),
    }
}

fn reject_unmet_filter_var(fv: &BTreeSet<String>, rho: &BTreeSet<String>) -> Result<(), String> {
    if let Some(unbound) = fv.iter().find(|v| !rho.contains(*v)) {
        return Err(format!(
            "variable `{unbound}` is used in a filter (a comparison or \
             negation) that is not range-restricted by a preceding \
             conjunct; place a conjunct that binds `{unbound}` (a \
             predicate, `tp`, or a binding equality) before it"
        ));
    }
    Ok(())
}

/// Descend into the nested `&&` chains a conjunct wraps, seeding each with
/// the accumulator at this position (minus a shadowing binder's name). This
/// mirrors the evaluator's environment threading: bindings produced by
/// preceding conjuncts are visible inside nested structure.
fn descend_nested_chains(c: &Condition, rho: &BTreeSet<String>) -> Result<(), String> {
    match &c.kind {
        ConditionKind::And { .. } => check_chain(c, rho),
        ConditionKind::Or { left, right } => {
            check_chain(left, rho)?;
            check_chain(right, rho)
        }
        ConditionKind::Not { inner } => descend_nested_chains(inner, rho),
        ConditionKind::Formerly { body, .. } | ConditionKind::Previous { body, .. } => {
            check_chain(body, rho)
        }
        ConditionKind::Since { left, right, .. } => {
            // The left is evaluated per step under the anchor's bindings.
            let mut left_seed = rho.clone();
            collect_range_restricted(right, &mut left_seed);
            check_chain(left, &left_seed)?;
            check_chain(right, rho)
        }
        ConditionKind::Exists { var, body } => {
            let mut seed = rho.clone();
            if let BinderSlot::Name(name) = &var.slot {
                seed.remove(name);
            }
            check_chain(body, &seed)
        }
        // An aggregate operand's `where` body evaluates under the enclosing
        // environment MINUS the aggregate's own `for` binders — the evaluator
        // sheds them (`shed_for_binders`) so a shadowing `for` binder is a
        // fresh variable, exactly like an `exists` binder. Seed accordingly:
        // a `for` binder shadowing an enclosing restrictor must not inherit
        // its restriction (alpha-equivalence: renaming the binder must not
        // change acceptance). A binder is never a seed.
        ConditionKind::Comparison { left, right, .. } => {
            for t in [left, right] {
                if let Term::Agg(agg) = t {
                    match &agg.kind {
                        AggExprKind::Sum { for_vars, body, .. }
                        | AggExprKind::Count { for_vars, body } => {
                            let mut seed = rho.clone();
                            for v in for_vars {
                                if let BinderSlot::Name(name) = &v.slot {
                                    seed.remove(name);
                                }
                            }
                            check_chain(body, &seed)?;
                        }
                        AggExprKind::Call(_) => {}
                    }
                }
            }
            Ok(())
        }
        ConditionKind::Refine { base, .. } => descend_nested_chains(base, rho),
        ConditionKind::Predicate(_)
        | ConditionKind::Tp { .. }
        | ConditionKind::Call(_)
        | ConditionKind::SigilRef { .. } => Ok(()),
    }
}

/// Flatten a left-associative `&&` chain into its conjuncts, in order.
/// A non-`And` node is a single-element chain.
fn flatten_and(cond: &Condition) -> Vec<&Condition> {
    let mut out = Vec::new();
    fn rec<'a>(c: &'a Condition, out: &mut Vec<&'a Condition>) {
        if let ConditionKind::And { left, right } = &c.kind {
            rec(left, out);
            rec(right, out);
        } else {
            out.push(c);
        }
    }
    rec(cond, &mut out);
    out
}

/// Collect variables that a *positive* atom of `cond` range-restricts.
/// A negation contributes **nothing** — the ¬ labeling rule
/// discards every restriction fact, with no parity: a doubly-negated atom is
/// NOT a positive restrictor (the evaluator's negation is an opaque boolean
/// filter whose rows carry no bindings, so an even-depth "restrictor" never
/// materializes a column). Descends the safe positive structure (`&&`,
/// `formerly`/`previous`/`since`-right, nested `exists`, parens); a
/// disjunction or exotic nesting is not modeled, so a variable only
/// restricted there simply won't appear — yielding a conservative reject.
fn collect_range_restricted(cond: &Condition, out: &mut BTreeSet<String>) {
    match &cond.kind {
        ConditionKind::And { left, right } => {
            collect_range_restricted(left, out);
            collect_range_restricted(right, out);
        }
        // A negation restricts nothing, at any depth (the ¬ rule: all
        // facts are discarded, not parity-flipped). Do not descend.
        ConditionKind::Not { .. } => {}
        // A predicate field `P{ f: x }` positively restricts `x`.
        ConditionKind::Predicate(p) => {
            for arg in &p.args {
                if let Term::Var(name) = &arg.value {
                    out.insert(name.clone());
                }
            }
        }
        // `tp(x)` positively restricts `x` to the current timepoint.
        ConditionKind::Tp {
            var: BinderSlot::Name(name),
        } => {
            out.insert(name.clone());
        }
        // An equality with exactly one bare-variable operand restricts that
        // variable to the other operand's (ground/computed) value.
        ConditionKind::Comparison {
            op: super::ast::CmpOp::Eq,
            left,
            right,
        } => {
            if let Some(name) = eq_restricted_var(left, right) {
                out.insert(name);
            }
        }
        // `formerly`/`previous` bodies and a `since` right operand hold at a
        // scanned timepoint — a positive occurrence there restricts too.
        ConditionKind::Formerly { body, .. } | ConditionKind::Previous { body, .. } => {
            collect_range_restricted(body, out);
        }
        ConditionKind::Since { right, .. } => {
            collect_range_restricted(right, out);
        }
        // A nested `exists (x). φ` propagates the restrictors of its body
        // upward, minus the ones naming its own binder — the `∃x.φ` labeling
        // rule `∃x. φ : { B → h ∈ L | x ∉ B and x ≠ h }`:
        // the body's label `L` carries up, dropping only facts that mention the
        // quantified `x`. For our fact shape (bare `∅ → h` restricted vars, no
        // antecedents) that reduces to "drop the fact whose head is the inner
        // binder." Without this arm an outer binder whose only positive
        // restrictor sits inside a nested `exists` is wrongly rejected. (An
        // `exists` under a negation is never reached — the `Not` arm does not
        // descend.)
        ConditionKind::Exists { var, body } => {
            let mut inner = BTreeSet::new();
            collect_range_restricted(body, &mut inner);
            if let BinderSlot::Name(name) = &var.slot {
                inner.remove(name);
            }
            out.extend(inner);
        }
        // A refinement's base is the positive predicate; its injected
        // fields behave like predicate args.
        ConditionKind::Refine { base, fields, .. } => {
            collect_range_restricted(base, out);
            for arg in fields {
                if let Term::Var(name) = &arg.value {
                    out.insert(name.clone());
                }
            }
        }
        // Everything else contributes no positive restrictor.
        _ => {}
    }
}

/// If exactly one operand of an equality is a bare `Var` and the other is
/// a resolvable restrictor (a non-variable, non-wildcard term, e.g. a
/// literal, context field, entity, or aggregate), return that variable's
/// name. A wildcard is NOT a resolvable value side: `x == *` never binds at
/// evaluation (a wildcard resolves to no value), so treating it as a
/// restrictor would validate a permanently-false guard.
fn eq_restricted_var(left: &Term, right: &Term) -> Option<String> {
    let bare_var = |t: &Term| match t {
        Term::Var(n) => Some(n.clone()),
        _ => None,
    };
    // A bare var restricts nothing on its own; a wildcard resolves to no
    // value; anything else is a ground/computed value.
    let is_restrictor = |t: &Term| !matches!(t, Term::Var(_) | Term::Wildcard);
    match (bare_var(left), bare_var(right)) {
        (Some(n), None) if is_restrictor(right) => Some(n),
        (None, Some(n)) if is_restrictor(left) => Some(n),
        _ => None,
    }
}

/// Does the condition contain a still-unresolved macro sigil or call,
/// making its concrete atoms unavailable until expansion?
fn body_has_sigil(cond: &Condition) -> bool {
    match &cond.kind {
        ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => true,
        ConditionKind::And { left, right }
        | ConditionKind::Or { left, right }
        | ConditionKind::Since { left, right, .. } => body_has_sigil(left) || body_has_sigil(right),
        ConditionKind::Not { inner }
        | ConditionKind::Formerly { body: inner, .. }
        | ConditionKind::Previous { body: inner, .. }
        | ConditionKind::Exists { body: inner, .. } => body_has_sigil(inner),
        // A refinement's injected field values are terms — a sigil can sit
        // there (`?s{ f: ?v }` pre-expansion), not just in the base.
        ConditionKind::Refine { base, fields, .. } => {
            body_has_sigil(base) || fields.iter().any(|a| term_has_sigil(&a.value))
        }
        ConditionKind::Comparison { left, right, .. } => {
            term_has_sigil(left) || term_has_sigil(right)
        }
        // Defensive: predicate args and a `tp` binder slot can carry sigils
        // in macro-body positions; should such a shape ever reach a leaf
        // check (the grammar does not produce it today), it must punt to the
        // post-expansion re-run rather than be analyzed with phantom names.
        ConditionKind::Predicate(p) => p.args.iter().any(|a| term_has_sigil(&a.value)),
        ConditionKind::Tp { var } => {
            matches!(var, BinderSlot::ParamRef(_) | BinderSlot::BinderRef(_))
        }
    }
}

/// Does a term carry an unresolved macro sigil, or an aggregate whose body
/// does? (An aggregate is a term now.)
fn term_has_sigil(term: &Term) -> bool {
    match term {
        Term::ParamRef(_) | Term::BinderRef(_) => true,
        Term::Array(items) => items.iter().any(term_has_sigil),
        Term::Agg(agg) => match &agg.kind {
            AggExprKind::Call(_) => true,
            AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => body_has_sigil(body),
        },
        _ => false,
    }
}

/// Check one aggregation expression (the value half of a `let`). A
/// `Call` (unresolved macro invocation) is opaque to this check — macro
/// expansion is the layer that validates its arguments and produced
/// body.
fn check_agg_expr(value: &AggExpr, bound: &BTreeSet<String>) -> Result<(), String> {
    match &value.kind {
        AggExprKind::Sum {
            bound_var,
            for_vars,
            body,
        } => check_aggregation(Some(bound_var), for_vars, body, bound),
        AggExprKind::Count { for_vars, body } => check_aggregation(None, for_vars, body, bound),
        AggExprKind::Call(_) => Ok(()),
    }
}

/// Check one aggregation node: require that the summand (`bound_var`) is one of
/// this aggregation's own `for_vars`, and that every free variable of `body` is
/// bound by `for_vars` or an enclosing binder; then recurse into `body` (with
/// the `for` vars in scope).
///
/// A `for` list that still contains a macro sigil ([`BinderSlot::ParamRef`]
/// / [`BinderSlot::BinderRef`]) is opaque to this check — its concrete
/// name only exists after expansion, so we conservatively accept and let
/// expansion run the check on the substituted form.
fn check_aggregation(
    bound_var: Option<&BinderSlot>,
    for_vars: &[TypedBinder],
    body: &Condition,
    bound: &BTreeSet<String>,
) -> Result<(), String> {
    // If either the bound var or any `for` element is still a sigil, the
    // body's free vars include sigils too; punt to expansion.
    let has_sigil = matches!(
        bound_var,
        Some(BinderSlot::ParamRef(_) | BinderSlot::BinderRef(_))
    ) || for_vars
        .iter()
        .any(|v| matches!(v.slot, BinderSlot::ParamRef(_) | BinderSlot::BinderRef(_)));
    if has_sigil {
        return Ok(());
    }

    // Reject a reserved request-variable name as a `for` domain binder.
    for v in for_vars {
        reject_reserved_binder(&v.slot)?;
    }

    // Scope visible to `body`: enclosing binders + this `for` list. All
    // slots are concrete names at this point.
    let mut inner = bound.clone();
    for v in for_vars {
        inner.insert(v.name().to_string());
    }

    // The summed variable must be one of *this* aggregation's `for` binders —
    // not merely in scope. `eval_agg_expr` projects the match relation onto the
    // `for_vars` columns and *then* sums the summand's column; a summand outside
    // `for_vars` (e.g. bound by an enclosing `exists`) has no column in the
    // projected relation, so the sum silently evaluates to 0. Requiring `for`
    // membership (rather than the wider `inner` scope) rejects that trap.
    if let Some(bv) = bound_var {
        let bv_name = bv.name();
        let in_for_list = for_vars.iter().any(|v| v.name() == bv_name);
        if !in_for_list {
            return Err(format!(
                "aggregation sums `{bv_name}`, which is not one of its `for` \
                 binders ({}); the summed variable must appear in the `for` \
                 list (the sum is computed over the `for` columns)",
                fmt_for_vars(for_vars)
            ));
        }
    }

    // Every free variable of the body must be bound.
    let mut free = BTreeSet::new();
    collect_free(body, &mut free);
    if let Some(unbound) = free.iter().find(|v| !inner.contains(*v)) {
        return Err(format!(
            "variable `{unbound}` is used in the aggregation body but is \
             bound by neither the `for` list ({}) nor an enclosing binder; \
             add it to the `for` list",
            fmt_for_vars(for_vars)
        ));
    }

    // The converse: every `for` (group-by) variable must OCCUR in the body.
    // Monitorability well-formedness (`z̄ = fv(ψ) \ ḡ`, which presupposes
    // `ḡ ⊆ fv(ψ)`): a group-by variable absent from the body's free variables
    // groups over an unbounded domain — every domain element forms the same
    // (non-empty) group, so the aggregation's result relation is infinite and
    // the formula is not monitorable. `collect_free` counts a `tp(t)` binder and
    // predicate/comparison/summand occurrences, so every legitimate `for`-var
    // (including a `Timepoint` bound only via `tp(t)`, and a `Sum` summand used
    // as `P{ f: a }`) appears in `free`; only a genuinely unused group key is
    // rejected here.
    for v in for_vars {
        let name = v.name();
        if !free.contains(name) {
            return Err(format!(
                "`for`-variable `{name}` does not occur in the aggregation body \
                 ({}); a group-by variable must be used in the `where` body, \
                 otherwise the grouping ranges over an unbounded domain",
                fmt_for_vars(for_vars)
            ));
        }
    }

    // Occurrence is necessary but NOT sufficient: every `for` variable must be
    // **range-restricted** by a positive atom of the body, exactly like an
    // `exists` binder (the monitorable fragment requires the aggregation
    // body to denote a finite relation over its `for` domain). A variable
    // occurring only under a negation, or only in the left operand of a
    // `since` (the per-step filter; only the anchor restricts), denotes an
    // infinite relation — or one that does not range over the variable at all
    // — and evaluation would silently degrade to a 0/1 witness count with no
    // such column (a `sum` to 0).
    let mut restricted = BTreeSet::new();
    collect_range_restricted(body, &mut restricted);
    for v in for_vars {
        let name = v.name();
        if !restricted.contains(name) {
            return Err(format!(
                "aggregation `for`-variable `{name}` is not range-restricted by \
                 any positive atom in the `where` body; bind it with a predicate \
                 field (`P{{ f: {name} }}`), a `tp({name})`, or an equality \
                 (`(count …) == {name}`) — an occurrence under a negation or in \
                 the left operand of a `since` does not restrict"
            ));
        }
    }

    // Recurse with the for-domain in scope.
    check_condition(body, &inner)
}

/// Collect the free temporal variables used in a condition: every
/// `Term::Var` (in predicate args, comparison operands, arrays) and every
/// `tp(t)` variable. Descends through boolean/temporal structure; a binder
/// (`exists`, an aggregation `for` list) removes its own name from what its
/// body exposes upward, so the result is the standard free-variable set.
fn collect_free(cond: &Condition, out: &mut BTreeSet<String>) {
    match &cond.kind {
        ConditionKind::And { left, right } => {
            collect_free(left, out);
            collect_free(right, out);
        }
        // Internal-only disjunction: free variables of both branches.
        ConditionKind::Or { left, right } => {
            collect_free(left, out);
            collect_free(right, out);
        }
        ConditionKind::Not { inner } => collect_free(inner, out),
        ConditionKind::Formerly { body, .. } | ConditionKind::Previous { body, .. } => {
            collect_free(body, out);
        }
        ConditionKind::Since { left, right, .. } => {
            collect_free(left, out);
            collect_free(right, out);
        }
        ConditionKind::Predicate(p) => collect_pred_vars(p, out),
        // A refinement contributes the free vars of its base plus the vars
        // used in each injected field's term (they behave like predicate
        // args). Direct-write `P{…}{…}` can reach this pass; a macro-body
        // `?s{…}` is opaque (see the SigilRef arm) until expansion.
        ConditionKind::Refine { base, fields, .. } => {
            collect_free(base, out);
            for arg in fields {
                collect_arg_var(arg, out);
            }
        }
        ConditionKind::Comparison { left, right, .. } => {
            collect_term_var(left, out);
            collect_term_var(right, out);
        }
        ConditionKind::Tp { var } => {
            if let BinderSlot::Name(name) = var {
                out.insert(name.clone());
            }
            // Sigil slots are opaque to this pass — see check_aggregation.
        }
        // A nested `exists (x: T). body` binds `x` within its body; the
        // variables it exposes upward are the free vars of its body minus
        // its own binder. (For the single-level forms the migration emits
        // this does not arise, but be correct for hand-written nesting.)
        ConditionKind::Exists { var, body } => {
            let mut inner = BTreeSet::new();
            collect_free(body, &mut inner);
            if let BinderSlot::Name(name) = &var.slot {
                inner.remove(name);
            }
            out.extend(inner);
        }
        // Unresolved macro call or sigil-condition — opaque to this pass.
        ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => {}
    }
}

fn collect_pred_vars(p: &Predicate, out: &mut BTreeSet<String>) {
    for arg in &p.args {
        collect_arg_var(arg, out);
    }
}

fn collect_arg_var(arg: &NamedArg, out: &mut BTreeSet<String>) {
    collect_term_var(&arg.value, out);
}

fn collect_term_var(term: &Term, out: &mut BTreeSet<String>) {
    match term {
        Term::Var(name) => {
            out.insert(name.clone());
        }
        Term::Array(items) => {
            for t in items {
                collect_term_var(t, out);
            }
        }
        // An aggregate term binds its `for` variables over its own `where`
        // body; what it exposes upward are the body's free variables MINUS
        // the `for` list — the standard binder rule. (Exposing the `for`
        // names themselves was a bug: it made an enclosing scope responsible
        // for the aggregate's own binders, over-rejecting correlated
        // aggregates in filter position and blinding closedness to the real
        // free variables.) A `for` slot still carrying a macro sigil has no
        // concrete name; expansion re-runs these checks on the substituted
        // form, so it is skipped here.
        Term::Agg(agg) => match &agg.kind {
            AggExprKind::Sum { for_vars, body, .. } | AggExprKind::Count { for_vars, body } => {
                let mut inner = BTreeSet::new();
                collect_free(body, &mut inner);
                for v in for_vars {
                    if let BinderSlot::Name(name) = &v.slot {
                        inner.remove(name);
                    }
                }
                out.extend(inner);
            }
            AggExprKind::Call(_) => {}
        },
        // Literals, entities, context fields, wildcards, and macro sigils
        // bind/use no temporal domain variable in the post-expansion sense.
        _ => {}
    }
}

fn fmt_for_vars(vars: &[TypedBinder]) -> String {
    vars.iter()
        .map(|v| match &v.slot {
            BinderSlot::Name(s) => s.clone(),
            BinderSlot::ParamRef(p) => format!("?{p}"),
            BinderSlot::BinderRef(b) => format!("${b}"),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Closedness of a temporal *leaf*: every variable occurring in the condition
/// must be bound by an `exists` binder or an aggregation `for` list. A free
/// variable at the leaf level is rejected: a leaf is evaluated **boolean-ly**
/// at the decision point with no implicit existential closure, so an accepted
/// free variable silently evaluates as an always-false (or mis-correlated)
/// guard — the checked safe-range semantics and the computed verdict diverge.
///
/// Runs both at parse time (`Temporal::parse`) and post-expansion. No sigil
/// punt is needed: an unresolved macro `Call` contributes no visible
/// variables (its internals are checked by the post-expansion re-run), and
/// macro hygiene guarantees expansion can never *bind* a call-site variable —
/// substitution happens at the `Call` node and macro-internal binders are
/// gensym-renamed — so a variable free here is necessarily still free after
/// expansion, and rejecting it at parse time is sound (and earlier).
pub fn check_leaf_closed(cond: &Condition) -> Result<(), String> {
    let mut free = BTreeSet::new();
    collect_free(cond, &mut free);
    if let Some(name) = free.iter().next() {
        return Err(format!(
            "variable `{name}` is free in this temporal condition (bound by no \
             `exists` binder or aggregation `for` list); a temporal condition \
             must be closed — wrap it as `exists ({name}: <type>). (…)`, or \
             use `*` to match any value"
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    //! §7 basic range-restriction safety for `exists`. Each case parses a
    //! condition and runs `check_condition` (the pass `Temporal::parse`
    //! invokes) at the empty top-level scope.

    use super::*;
    use crate::extension::temporal::parse::parse_condition;

    fn check(body: &str) -> Result<(), String> {
        let cond = parse_condition(body).unwrap_or_else(|e| panic!("parse `{body}` failed: {e}"));
        check_condition(&cond, &BTreeSet::new())?;
        check_demands(&cond)
    }

    #[test]
    fn exists_restricted_by_predicate_field_is_safe() {
        // `x` occurs as a predicate-field value — a positive restrictor.
        check(r#"exists (x: String). Drupe::Action::"Login"::request{ input.user: x }"#)
            .expect("predicate field restricts x");
    }

    #[test]
    fn exists_restricted_by_tp_is_safe() {
        check(r#"exists (t: Timepoint). tp(t)"#).expect("tp restricts t");
    }

    #[test]
    fn exists_restricted_by_agg_equality_is_safe() {
        // `(count …) == n` restricts `n` to the aggregate's value — the
        // shape the `let`-migration emits.
        check(
            r#"exists (n: Long). ((count for (t: Timepoint). where (Drupe::Action::"Login"::request{} && tp(t))) == n && n > 0)"#,
        )
        .expect("agg equality restricts n");
    }

    #[test]
    fn agg_for_var_absent_from_body_is_rejected() {
        // `x` is a `for` (group-by) variable that never occurs in the body:
        // grouping over an unbounded domain (monitorability well-formedness,
        // `ḡ ⊆ fv(ψ)`). Must be rejected.
        let e = check(
            r#"exists (n: Long). ((count for (x: String), (t: Timepoint). where (Drupe::Action::"Login"::request{} && tp(t))) == n && n >= 1)"#,
        )
        .expect_err("a for-var absent from the body must be rejected");
        assert!(e.contains("does not occur in the aggregation body"), "{e}");
    }

    #[test]
    fn agg_for_var_used_positively_is_safe() {
        // The converse-check must NOT over-reject: `x` used in a predicate field,
        // `t` bound via `tp(t)` — both occur in the body's free vars.
        check(
            r#"exists (n: Long). ((count for (x: String), (t: Timepoint). where (Drupe::Action::"Login"::request{ input.user: x } && tp(t))) == n && n >= 1)"#,
        )
        .expect("a for-var used positively in the body is safe");
    }

    #[test]
    fn agg_sum_summand_for_var_is_safe() {
        // A `Sum` summand `a` occurs as a predicate field (`input.amount: a`), so
        // it is in the body's free vars — the converse check must accept it.
        check(
            r#"exists (s: Long). ((sum a for (a: Long), (t: Timepoint). where (Drupe::Action::"Transfer"::request{ input.amount: a } && tp(t))) == s && s >= 1)"#,
        )
        .expect("a Sum summand used as a predicate field is safe");
    }

    #[test]
    fn exists_restricted_by_literal_equality_is_safe() {
        // An equality against a ground term also restricts.
        check(r#"exists (x: Long). (x == 5)"#).expect("literal equality restricts x");
    }

    #[test]
    fn exists_with_no_restrictor_is_rejected() {
        // `0 < x && x < 2` restricts `x` by neither a predicate field, a
        // `tp`, nor an equality — infinite domain, unsafe.
        let e = check(r#"exists (x: Long). (0 < x && x < 2)"#)
            .expect_err("unrestricted x must be rejected");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    #[test]
    fn exists_restricted_only_under_negation_is_rejected() {
        // The classic unsafe shape: `x` occurs only under a negation, so
        // it is not positively restricted.
        let e = check(r#"exists (x: String). !Drupe::Action::"Login"::request{ input.user: x }"#)
            .expect_err("restrictor under negation does not count");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    #[test]
    fn negation_outside_a_closed_exists_is_safe() {
        // `!exists (x). φ` — negation OUTSIDE a safe (closed) existential
        // is fine; the inner `exists` is self-contained (x restricted by a
        // predicate field).
        check(r#"!exists (x: String). Drupe::Action::"Login"::request{ input.user: x }"#)
            .expect("negation outside a closed exists is safe");
    }

    #[test]
    fn exists_restricted_under_formerly_is_safe() {
        // A positive occurrence inside a `formerly` body still restricts.
        check(
            r#"exists (x: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: x }"#,
        )
        .expect("predicate field under formerly restricts x");
    }

    #[test]
    fn exists_restricted_by_predicate_under_nested_exists_is_safe() {
        // the `∃x.φ` labeling rule: the inner `exists (g)` body
        // restricts BOTH `v` and `g`; the inner binder propagates `∅ → v`
        // (which does not mention `g`) up to the outer `exists (v)`. So the
        // outer `v` is range-restricted even though its only positive
        // restrictor sits inside the nested `exists`. This is the minimal
        // repro of the "collector does not descend into a nested exists" gap.
        check(
            r#"exists (v: String). exists (g: String). Drupe::Action::"Transfer"::request{ input.user: v, input.recipient: g }"#,
        )
        .expect("nested exists propagates v's restrictor up to the outer binder");
    }

    #[test]
    fn exists_with_only_inner_binder_restricted_is_rejected() {
        // Negative control: the nested `exists (g)` restricts only `g` (via
        // `input.recipient: g`); `v` occurs nowhere positive. After dropping
        // the inner binder's own fact, nothing restricts `v`, so the outer
        // `exists (v)` is correctly rejected — the fix must not over-permit.
        let e = check(
            r#"exists (v: String). exists (g: String). Drupe::Action::"Transfer"::request{ input.recipient: g }"#,
        )
        .expect_err("v is unrestricted even after descending the nested exists");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    // ─── Nested-exists range restriction: acceptance-boundary battery ──────
    //
    // These pin the exact boundary the nested-`exists` fix (the `Exists` arm of
    // `collect_range_restricted`) draws — the corner cases
    // beyond the minimal repro/control above. Each safe case is paired with a
    // near-miss that must stay rejected, so the fix cannot silently over-permit.

    #[test]
    fn nested_exists_restrictor_under_formerly_is_safe() {
        // The outer binder's restrictor sits inside a nested `exists` AND under
        // a `formerly` — exercises the Formerly→Exists→Predicate descent chain.
        check(
            r#"exists (v: String). exists (g: String). formerly within 1h Drupe::Action::"Transfer"::request{ input.user: v, input.recipient: g }"#,
        )
        .expect("v restricted by a predicate under formerly inside a nested exists");
    }

    #[test]
    fn nested_exists_restrictor_under_since_right_is_safe() {
        // A `since` propagates its RIGHT operand's restrictors (the anchor). An
        // outer binder restricted by the since-right, inside a nested exists,
        // must be accepted.
        check(
            r#"exists (v: String). exists (g: String). (Drupe::Action::"Ping"::request{} since within 1h Drupe::Action::"Transfer"::request{ input.user: v, input.recipient: g })"#,
        )
        .expect("v restricted by the since-right operand inside a nested exists");
    }

    #[test]
    fn nested_exists_restrictor_only_in_since_left_is_rejected() {
        // Near-miss for the above: `since` does NOT propagate its LEFT operand's
        // restrictors (the left is a per-step filter, not a range-restrictor).
        // Here `v` occurs only in the since-LEFT, so it stays unrestricted.
        let e = check(
            r#"exists (v: String). exists (g: String). (Drupe::Action::"Transfer"::request{ input.user: v } since within 1h Drupe::Action::"Ping"::request{ input.recipient: g })"#,
        )
        .expect_err("a since-left occurrence does not range-restrict v");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    #[test]
    fn triple_nested_exists_outer_restricted_innermost_is_safe() {
        // Two levels of nesting between the outer binder and its restrictor: the
        // `∅ → v` fact must propagate up through BOTH inner `exists` (neither
        // mentions `v`), reaching the outermost binder.
        check(
            r#"exists (v: String). exists (g: String). exists (h: String). Drupe::Action::"Transfer"::request{ input.user: v, input.recipient: g, input.doc: h }"#,
        )
        .expect("v's restrictor propagates up through two nested exists");
    }

    #[test]
    fn nested_exists_binder_shadowing_is_rejected() {
        // Shadowing: the inner `exists (v)` rebinds `v`, so the atom's `v`
        // refers to the INNER binder. Dropping the inner binder's own fact
        // leaves nothing for the OUTER `exists (v)` — correctly rejected. (Guards
        // that the name-based removal does not wrongly credit the outer binder
        // with a shadowed occurrence's restrictor.)
        let e = check(
            r#"exists (v: String). exists (v: String). Drupe::Action::"Transfer"::request{ input.user: v }"#,
        )
        .expect_err("the outer v is shadowed and unrestricted");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    #[test]
    fn shadowing_outer_binder_restricted_by_sibling_conjunct_is_safe() {
        // Shadowing that DOES validate: the outer `exists (v)` is range-
        // restricted by its OWN conjunct (`Login{ input.user: v }`), while the
        // OTHER conjunct is a self-contained `exists (v)` that shadows `v` and is
        // itself safe (inner `v` restricted by `Transfer{ input.user: v }`).
        // Both `exists` are independently safe, so the whole formula is accepted.
        // This guards that the inner `exists`'s name-based `remove(v)` operates on
        // its own local recursion and cannot strip the outer `v`'s restrictor that
        // the enclosing `&&` collected from the sibling `Login` conjunct.
        check(
            r#"exists (v: String). (Drupe::Action::"Login"::request{ input.user: v } && exists (v: String). Drupe::Action::"Transfer"::request{ input.user: v })"#,
        )
        .expect("outer v restricted by a sibling conjunct; inner shadowing exists is itself safe");
    }

    #[test]
    fn shadowing_outer_restricted_but_inner_unrestricted_is_rejected() {
        // The other direction: the OUTER `exists (v)` is properly restricted (by
        // `Login{ input.user: v }`), but the shadowing INNER `exists (v)` is NOT
        // range-restricted — its body `Ping{}` mentions `v` nowhere. Each `exists`
        // must be independently safe, so the formula is rejected on the inner
        // binder even though the outer one is fine. (Guards that a restricted
        // outer binder does not mask an unsafe shadowing inner `exists`.)
        let e = check(
            r#"exists (v: String). (Drupe::Action::"Login"::request{ input.user: v } && exists (v: String). Drupe::Action::"Ping"::request{})"#,
        )
        .expect_err("the inner shadowing exists is unrestricted");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    #[test]
    fn nested_exists_restrictor_via_conjunct_inside_inner_is_safe() {
        // The outer binder is restricted by one conjunct that lives inside the
        // nested exists's `&&` body; the inner binder is restricted by another.
        // Both must be accepted (the And arm inside the Exists body is reached
        // via the new Exists→And descent).
        check(
            r#"exists (v: String). exists (g: String). (Drupe::Action::"Login"::request{ input.user: v } && Drupe::Action::"Transfer"::request{ input.recipient: g })"#,
        )
        .expect("v restricted by a conjunct inside the nested exists body");
    }

    #[test]
    fn nested_exists_restrictor_only_under_negation_is_rejected() {
        // A restrictor under a negation is NOT positive: the RR collector
        // does not descend into `!` at all (the ¬-rule discards all
        // facts), so `v`'s only occurrence — under the `!` inside the nested
        // exists — contributes no restrictor.
        let e = check(
            r#"exists (v: String). exists (g: String). (Drupe::Action::"Transfer"::request{ input.recipient: g } && !Drupe::Action::"Login"::request{ input.user: v })"#,
        )
        .expect_err("v occurs only under negation inside the nested exists");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    // ─── Aggregate comparison-operand-only rule (validation) ───────

    #[test]
    fn aggregate_as_comparison_operand_is_accepted() {
        // The legal position: an aggregate directly as a comparison operand.
        check(
            r#"0 < count for (t: Timepoint). where (Drupe::Action::"Login"::request{} && tp(t))"#,
        )
        .expect("aggregate as a comparison operand is allowed");
    }

    #[test]
    fn aggregate_in_predicate_arg_is_rejected() {
        // An aggregate as a predicate-field value is not a comparison
        // operand — rejected by validation (the grammar admits it as a
        // term, but validation forbids it here).
        let e = check(
            r#"Drupe::Action::"Login"::request{ input.amount: count for (t: Timepoint). where tp(t) }"#,
        )
        .expect_err("aggregate in a predicate arg must be rejected");
        assert!(
            e.contains("only as the immediate operand of a comparison"),
            "{e}"
        );
    }

    #[test]
    fn aggregate_nested_in_array_operand_is_rejected() {
        // An aggregate inside an array (even though the array is a
        // comparison operand) is not the *immediate* operand — rejected.
        let e = check(r#"[count for (t: Timepoint). where tp(t)] == x"#)
            .expect_err("aggregate nested in an array operand must be rejected");
        assert!(
            e.contains("only as the immediate operand of a comparison"),
            "{e}"
        );
    }

    // ─── Order-sensitive conjunction rule ───────────────────────────
    //
    // An ordering comparison (`<`, `<=`, `>`, `>=`) and a guarded negation
    // are pure *filters*: they range-restrict nothing. They are monitorable
    // only as a conjunct whose variables are already range-restricted by a
    // *preceding* conjunct in the same `&&` chain (the left restricts the
    // right). A filter written before its restrictor — or with no
    // restrictor — is rejected.

    #[test]
    fn ordering_filter_after_restrictor_is_accepted() {
        // Restrictor-first: the predicate binds `a`, then `a > 100` filters.
        check(r#"exists (a: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a } && a > 100)"#)
            .expect("predicate restricts a before the filter → monitorable");
    }

    #[test]
    fn ordering_filter_before_restrictor_is_rejected() {
        // Filter-first: `a > 100` precedes the predicate that binds `a`.
        // Rejected; the author must write the restrictor first.
        let e = check(r#"exists (a: Long). (a > 100 && formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a })"#)
            .expect_err("filter before its restrictor must be rejected");
        assert!(
            e.contains("range-restricted by a preceding conjunct"),
            "{e}"
        );
    }

    #[test]
    fn ordering_filter_between_restrictors_is_accepted() {
        // `P{a} && a > 100 && Q` — the filter's var `a` is restricted by the
        // preceding `P{a}`, so it is monitorable regardless of the later Q.
        check(r#"exists (a: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a } && a > 100 && formerly within 1h Drupe::Action::"Login"::request{})"#)
            .expect("filter restricted by a preceding conjunct → monitorable");
    }

    #[test]
    fn guarded_negation_after_restrictor_is_accepted() {
        // `Login{u} && !Logout{u}` — the negation's free var `u` is
        // restricted by the preceding Login (guarded negation).
        check(r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && !formerly within 1h Drupe::Action::"Logout"::request{ input.user: u })"#)
            .expect("guarded negation with a preceding restrictor → monitorable");
    }

    #[test]
    fn negation_before_restrictor_is_rejected() {
        // `!Logout{u} && Login{u}` — the negation precedes the restrictor of
        // its free var `u`. Rejected (the left operand restricts nothing and
        // has free vars).
        let e = check(r#"exists (u: String). (!formerly within 1h Drupe::Action::"Logout"::request{ input.user: u } && formerly within 1h Drupe::Action::"Login"::request{ input.user: u })"#)
            .expect_err("negation before its restrictor must be rejected");
        assert!(
            e.contains("range-restricted by a preceding conjunct"),
            "{e}"
        );
    }

    #[test]
    fn migration_shape_agg_eq_then_filter_is_accepted() {
        // The `let`-migration output `(agg) == n && n > 0`: the equality
        // binds `n` (a restrictor), then `n > 0` filters. Must stay accepted.
        check(r#"exists (n: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp(t)))) == n && n > 0)"#)
            .expect("agg-equality restricts n before the filter → monitorable");
    }

    // ─── Reserved request-variable names (Cedar parity) ─────────────
    //
    // `principal`, `action`, `resource`, and `context` are Cedar's four
    // reserved request variables. Dogwood must reject them as `exists` /
    // aggregation-`for` / `tp` binder names with a clear "reserved word"
    // diagnostic. A bare `principal` / `resource` / `context` term always
    // denotes the scope entity / context record — never a bound variable — so
    // a binder of that name binds something term-position syntax can never
    // read back. (`action` has no term meaning in temporal conditions today;
    // reserving it is preventive Cedar parity.)
    //
    // TDD: the reserved-word rule is not yet implemented, so these fail now
    // (three of the four shapes are currently *accepted*, and the fourth,
    // `exists (principal: String). P{ … principal }`, is rejected only
    // accidentally with the misleading "not range-restricted" message). They
    // go green when the validator learns to reject the reserved names.

    /// A reserved name must be rejected with a "reserved word" diagnostic — not
    /// the accidental "not range-restricted" message it may currently produce.
    fn assert_reserved(body: &str) {
        let e = check(body)
            .err()
            .unwrap_or_else(|| panic!("reserved-name binder must be rejected: `{body}`"));
        assert!(
            e.contains("reserved"),
            "expected a `reserved word` diagnostic for `{body}`, got: {e}"
        );
    }

    #[test]
    fn rejects_principal_as_exists_binder() {
        assert_reserved(
            r#"exists (principal: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: principal }"#,
        );
    }

    #[test]
    fn rejects_resource_as_exists_binder() {
        assert_reserved(
            r#"exists (resource: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: resource }"#,
        );
    }

    #[test]
    fn rejects_context_as_exists_binder() {
        assert_reserved(
            r#"exists (context: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: context }"#,
        );
    }

    #[test]
    fn rejects_action_as_exists_binder() {
        assert_reserved(
            r#"exists (action: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: action }"#,
        );
    }

    #[test]
    fn rejects_principal_as_tp_binder() {
        // `tp` binds a Timepoint variable; a reserved name is rejected there.
        // The enclosing `exists` binds a *different* name (`t`, range-restricted
        // by `tp(t)`), so it is the `Tp` arm — not the `exists` arm — that must
        // reject `tp(principal)`.
        assert_reserved(r#"exists (t: Timepoint). (tp(t) && tp(principal))"#);
    }

    #[test]
    fn rejects_resource_as_tp_binder() {
        assert_reserved(r#"exists (t: Timepoint). (tp(t) && tp(resource))"#);
    }

    #[test]
    fn rejects_context_as_for_binder() {
        // A reserved name as an aggregation `for` domain variable.
        assert_reserved(
            r#"exists (n: Long). ((count for (context: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp(context)))) == n && n > 0)"#,
        );
    }

    #[test]
    fn rejects_principal_as_for_binder() {
        assert_reserved(
            r#"exists (n: Long). ((count for (principal: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp(principal)))) == n && n > 0)"#,
        );
    }

    /// Control: a NON-reserved binder of each position stays accepted, so the
    /// reserved-word rule doesn't over-reach into ordinary names.
    #[test]
    fn non_reserved_binders_stay_accepted() {
        check(r#"exists (user: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: user }"#)
            .expect("ordinary exists binder is fine");
        check(r#"exists (n: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp(t)))) == n && n > 0)"#)
            .expect("ordinary for/tp binders are fine");
    }

    // ─── Aggregation `for`-var range restriction (soundness, U1) ───────
    //
    // The monitorable fragment requires an aggregation body to denote a
    // FINITE relation over its `for` domain — occurrence alone is not enough.
    // A `for`-variable whose only occurrences are under a negation or in the
    // left operand of a `since` is not range-restricted: the relation is
    // infinite (or does not range over the variable at all) and the evaluator
    // silently degrades to a witness count with no such column. Each `for`
    // variable must therefore be in RR(body), exactly like an `exists` binder.

    #[test]
    fn agg_for_var_only_under_negation_is_rejected() {
        // `{x | ¬ once Login(x)}` is infinite; the evaluator would count 1.
        let e = check(
            r#"exists (nn: Long). ((count for (x: String). where (!(formerly within 1h Drupe::Action::"Login"::request{ input.user: x }))) == nn && nn >= 1)"#,
        )
        .expect_err("a for-var occurring only under a negation must be rejected");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    #[test]
    fn sum_summand_only_under_negation_is_rejected() {
        // Same shape through `sum`: the summand column never materializes, so
        // the sum silently evaluates to 0 — the exact trap the summand-in-
        // `for`-list rule exists to prevent.
        let e = check(
            r#"exists (nn: Long). ((sum a for (a: Long). where (!(formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a }))) == nn && nn == 0)"#,
        )
        .expect_err("a summand occurring only under a negation must be rejected");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    #[test]
    fn agg_for_var_only_in_since_left_is_rejected() {
        // Range restriction propagates only through the since-RIGHT (the
        // anchor); a left-only variable is evaluated per-step with independent
        // re-quantification and produces no column in the anchor rows.
        let e = check(
            r#"exists (nn: Long). ((count for (w: String). where (Drupe::Action::"Read"::request{ input.user: w } since within 1h Drupe::Action::"Login"::request{})) == nn && nn >= 1)"#,
        )
        .expect_err("a for-var occurring only in the since-left must be rejected");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    #[test]
    fn agg_for_var_in_since_right_is_accepted() {
        // Positive control for the since arm: an anchor-side occurrence IS a
        // range restrictor, so the same shape with the predicate on the RIGHT
        // stays accepted.
        check(
            r#"exists (nn: Long). ((count for (w: String). where (Drupe::Action::"Ping"::request{} since within 1h Drupe::Action::"Login"::request{ input.user: w })) == nn && nn >= 1)"#,
        )
        .expect("a for-var restricted by the since anchor is safe");
    }

    #[test]
    fn agg_for_var_guarded_negation_stays_accepted() {
        // The mc_0022 idiom: the for-var is restricted by a positive predicate
        // conjunct, and a guarded negation then filters it. Must stay accepted
        // — the new RR requirement must not over-reject guarded negation.
        check(
            r#"exists (n: Long). ((count for (q: String). where (formerly within 1h Drupe::Action::"Transfer"::request{ input.user: q } && !exists (r: Timepoint). formerly within 1h (Drupe::Action::"Logout"::request{ input.user: q } && tp(r)))) == n && n >= 2)"#,
        )
        .expect("a positively-restricted for-var with a guarded-negation filter is safe");
    }

    #[test]
    fn agg_correlated_with_enclosing_binder_stays_accepted() {
        // A correlated aggregate: the enclosing `exists (u)` variable flows
        // into the body as a bound value; only the aggregate's OWN for-vars
        // need local restriction. `t` is restricted by `tp(t)` — accepted.
        check(
            r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && (count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Transfer"::request{ input.user: u } && tp(t)))) >= 2)"#,
        )
        .expect("enclosing-binder correlation with locally-restricted for-vars is safe");
    }

    // ─── Negation discards restriction facts (soundness, U2) ───────────
    //
    // the ¬ labeling rule removes EVERY restriction fact — it
    // does not flip a parity. An even-negation-depth atom must not count as a
    // positive restrictor: the evaluator's negation is an opaque boolean
    // filter whose rows carry no bindings.

    #[test]
    fn exists_restricted_only_by_double_negation_is_rejected() {
        let e = check(
            r#"exists (x: String). !(!(formerly within 1h Drupe::Action::"Login"::request{ input.user: x }))"#,
        )
        .expect_err("a double-negated atom is not a positive restrictor");
        assert!(e.contains("not range-restricted"), "{e}");
    }

    #[test]
    fn exists_restrictor_beside_double_negation_stays_accepted() {
        // Control: a genuine positive restrictor next to a doubly-negated
        // filter keeps the formula accepted — discarding facts under ¬ must
        // not reject the guarded shape.
        check(
            r#"exists (x: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: x } && !(!(formerly within 1h Drupe::Action::"Login"::request{ input.user: x })))"#,
        )
        .expect("a positive restrictor beside a double negation is safe");
    }

    // ─── Leaf closedness (soundness, U3) ────────────────────────────────
    //
    // A temporal leaf is evaluated boolean-ly at the decision point with NO
    // implicit existential closure: a free variable's bindings do not thread
    // across conjuncts (except the bare-predicate-left special case), so an
    // accepted free variable yields an always-false or mis-correlated guard.
    // Leaves must be closed; `check_leaf_closed` runs after `check_condition`
    // in `Temporal::parse` and post-expansion.

    /// The full leaf-level check: bindings + closedness + demands (what
    /// `Temporal::parse` runs, in its order).
    fn check_leaf(body: &str) -> Result<(), String> {
        let cond = parse_condition(body).unwrap_or_else(|e| panic!("parse `{body}` failed: {e}"));
        check_condition(&cond, &BTreeSet::new())?;
        check_leaf_closed(&cond)?;
        check_demands(&cond)
    }

    #[test]
    fn leaf_free_var_in_filter_is_rejected() {
        // The U3a repro: restrictor-then-filter over a free `a`. The chain is
        // well-ordered, but the leaf is not closed.
        let e = check_leaf(
            r#"formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a } && a > 100"#,
        )
        .expect_err("a free variable shared across conjuncts must be rejected");
        assert!(e.contains("free in this temporal condition"), "{e}");
    }

    #[test]
    fn leaf_free_var_guarded_negation_is_rejected() {
        // The U3b repro: "A but not B" over a free `u`.
        let e = check_leaf(
            r#"formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && !(formerly within 1h Drupe::Action::"Logout"::request{ input.user: u })"#,
        )
        .expect_err("a free variable in a guarded negation must be rejected");
        assert!(e.contains("free in this temporal condition"), "{e}");
    }

    #[test]
    fn leaf_single_use_free_var_is_rejected() {
        // Even a single-occurrence free variable (the wildcard-like shape) is
        // rejected: closedness is uniform, and `*` expresses the intent.
        let e =
            check_leaf(r#"formerly within 1h Drupe::Action::"Login"::request{ input.user: u }"#)
                .expect_err("a single-use free variable must be rejected");
        assert!(e.contains("free in this temporal condition"), "{e}");
    }

    #[test]
    fn leaf_free_tp_binder_is_rejected() {
        // A bare `tp(t)` at the leaf level leaves `t` free.
        let e = check_leaf(r#"formerly within 1h (Drupe::Action::"Login"::request{} && tp(t))"#)
            .expect_err("a free tp variable must be rejected");
        assert!(e.contains("free in this temporal condition"), "{e}");
    }

    #[test]
    fn closed_leaves_stay_accepted() {
        // Ground / context-field leaves (the read_login_not_logout shape).
        check_leaf(
            r#"formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user } && !Drupe::Action::"Logout"::request{ input.user: context.input.user }"#,
        )
        .expect("a variable-free leaf is closed");
        // Exists-wrapped filter.
        check_leaf(
            r#"exists (a: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a } && a > 100)"#,
        )
        .expect("an exists-bound variable is closed");
        // The standard aggregation shape: `for`/`tp` binders and the exists
        // binder all bound; nothing leaks (the aggregate binds its for-vars).
        check_leaf(
            r#"exists (n: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp(t)))) == n && n > 0)"#,
        )
        .expect("the standard aggregation shape is closed");
        // A wildcard is not a variable.
        check_leaf(r#"formerly within 1h Drupe::Action::"Login"::request{ input.user: * }"#)
            .expect("a wildcard leaves nothing free");
    }

    #[test]
    fn leaf_with_macro_call_checks_visible_vars_at_parse() {
        // A call-bearing leaf does not false-positive: the `Call` contributes
        // no visible variables (its internals are validated by the
        // post-expansion re-run).
        check_leaf(r#"count_logins(1h) == 2"#).expect("a closed call-bearing leaf is fine");
        // But a variable free OUTSIDE the call is rejected already at parse:
        // hygiene guarantees expansion can never bind a call-site variable,
        // so the rejection is sound and needs no post-expansion deferral.
        let e = check_leaf(r#"count_logins(1h) == n"#)
            .expect_err("a free variable beside a macro call is rejected at parse");
        assert!(e.contains("free in this temporal condition"), "{e}");
    }

    // ─── Demands: binding equalities and since-lefts are consumers too ──
    //
    // A conjunct can PRODUCE bindings (RR) and CONSUME bindings (demands) at
    // once. A binding equality `(agg) == n` produces `n` but consumes the
    // aggregate's outward free variables; `left since right` produces
    // RR(right) but consumes fv(left) \ RR(right). Each demand must be met by
    // a restrictor EARLIER in evaluation order — a preceding conjunct in the
    // same chain, or one inherited from an enclosing chain (the evaluator
    // threads bindings left-to-right through nested structure). An enclosing
    // *binder* is still never a seed; a shadowing binder cuts inherited
    // restrictions of its name.

    #[test]
    fn agg_eq_correlated_var_restricted_after_is_rejected() {
        // The A1 repro: the count consumes `u`, whose restrictor comes later
        // in the chain — the count would run with `u` unbound (global, not
        // per-`u`).
        let e = check(
            r#"exists (u: String). exists (n: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: u } && tp(t)))) == n && n >= 2 && formerly within 1h Drupe::Action::"Login"::request{ input.user: u })"#,
        )
        .expect_err("a binding equality's aggregate demand must be met by a PRECEDING conjunct");
        assert!(e.contains("reads `u` inside its aggregate operand"), "{e}");
    }

    #[test]
    fn agg_eq_correlated_var_restricted_before_stays_accepted() {
        // Restrictor-first spelling of the same formula — the accepted form.
        check(
            r#"exists (u: String). exists (n: Long). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && (count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: u } && tp(t)))) == n && n >= 2)"#,
        )
        .expect("restrictor before the consuming equality is fine");
    }

    #[test]
    fn agg_eq_correlated_var_restricted_in_enclosing_chain_stays_accepted() {
        // The SEEDED case: `u`'s restrictor precedes the nested `exists (n)`
        // in the ENCLOSING chain. The evaluator threads `u`'s bindings into
        // the nested body, so the count is correctly per-`u` — the nested
        // chain inherits the enclosing accumulator and must stay accepted.
        check(
            r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && exists (n: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: u } && tp(t)))) == n && n >= 2))"#,
        )
        .expect("an enclosing-chain restrictor before the nested exists discharges the demand");
    }

    #[test]
    fn agg_eq_correlated_var_restricted_only_after_nested_exists_is_rejected() {
        // Flipped nesting: the consuming `exists (n)` conjunct precedes `u`'s
        // restrictor in the enclosing chain — the count runs before `u`'s
        // rows exist. Must be rejected.
        let e = check(
            r#"exists (u: String). (exists (n: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: u } && tp(t)))) == n && n >= 2) && formerly within 1h Drupe::Action::"Login"::request{ input.user: u })"#,
        )
        .expect_err("a restrictor after the consuming nested exists does not discharge");
        assert!(e.contains("reads `u` inside its aggregate operand"), "{e}");
    }

    #[test]
    fn agg_eq_shadowing_binder_cuts_inherited_restriction() {
        // The outer chain restricts `u`, but the inner `exists (u)` SHADOWS
        // it — the inner `u` is a different variable, so the inherited
        // restriction must not discharge the inner equality's demand.
        // (The inner `u` is itself range-restricted by the trailing
        // `formerly Transfer{u}`, so the exists-RR check passes; only the
        // demands rule can catch the order.)
        let e = check(
            r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && exists (u: String). exists (n: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Transfer"::request{ input.user: u } && tp(t)))) == n && n >= 1 && formerly within 1h Drupe::Action::"Transfer"::request{ input.user: u }))"#,
        )
        .expect_err("a shadowing binder cuts the inherited restriction of its name");
        assert!(e.contains("reads `u` inside its aggregate operand"), "{e}");
    }

    #[test]
    fn since_left_var_restricted_after_is_rejected() {
        // The A2 repro: the since-left reads `u`; the anchor restricts
        // nothing about it and its restrictor comes later — per-step
        // re-quantification, verdict changes under commutation.
        let e = check(
            r#"exists (u: String). ((Drupe::Action::"Read"::request{ input.user: u } since within 1h Drupe::Action::"Login"::request{}) && formerly within 1h Drupe::Action::"Transfer"::request{ input.user: u })"#,
        )
        .expect_err("a since-left variable needs the anchor or a preceding conjunct");
        assert!(e.contains("left operand of a `since`"), "{e}");
    }

    #[test]
    fn since_left_var_restricted_before_stays_accepted() {
        // Commuted spelling: the restrictor precedes the since.
        check(
            r#"exists (u: String). (formerly within 1h Drupe::Action::"Transfer"::request{ input.user: u } && (Drupe::Action::"Read"::request{ input.user: u } since within 1h Drupe::Action::"Login"::request{}))"#,
        )
        .expect("restrictor before the since discharges the left's demand");
    }

    #[test]
    fn since_left_var_restricted_by_anchor_stays_accepted() {
        // The standard form: free(left) ⊆ free(right) — the anchor binds
        // `u`, the left is checked per step under that binding.
        check(
            r#"exists (u: String). (Drupe::Action::"Read"::request{ input.user: u } since within 1h Drupe::Action::"Login"::request{ input.user: u })"#,
        )
        .expect("an anchor-restricted since-left variable is fine");
    }

    #[test]
    fn since_left_demand_propagates_through_formerly() {
        // The demand must surface through a `formerly` wrapper: the since
        // sits inside a formerly conjunct, but its left still consumes `u`
        // before `u`'s restrictor.
        let e = check(
            r#"exists (u: String). (formerly within 1h (Drupe::Action::"Read"::request{ input.user: u } since within 1h Drupe::Action::"Login"::request{}) && formerly within 1h Drupe::Action::"Transfer"::request{ input.user: u })"#,
        )
        .expect_err("a demand inside a formerly-wrapped conjunct still counts");
        assert!(e.contains("left operand of a `since`"), "{e}");
    }

    #[test]
    fn wildcard_equality_is_not_a_restrictor() {
        // `x == *` never binds anything at evaluation (a wildcard resolves to
        // no value), so it must not count as a restrictor: `x` is left
        // unrestricted and the exists check fires.
        let e = check(r#"exists (x: String). (x == *)"#)
            .expect_err("a wildcard value side binds nothing");
        assert!(e.contains("not range-restricted"), "{e}");
        // The forbid-guard shape: dead guard, fail-open — also rejected.
        let e2 = check(r#"exists (a: Long). (a == * && a > 100)"#)
            .expect_err("a wildcard equality cannot restrict the filter's variable");
        assert!(e2.contains("not range-restricted"), "{e2}");
    }

    #[test]
    fn parenthesized_subchain_inherits_preceding_restrictors() {
        // Byproduct of the seeded walk (fixes the old parenthesization
        // sensitivity): the explicitly right-nested chain inherits the outer
        // accumulator, so `P{a} && (a > 100 && Q)` is accepted exactly like
        // its flat spelling — the evaluator threads `a` into the sub-chain.
        check(
            r#"exists (a: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a } && (a > 100 && formerly within 1h Drupe::Action::"Login"::request{}))"#,
        )
        .expect("a parenthesized sub-chain sees preceding restrictors");
        // The filter-first arrangement stays rejected regardless of grouping.
        let e = check(
            r#"exists (a: Long). ((a > 100 && formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a }) && formerly within 1h Drupe::Action::"Login"::request{})"#,
        )
        .expect_err("a filter before its restrictor is rejected in any grouping");
        assert!(e.contains("preceding conjunct"), "{e}");
    }

    // ─── Reviewer-suggested pins: correct-but-unpinned behaviors ────────

    #[test]
    fn self_referential_agg_equality_is_rejected() {
        // Degenerate binding equality: the bound variable also occurs inside
        // its own aggregate operand. The value side demands `u`, which the
        // equality itself cannot supply — nothing precedes it, so reject.
        let e = check(
            r#"exists (u: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Transfer"::request{ input.amount: u } && tp(t)))) == u)"#,
        )
        .expect_err("a self-referential aggregate equality cannot discharge its own demand");
        assert!(e.contains("reads `u` inside its aggregate operand"), "{e}");
        // Control: with `u` restricted by a PRECEDING conjunct the equality
        // is a well-defined filter-like constraint (u's count equals u) and
        // is accepted — the order, not the self-reference, is the defect.
        check(
            r#"exists (u: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: u } && (count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Transfer"::request{ input.amount: u } && tp(t)))) == u)"#,
        )
        .expect("a preceding restrictor makes the self-referential equality well-defined");
    }

    #[test]
    fn refinement_field_free_var_is_rejected_by_closedness() {
        // A free variable in a direct-write refinement's injected field:
        // `collect_free`'s Refine arm must surface it to the closedness
        // check exactly like an ordinary predicate arg.
        let e = check_leaf(
            r#"formerly within 1h Drupe::Action::"Transfer"::request{ input.user: context.input.user }{ status: x }"#,
        )
        .expect_err("a free variable in an injected refinement field must be rejected");
        assert!(e.contains("free in this temporal condition"), "{e}");
        // Control: exists-bound, the injected field both closes and
        // range-restricts the variable (RR's Refine arm covers fields).
        check_leaf(
            r#"exists (x: String). formerly within 1h Drupe::Action::"Transfer"::request{ input.user: context.input.user }{ status: x }"#,
        )
        .expect("an exists-bound refinement-field variable is closed and restricted");
    }

    #[test]
    fn not_equal_is_a_pure_filter_in_the_demands_walk() {
        // `!=` never binds (there is no value to bind to), so it is a pure
        // filter: rejected before its restrictor, accepted after.
        let e = check(
            r#"exists (a: Long). (a != 5 && formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a })"#,
        )
        .expect_err("a != filter before its restrictor must be rejected");
        assert!(e.contains("preceding conjunct"), "{e}");
        check(
            r#"exists (a: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a } && a != 5)"#,
        )
        .expect("a != filter after its restrictor is fine");
    }

    #[test]
    fn shadowing_for_binder_does_not_inherit_the_seed() {
        // A `for` binder shadowing an enclosing restricted variable is a
        // FRESH variable (the evaluator sheds it from the env), so the
        // where-body chain's seed must drop it: a filter-first body is
        // rejected even though the enclosing chain restricted the same name…
        let e = check(
            r#"exists (u: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: u } && (count for (u: Long), (t: Timepoint). where (u > 100 && formerly within 1h (Drupe::Action::"Transfer"::request{ input.amount: u } && tp(t)))) >= 1)"#,
        )
        .expect_err("a shadowing for-binder must not inherit the enclosing restriction");
        assert!(e.contains("preceding conjunct"), "{e}");
        // …exactly like its alpha-renamed twin (acceptance must be
        // alpha-equivalent):
        let e2 = check(
            r#"exists (u: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: u } && (count for (w: Long), (t: Timepoint). where (w > 100 && formerly within 1h (Drupe::Action::"Transfer"::request{ input.amount: w } && tp(t)))) >= 1)"#,
        )
        .expect_err("the renamed twin is rejected the same way");
        assert!(e2.contains("preceding conjunct"), "{e2}");
        // Control: a NON-shadowed enclosing variable still seeds through —
        // the correlated `u` (not in the for list) reaches the body's filter.
        check(
            r#"exists (u: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: u } && (count for (t: Timepoint). where (u > 100 && formerly within 1h (Drupe::Action::"Login"::request{} && tp(t)))) >= 1)"#,
        )
        .expect("a non-shadowed enclosing restriction seeds the where body");
    }

    #[test]
    fn sigil_detection_covers_predicate_args_tp_slots_and_refine_fields() {
        // Defensive pins for `body_has_sigil`: sigils in term/binder
        // positions the grammar reaches only inside macro bodies must still
        // trigger the punt if such a shape ever reaches a leaf check. Built
        // directly as AST (the leaf grammar cannot spell these).
        use crate::error::Span;
        let span = Span { start: 0, end: 0 };
        let pred_with_sigil_arg = Condition {
            kind: ConditionKind::Predicate(Predicate {
                namespace: vec!["Drupe".into(), "Action".into()],
                action: "Login".into(),
                kind: "request".into(),
                args: vec![NamedArg {
                    name: "input.user".into(),
                    value: Term::ParamRef("x".into()),
                }],
                span,
            }),
            span,
        };
        assert!(
            body_has_sigil(&pred_with_sigil_arg),
            "a sigil predicate arg must trigger the punt"
        );
        let tp_with_sigil_slot = Condition {
            kind: ConditionKind::Tp {
                var: BinderSlot::ParamRef("t".into()),
            },
            span,
        };
        assert!(
            body_has_sigil(&tp_with_sigil_slot),
            "a sigil tp slot must trigger the punt"
        );
        let refine_with_sigil_field = Condition {
            kind: ConditionKind::Refine {
                // A sigil-FREE base, so the assertion can only pass through
                // the fields branch — using the sigil-bearing predicate here
                // would short-circuit on the base and never exercise it.
                base: Box::new(Condition {
                    kind: ConditionKind::Predicate(Predicate {
                        namespace: vec!["Drupe".into(), "Action".into()],
                        action: "Login".into(),
                        kind: "request".into(),
                        args: vec![NamedArg {
                            name: "input.user".into(),
                            value: Term::Var("u".into()),
                        }],
                        span,
                    }),
                    span,
                }),
                fields: vec![NamedArg {
                    name: "status".into(),
                    value: Term::ParamRef("v".into()),
                }],
                span,
            },
            span,
        };
        assert!(
            body_has_sigil(&refine_with_sigil_field),
            "a sigil refinement field must trigger the punt"
        );
    }
}
