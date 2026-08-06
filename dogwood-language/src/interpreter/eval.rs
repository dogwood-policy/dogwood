//! The temporal condition evaluator.
//!
//! Implements the temporal semantics exactly as given in the formal
//! specification, so verdicts agree with the corpus:
//!
//! * a condition is evaluated at a single decision timepoint `i`
//!   against the trace history `0..=i`;
//! * `formerly within W body` scans `j` in `[0, i]` with the **closed**
//!   window `ts(i) - ts(j) <= W_seconds`, succeeding if `body` holds at
//!   any such `j`;
//! * `previous within W body` checks only `j = i-1`;
//! * `since` anchors `right` at some `j` in the window and requires
//!   `left` at every `k` in `[j+1, i]` (write `!X since …` for the
//!   negated-left "X has not held since" form);
//! * `!a` = ¬a (the conjunct-level negation; replaces the old
//!   `a except b`, now written `a && !b`);
//! * predicate args bind unbound variables and equality-check bound
//!   ones; bindings accumulate left-to-right through `&&`.

use std::collections::BTreeMap;

use crate::extension::temporal::ast::{
    AggExpr, AggExprKind, CmpOp, Condition, ConditionKind, Interval, NamedArg, Predicate, Term,
    TypedBinder,
};

use super::value::{Trace, Value};

/// Variable bindings in scope during evaluation (innermost last).
type Env = BTreeMap<String, Value>;

/// Evaluate a temporal condition at decision timepoint `i`.
///
/// `request_env` holds the request event's fields as bindings (so
/// `context.input.x` resolves). Returns whether the condition holds.
pub fn eval_condition(trace: &Trace, i: usize, env: &Env, cond: &Condition) -> bool {
    match &cond.kind {
        ConditionKind::And { left, right } => {
            // Left-to-right: bindings from `left` are visible to `right`.
            // We thread bindings by trying to satisfy left while
            // collecting its bindings, then evaluating right.
            eval_and(trace, i, env, left, right)
        }
        // Internal-only disjunction (synthesized by the pin-relativization
        // rewrite; the surface grammar has no `||`): at least one branch
        // holds. Branch bindings do not escape a boolean disjunction —
        // the rewrite closes each branch's variables inside the branch.
        ConditionKind::Or { left, right } => {
            eval_condition(trace, i, env, left) || eval_condition(trace, i, env, right)
        }
        ConditionKind::Not { inner } => !eval_condition(trace, i, env, inner),
        ConditionKind::Formerly { within, body } => {
            scan_formerly(trace, i, env, within.interval(), body)
        }
        ConditionKind::Previous { within, body } => {
            if i == 0 {
                return false;
            }
            let j = i - 1;
            in_window(trace, i, j, within.interval()) && eval_condition(trace, j, env, body)
        }
        ConditionKind::Since {
            left,
            within,
            right,
        } => eval_since(trace, i, env, left, within.interval(), right),
        ConditionKind::Predicate(p) => {
            // A predicate at `i` matches the event there when their
            // identity (action + kind + namespace) and args agree.
            match_predicate(trace, i, env, p).is_some()
        }
        ConditionKind::Comparison { op, left, right } => {
            eval_comparison(env, trace, i, *op, left, right)
        }
        // `exists (x: T). φ` holds iff `φ` has at least one satisfying
        // assignment (with `x` range-restricted by a positive atom in
        // `φ`). Operationally: `φ` produces a relation of binding rows over
        // the trace, and existence is that relation being non-empty. `x`'s
        // candidate values come from whichever atom binds it (a predicate
        // field, a `tp`, or an `(agg) == x` equality — see
        // `match_occurrences`); no enumeration of the type `T`.
        //
        // Shadow the binder: shed `x` from the incoming env so an enclosing
        // binding of the same name does not leak in and turn `x`'s binding
        // occurrences into equality filters (which would break alpha-
        // equivalence — renaming `x` would change the verdict). Context
        // fields are `context.`-keyed (see `request_env`), so removing the
        // bare variable name never disturbs a `context.<name>` reference.
        ConditionKind::Exists { var, body } => {
            let mut inner = env.clone();
            inner.remove(var.name());
            !match_occurrences(trace, i, &inner, body).is_empty()
        }
        // `tp(t)` in boolean position: holds iff `t` is unbound (then it
        // would bind, but there is nothing to bind into here) or already
        // equals the current timepoint. The binding effect only matters
        // in relational (aggregation-domain) context — see
        // `match_occurrences`.
        ConditionKind::Tp { var } => match env.get(var.name()) {
            Some(bound) => bound.dom_eq(&Value::Int(i as i64)),
            None => true,
        },
        ConditionKind::Call(call) => panic!(
            "eval reached unresolved macro call `{}` — expansion did not run",
            call.name
        ),
        ConditionKind::SigilRef { sigil, name } => panic!(
            "eval reached unresolved condition sigil `{}{name}` — expansion did not run",
            match sigil {
                crate::extension::temporal::ast::Sigil::Param => "?",
                crate::extension::temporal::ast::Sigil::Binder => "$",
            }
        ),
        ConditionKind::Refine { .. } => {
            panic!("eval reached an unfolded field-injection refinement — expansion did not run")
        }
    }
}

/// Evaluate an aggregation expression at decision timepoint `i`. Returns
/// the integer result (the sum, or the row count). Called from comparison
/// evaluation ([`resolve_term_at`]) — an aggregate is a numeric term.
pub fn eval_agg_expr(trace: &Trace, i: usize, env: &Env, value: &AggExpr) -> i64 {
    match &value.kind {
        AggExprKind::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            let inner = shed_for_binders(env, for_vars);
            let rel = project_dedup(&match_occurrences(trace, i, &inner, body), for_vars);
            sum_column(&rel, bound_var.name())
        }
        AggExprKind::Count { for_vars, body } => {
            let inner = shed_for_binders(env, for_vars);
            project_dedup(&match_occurrences(trace, i, &inner, body), for_vars).len() as i64
        }
        AggExprKind::Call(call) => panic!(
            "eval reached unresolved macro call `{}` — expansion did not run",
            call.name
        ),
    }
}

/// Clone `env` and shed each **local** `for` binder name, so an enclosing
/// binding of the same name does not leak into the aggregation body and turn
/// the binder's occurrences into equality filters (alpha-equivalence: renaming
/// a `for` variable must not change the aggregate's value). Only the local
/// `for` names are removed — an *enclosing* binder not in `for_vars` must keep
/// flowing in, so a correlated aggregate
/// (`exists (u). ( … count for (t). where Transfer{ user: u } && tp(t) … )`)
/// still sees the outer `u` in its `where` body.
fn shed_for_binders(env: &Env, for_vars: &[TypedBinder]) -> Env {
    let mut inner = env.clone();
    for v in for_vars {
        inner.remove(v.name());
    }
    inner
}

/// A binding row: ordered `(name, value)` pairs (order matters for the
/// positional distinctness `count` uses).
type Row = Vec<(String, Value)>;

/// Compute the relation (set of binding rows) a condition produces over
/// the trace, for aggregation. A bare predicate at `i` yields at most
/// one row; `formerly`/`since` scan `0..=i` stamping each match with a
/// distinct timepoint column so per-occurrence rows stay distinct;
/// `And` joins left/right rows on shared columns.
fn match_occurrences(trace: &Trace, i: usize, env: &Env, cond: &Condition) -> Vec<Row> {
    match &cond.kind {
        ConditionKind::Predicate(p) => match match_predicate(trace, i, env, p) {
            Some(bindings) => vec![bindings.into_iter().collect()],
            None => Vec::new(),
        },
        ConditionKind::And { left, right } => {
            let lrows = match_occurrences(trace, i, env, left);
            let mut out = Vec::new();
            for lrow in &lrows {
                // Extend env with the left row, enumerate right, join.
                let mut env2 = env.clone();
                for (k, v) in lrow {
                    env2.insert(k.clone(), v.clone());
                }
                for rrow in match_occurrences(trace, i, &env2, right) {
                    if let Some(joined) = join_rows(lrow, &rrow) {
                        out.push(joined);
                    }
                }
            }
            out
        }
        // Internal-only disjunction: the set union of the two branches'
        // satisfying rows, deduplicated — mirroring the temporal engine's
        // `UNION` (set semantics), so a tuple produced by both branches
        // counts once in an enclosing aggregation. The rewrite emits `Or`
        // only with identical per-branch free variables (each closed
        // within its branch), so the rows are union-compatible.
        ConditionKind::Or { left, right } => {
            let mut out = match_occurrences(trace, i, env, left);
            for row in match_occurrences(trace, i, env, right) {
                if !out.iter().any(|r| rows_eq(r, &row)) {
                    out.push(row);
                }
            }
            out
        }
        ConditionKind::Formerly { within, body } => {
            // Collect the body's satisfying rows at every in-window past
            // timepoint. Per-timepoint distinctness is the caller's
            // explicit choice: conjoin `tp(t)` and include `t` in the
            // aggregation's `for` domain. (The old implicit form stamped a
            // synthetic timepoint column here; that machinery is gone.)
            let interval = within.interval();
            let mut out = Vec::new();
            for j in 0..=i {
                if !in_window(trace, i, j, interval) {
                    continue;
                }
                out.extend(match_occurrences(trace, j, env, body));
            }
            out
        }
        // `previous within I body`: relationally, its rows at `i` are
        // exactly `body`'s rows at the immediately preceding timepoint
        // `i-1`, provided `i>0` and the elapsed time is in the window. The
        // single-point analogue of `Formerly`; binds `free(body)`.
        ConditionKind::Previous { within, body } => {
            if i == 0 {
                return Vec::new();
            }
            let j = i - 1;
            if in_window(trace, i, j, within.interval()) {
                match_occurrences(trace, j, env, body)
            } else {
                Vec::new()
            }
        }
        // `left since within I right` (MFOTL `left S_I right`): a row is a
        // satisfying valuation iff the anchor `right` held at some in-window
        // past timepoint `j` and `left` held at every step in `(j, i]` under
        // that same valuation. Binds `free(left) ∪ free(right)`;
        // the range restriction comes from the anchor `right` (the since
        // rule propagates only the second subformula's
        // label). We enumerate the anchor's rows, then keep a row only if
        // `left` holds at every intervening step under that row's bindings.
        ConditionKind::Since {
            left,
            within,
            right,
        } => {
            let interval = within.interval();
            let mut out: Vec<Row> = Vec::new();
            for j in 0..=i {
                if !in_window(trace, i, j, interval) {
                    continue;
                }
                for anchor in match_occurrences(trace, j, env, right) {
                    // Extend the env with the anchor's bindings, then require
                    // `left` at every k in (j, i] under those bindings.
                    let mut env2 = env.clone();
                    for (k, v) in &anchor {
                        env2.insert(k.clone(), v.clone());
                    }
                    let left_holds_since =
                        ((j + 1)..=i).all(|k| eval_condition(trace, k, &env2, left));
                    if left_holds_since && !out.iter().any(|r| rows_eq(r, &anchor)) {
                        out.push(anchor);
                    }
                }
            }
            out
        }
        // `tp(t)` in relational context binds `t` to the current
        // timepoint index `i`: contribute one row `{t: i}`. If `t` is
        // already bound (e.g. by an outer join), contribute a row only
        // when it agrees, so the conjunction unifies on `t`.
        ConditionKind::Tp { var } => {
            let name = var.name();
            match env.get(name) {
                Some(bound) if !bound.dom_eq(&Value::Int(i as i64)) => Vec::new(),
                _ => vec![vec![(name.to_string(), Value::Int(i as i64))]],
            }
        }
        // `exists (x: T). φ` in relational context: φ's rows with the
        // bound `x` projected away (it is local to the exists), then
        // deduplicated (set semantics). Other bindings escape — `exists`
        // binds only its own variable. This is MFOTL's ∃-as-projection,
        // and any conforming engine must compute the same projection. The
        // pin-relativization rewrite relies on it: its fresh timepoint
        // binders stay internal while the rewritten body's own variables
        // still flow to an enclosing aggregation domain.
        //
        // Shadow the binder first (mirroring the `eval_condition` arm): shed
        // `x` from the incoming env so an enclosing binding of the same name
        // does not leak in and turn `x`'s binding occurrences into equality
        // filters — which would break alpha-equivalence.
        ConditionKind::Exists { var, body } => {
            let name = var.name();
            let mut inner = env.clone();
            inner.remove(name);
            let mut out: Vec<Row> = Vec::new();
            for mut row in match_occurrences(trace, i, &inner, body) {
                row.retain(|(k, _)| k != name);
                if !out.iter().any(|r| rows_eq(r, &row)) {
                    out.push(row);
                }
            }
            out
        }
        ConditionKind::Call(call) => panic!(
            "match_occurrences reached unresolved macro call `{}` — expansion did not run",
            call.name
        ),
        ConditionKind::SigilRef { sigil, name } => panic!(
            "match_occurrences reached unresolved condition sigil `{}{name}` — expansion did not run",
            match sigil {
                crate::extension::temporal::ast::Sigil::Param => "?",
                crate::extension::temporal::ast::Sigil::Binder => "$",
            }
        ),
        ConditionKind::Refine { .. } => panic!(
            "match_occurrences reached an unfolded field-injection refinement — expansion did not run"
        ),
        // An equality `a == x` / `x == a` with exactly one *unbound*
        // variable operand range-restricts that variable: contribute one
        // row binding it to the other operand's value. This is standard
        // MFOTL — an equality against a ground/computed term (a literal,
        // a context field, or an aggregate) is a range-restrictor exactly
        // like a positive predicate occurrence. It is what lets
        // `exists (n: Long). ((agg) == n && …)` bind `n` to the
        // aggregate's value (the `let`-encoding). A comparison with no
        // unbound operand falls through to the filter case below.
        ConditionKind::Comparison {
            op: CmpOp::Eq,
            left,
            right,
        } => match eq_binding(env, trace, i, left, right) {
            Some(row) => vec![row],
            None => filter_witness(trace, i, env, cond),
        },
        // Comparison / other forms used as a filter inside a `where`
        // body: if the boolean condition holds, contribute one empty
        // row (a witness), else none.
        _ => filter_witness(trace, i, env, cond),
    }
}

/// A `where`-body filter: the boolean condition holds → one empty witness
/// row; else none.
fn filter_witness(trace: &Trace, i: usize, env: &Env, cond: &Condition) -> Vec<Row> {
    if eval_condition(trace, i, env, cond) {
        vec![Vec::new()]
    } else {
        Vec::new()
    }
}

/// If exactly one operand of an equality is an unbound `Var` and the other
/// resolves to a value, return the single-column binding row for that
/// variable. Returns `None` when neither operand is an unbound variable
/// (both resolvable → a plain filter) or the resolvable side is unknown.
fn eq_binding(env: &Env, trace: &Trace, i: usize, left: &Term, right: &Term) -> Option<Row> {
    // A term is an unbound variable iff it is a bare `Var` absent from env.
    let unbound_var = |t: &Term| -> Option<String> {
        match t {
            Term::Var(name) if env.get(name).is_none() => Some(name.clone()),
            _ => None,
        }
    };
    match (unbound_var(left), unbound_var(right)) {
        (Some(name), None) => {
            let v = resolve_term_at(env, trace, i, right)?;
            Some(vec![(name, v)])
        }
        (None, Some(name)) => {
            let v = resolve_term_at(env, trace, i, left)?;
            Some(vec![(name, v)])
        }
        // Both unbound (can't restrict) or neither unbound (plain filter).
        _ => None,
    }
}

/// Project each row onto `vars` (in order), then deduplicate. A column
/// in `vars` that a row lacks is dropped from that row (it contributes
/// an absent binding); rows that become equal after projection collapse
/// to one. This is what makes the aggregation domain — and thus the
/// dedup-vs-keep distinction — a visible choice in the `for` binder list.
///
/// `vars` is `&[TypedBinder]`: post-expansion every slot has been resolved
/// to a concrete name (`TypedBinder::name()` panics on a still-sigil
/// slot, flagging a bug in the macro expander). Only the name is used
/// here — the type annotation is not consulted by evaluation.
fn project_dedup(rel: &[Row], vars: &[TypedBinder]) -> Vec<Row> {
    let mut out: Vec<Row> = Vec::new();
    for row in rel {
        let projected: Row = vars
            .iter()
            .filter_map(|v| {
                let name = v.name();
                row.iter()
                    .find(|(k, _)| k == name)
                    .map(|(k, val)| (k.clone(), val.clone()))
            })
            .collect();
        if !out.iter().any(|r| rows_eq(r, &projected)) {
            out.push(projected);
        }
    }
    out
}

/// Join two rows: union of columns, failing if they disagree on a
/// shared column.
fn join_rows(a: &Row, b: &Row) -> Option<Row> {
    let mut out = a.clone();
    for (k, v) in b {
        if let Some((_, existing)) = out.iter().find(|(ek, _)| ek == k) {
            if !existing.dom_eq(v) {
                return None;
            }
        } else {
            out.push((k.clone(), v.clone()));
        }
    }
    Some(out)
}

/// Sum the integer values of column `col` across all rows.
///
/// Accumulated in 128 bits, then clamped to the result width ONCE, at the end.
///
/// The width matters because an aggregate ranges over a SET: its value must not
/// depend on the order rows happen to be folded in. Accumulating in the result's
/// own width breaks that — a partial total can leave the range while the final total
/// sits well inside it, and a clamp applied mid-fold never recovers, so the answer
/// becomes a function of row order. Two orders of the same rows could disagree, and
/// a total that was perfectly representable could come out wrong.
///
/// 128 bits cannot itself overflow here: every input is an `i64`, so a relation
/// would need on the order of 2^64 rows to exceed the accumulator.
///
/// A total that does NOT fit is clamped to the returned range. That case is
/// IMPLEMENTATION-DEFINED by the language (formal specification §5.4, "Aggregate
/// value"): an implementation may clamp, compare at a wider precision, or report an
/// error, and a policy whose verdict depends on the choice is not portable. Clamping
/// is chosen here so a pathological relation cannot take down the evaluator, which is
/// what the previous saturating fold was for.
///
/// An implementation that widens instead answers differently, so a policy that can
/// observe the difference is not a sound basis for comparing two implementations.
/// Taking those two readings (an ERRORING implementation differs from both for every
/// comparison, so it is not covered here):
///
/// - Compared DIRECTLY, only a comparison against an endpoint can distinguish them —
///   at the maximum `==`, `!=`, `>` and `<=` can while `>=` and `<` cannot, mirrored
///   at the minimum. A threshold strictly inside the range never can.
/// - BOUND to a variable, as `exists (n: Long). ((A) == n && B)` does, the reach is
///   wider: an out-of-range total has no `Long` witness unless clamped, so a widening
///   implementation empties the existential. The readings then differ exactly when `B`
///   holds of the clamped endpoint — so `n > <maximum>` agrees (no `Long` exceeds it)
///   while most other `B` do not. Under `forbid` an empty existential stops the rule
///   firing, so the divergence surfaces as a permit rather than a deny.
///
/// A row whose value is not an integer is SKIPPED, not treated as zero — which for a
/// sum is the same thing, but is worth stating because `count` over the same relation
/// still counts it, so the two disagree about the same rows.
///
/// Validation catches the common way in: a summand's declared type is checked against
/// the type of whatever range-restricts it, so a `Long` summand equated to a `String`
/// field or scope attribute is rejected. It is NOT a guarantee, and the gaps matter
/// because each one is fail-OPEN — a `forbid` written that way never fires:
///
/// - Validation is a SEPARATE step. `Authorizer::new` takes a lowered policy set and
///   does not require one, so an unvalidated (or outright rejected) policy runs.
/// - A comparison is only checked when both sides type, and nothing types under an
///   `action in [..]` or unconstrained `action` scope, which pins no single signature.
/// - An OPTIONAL attribute types fine and can still be absent at run time, and the
///   temporal dialect has no `has` guard with which to test for it.
/// - An attribute declared on only SOME of the entity types a scope permits is left
///   untyped on purpose, since rejecting it would remove a capability that has no
///   other spelling.
///
/// So the skip is a backstop that is genuinely load-bearing, not dead defence. It
/// cannot be promoted into the guard: this function cannot tell an absent column from
/// a present non-integer one, and the type information is gone by the time a row
/// arrives.
fn sum_column(rel: &[Row], col: &str) -> i64 {
    let total: i128 = rel
        .iter()
        .filter_map(|row| row.iter().find(|(k, _)| k == col).map(|(_, v)| v))
        .filter_map(|v| v.as_int())
        .map(i128::from)
        .sum();

    total.clamp(i128::from(i64::MIN), i128::from(i64::MAX)) as i64
}

fn rows_eq(a: &Row, b: &Row) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|((ka, va), (kb, vb))| ka == kb && va.dom_eq(vb))
}

/// And with left-to-right binding flow. We evaluate `left`; if it is a
/// binding-producing predicate, we extend the env before evaluating
/// `right`. For non-binding lefts this is a plain conjunction.
fn eval_and(trace: &Trace, i: usize, env: &Env, left: &Condition, right: &Condition) -> bool {
    match &left.kind {
        ConditionKind::Predicate(p) => match match_predicate(trace, i, env, p) {
            Some(bindings) => {
                let mut extended = env.clone();
                extended.extend(bindings);
                eval_condition(trace, i, &extended, right)
            }
            None => false,
        },
        _ => eval_condition(trace, i, env, left) && eval_condition(trace, i, env, right),
    }
}

/// `formerly within W body`: succeed if `body` holds at some `j` in
/// `[0, i]` within the closed window.
fn scan_formerly(trace: &Trace, i: usize, env: &Env, within: Interval, body: &Condition) -> bool {
    for j in (0..=i).rev() {
        // `continue`, not `break`: with strictly-monotone timestamps an
        // out-of-window `j` means every earlier `j` is further out too, so a
        // `break` would be equivalent and cheaper. But event timestamps are
        // untrusted and arrival order is not guaranteed monotone (see
        // `observe`, which appends without sorting); a single out-of-order
        // event must not truncate the scan and blind the guard (a fail-open
        // for a history-gated `forbid`). The relational aggregation path
        // (`match_occurrences`) already scans defensively this way.
        if !in_window(trace, i, j, within) {
            continue;
        }
        if eval_condition(trace, j, env, body) {
            return true;
        }
    }
    false
}

/// `left since within W right`: find an anchor `j` in the window where
/// `right` holds, then require `left` at every `k` in `[j+1, i]`. The
/// negated-left form ("left has *not* held since") is written
/// `!left since …`, so `left` here is simply a `ConditionKind::Not`
/// whose own evaluation flips the result — no special-casing needed.
fn eval_since(
    trace: &Trace,
    i: usize,
    env: &Env,
    left: &Condition,
    within: Interval,
    right: &Condition,
) -> bool {
    for j in (0..=i).rev() {
        // `continue`, not `break`: see `scan_formerly` — untrusted, possibly
        // non-monotone timestamps must not let one out-of-window event
        // truncate the anchor search.
        if !in_window(trace, i, j, within) {
            continue;
        }
        if eval_condition(trace, j, env, right) {
            // Check left across (j, i].
            let mut ok = true;
            for k in (j + 1)..=i {
                if !eval_condition(trace, k, env, left) {
                    ok = false;
                    break;
                }
            }
            if ok {
                return true;
            }
        }
    }
    false
}

/// Closed-window test: `0 <= ts(i) - ts(j) <= W_seconds`.
///
/// Timestamps are untrusted i64s (parsed verbatim from `@<ts>` / set via the
/// event builder), so a straddling pair (`i64::MAX` and a negative) would
/// overflow a plain subtraction — a debug-build panic and a release-build
/// wrap. `saturating_sub` clamps to the i64 bounds instead: a saturated delta
/// is enormous and simply falls outside any real window, which is the
/// fail-closed direction for a `formerly`/`since` guard. `within.seconds()` is
/// itself computed with `checked_mul` (see `Interval::seconds`), so the
/// right-hand side cannot wrap either.
fn in_window(trace: &Trace, i: usize, j: usize, within: Interval) -> bool {
    let delta = trace.ts(i).saturating_sub(trace.ts(j));
    delta >= 0 && delta <= within.seconds()
}

/// Match a predicate against the event at timepoint `i`. The predicate's
/// identity — namespace, action, and kind — must equal the event's;
/// request and response are ordinary predicates distinguished by their
/// `kind`. Returns the new bindings produced by unbound variable args, or
/// `None` if the event doesn't match.
fn match_predicate(trace: &Trace, i: usize, env: &Env, p: &Predicate) -> Option<Env> {
    let event = trace.event(i);
    if event.action != p.action || event.kind != p.kind || event.namespace != p.namespace {
        return None;
    }
    match_args(env, event, &p.args)
}

/// Match a list of named args against an event's fields. An arg whose
/// term is an unbound variable binds that variable to the field value;
/// otherwise the resolved term must equal the field value. A `*`
/// wildcard matches anything.
fn match_args(env: &Env, event: &super::value::EventData, args: &[NamedArg]) -> Option<Env> {
    let mut bindings = Env::new();
    for arg in args {
        // The field name is a dotted path (`input.user`); descend nested
        // event records. A bare name is a single-segment path.
        let field_val = event.field_path(&arg.field_path())?;
        match &arg.value {
            Term::Wildcard => {}
            Term::Var(name) => {
                // Bound already? equality-check. Unbound? bind it.
                if let Some(bound) = env.get(name).or_else(|| bindings.get(name)) {
                    if !bound.dom_eq(field_val) {
                        return None;
                    }
                } else {
                    bindings.insert(name.clone(), field_val.clone());
                }
            }
            other => {
                let v = resolve_term(env, other)?;
                if !v.dom_eq(field_val) {
                    return None;
                }
            }
        }
    }
    Some(bindings)
}

fn eval_comparison(
    env: &Env,
    trace: &Trace,
    i: usize,
    op: CmpOp,
    left: &Term,
    right: &Term,
) -> bool {
    let (l, r) = match (
        resolve_term_at(env, trace, i, left),
        resolve_term_at(env, trace, i, right),
    ) {
        (Some(l), Some(r)) => (l, r),
        _ => return false,
    };
    match op {
        CmpOp::Eq => l.dom_eq(&r),
        CmpOp::NotEq => !l.dom_eq(&r),
        CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge => match (l.as_int(), r.as_int()) {
            (Some(a), Some(b)) => match op {
                CmpOp::Lt => a < b,
                CmpOp::Le => a <= b,
                CmpOp::Gt => a > b,
                CmpOp::Ge => a >= b,
                CmpOp::Eq | CmpOp::NotEq => unreachable!(),
            },
            _ => false,
        },
    }
}

/// Resolve a term to a value, evaluating an aggregate operand against the
/// trace. This is the resolver for comparison operands — the only position
/// an aggregate may occupy. For every non-aggregate term it defers
/// to the env-only [`resolve_term`].
fn resolve_term_at(env: &Env, trace: &Trace, i: usize, term: &Term) -> Option<Value> {
    match term {
        Term::Agg(agg) => Some(Value::Int(eval_agg_expr(trace, i, env, agg))),
        other => resolve_term(env, other),
    }
}

/// Resolve a term to a value under the environment. Used wherever an
/// aggregate cannot appear (predicate args, array elements) — validation
/// guarantees a `Term::Agg` never reaches here, so that arm panics.
fn resolve_term(env: &Env, term: &Term) -> Option<Value> {
    match term {
        Term::Integer(n) => Some(Value::Int(*n)),
        Term::Decimal(s) => Some(Value::Decimal(s.clone())),
        Term::String(s) => Some(Value::String(s.clone())),
        Term::Bool(b) => Some(Value::Bool(*b)),
        Term::Entity { ty, id } => Some(Value::Entity {
            ty: ty.clone(),
            id: id.clone(),
        }),
        Term::Array(items) => {
            let vals: Option<Vec<Value>> = items.iter().map(|t| resolve_term(env, t)).collect();
            vals.map(Value::Array)
        }
        Term::Var(name) => env.get(name).cloned(),
        // `context.<path>`: a field of the request **context** record, read by
        // its full surface path (`context.input.x` → key `context.input.x`).
        // The `context.` head namespaces context fields away from variable
        // bindings (see `request_env`), so a binder named after a context
        // field neither pre-binds the variable nor shadows the field. No
        // scope-alias special-case — a `principal` / `resource` head is an
        // ordinary context field named `principal` / `resource` (as in Cedar),
        // resolving only if the context actually carries it. The scope
        // entities are [`Term::ScopeField`].
        Term::ContextField(path) => env.get(&format!("context.{}", path.join("."))).cloned(),
        // `principal` / `resource` (± attribute tail): the request scope
        // entity or one of its attributes, seeded into the env by
        // [`request_env`] under an `@`-prefixed dotted key (`@principal.dept`).
        // The `@` prefix keeps the scope namespace disjoint from context fields
        // — a context record may legally declare a field literally named
        // `principal` (`context.principal`), which must NOT collide with the
        // request scope entity. A bare root resolves to the entity; an
        // attribute path to its value.
        Term::ScopeField(path) => env.get(&scope_env_key(path)).cloned(),
        Term::Wildcard => None,
        Term::Agg(_) => panic!(
            "resolve_term reached an aggregate outside a comparison operand — \
             validation did not run or admitted an aggregate in a non-operand position"
        ),
        Term::ParamRef(p) => {
            panic!("resolve_term reached unresolved macro param `?{p}` — expansion did not run")
        }
        Term::BinderRef(b) => {
            panic!("resolve_term reached unresolved macro binder `${b}` — expansion did not run")
        }
    }
}

/// Build the request environment for timepoint `i`. Two families of key
/// live here, both anchored to the **current request**:
///
///   * **context fields** — every member of the request `context` record,
///     keyed by its full dotted path (a nested `input: { user }` seeds
///     `input.user`), so a `context.input.user` term resolves to `input.user`.
///   * **scope fields** — the request scope's principal / resource, keyed by
///     `principal` / `resource` (the bare entity) plus every supplied entity
///     attribute under `principal.<attr>` / `resource.<attr>` (and the
///     `.id` / `.type` uid projections), so a `principal.dept` term resolves.
///
/// A temporal formula's `context.<path>` / `principal.<attr>` / `resource.<attr>`
/// references **the current request** — the exact same values the Cedar request
/// and provider args see. Context resolves from `request_context` (NOT
/// `logged`): there is one notion of "the current request's context", shared by
/// Cedar and temporal (Position A). Scope attributes resolve from the current
/// event's entity store (the same store the Cedar request and `resolve_scope_path`
/// read), so the three consumers agree.
///
/// Predicate *field* args (`Login{ foo: x }`) do NOT use this env — they read
/// the matched event's `logged` directly via `field_path` (that event may be in
/// the past). This env resolves only `context.` / `principal.` / `resource.` /
/// bound-variable terms.
pub fn request_env(trace: &Trace, i: usize) -> Env {
    let mut env = Env::new();
    let event = trace.event(i);
    for (k, v) in &event.request_context {
        // Seed context members under a `context.`-headed key
        // (`context.input`, `context.input.user`). The `context.` head keeps
        // the context namespace disjoint from variable bindings: a
        // `context_field` path always carries at least one dot (grammar:
        // `"context" ~ ("." ~ ident)+`) and an `ident` never contains a dot,
        // so a full-path context key can never equal a bare variable name.
        // This is what lets `exists`/`for` binders shed their name from the
        // env (see the `Exists` / `eval_agg_expr` arms) without stranding a
        // same-named `context.<name>` reference in the body.
        seed_env(&mut env, &format!("context.{k}"), v);
    }
    let scope = trace.scope(i);
    if let Some(p) = &scope.principal {
        seed_scope_env(&mut env, "principal", p, event);
    }
    if let Some(r) = &scope.resource {
        seed_scope_env(&mut env, "resource", r, event);
    }
    env
}

/// Seed a scope entity (`principal` / `resource`) and its attributes under
/// `root` (`"principal"` / `"resource"`). The bare `root` key holds the entity
/// itself (for an identity comparison); each supplied attribute of the entity's
/// uid is seeded under `root.<attr>` (nested records flattened into dotted keys,
/// like [`seed_env`]); and the `.id` / `.type` uid projections are seeded unless
/// a supplied attribute already occupies that key. This mirrors the provider-arg
/// resolver `resolve_scope_path` (in `api.rs`): a supplied attribute wins,
/// `.id` / `.type` fall back to the uid, and a deeper path descends — so
/// `principal.dept` resolves for a temporal formula exactly as it does for a
/// provider argument and a pure-Cedar `when`.
fn seed_scope_env(env: &mut Env, root: &str, entity: &Value, event: &super::value::EventData) {
    env.insert(scope_env_key(&[root.to_string()]), entity.clone());
    let Value::Entity { ty, id } = entity else {
        return;
    };
    // Key the store by the canonical (escaped) uid literal — the same form the
    // `.log` `entities(...)` envelope / `EventBuilder::entity` insert under — so
    // an id containing `"` / `\` is not missed (see `entity_uid_string`).
    let uid = super::value::entity_uid_string(ty, id);
    if let Some(rec) = event.entities.get(&uid) {
        for (attr, value) in &rec.attrs {
            // Seed each supplied attribute under `@<root>.<attr>` (nested
            // records flattened by `seed_env`, which appends `.` segments).
            seed_env(
                env,
                &scope_env_key(&[root.to_string(), attr.clone()]),
                value,
            );
        }
    }
    // `.id` / `.type` project the uid via the shared resolver, unless a supplied
    // attribute of that name already took the key (a supplied attribute wins —
    // the resolver checks supplied attrs first, and `seed_env` above already
    // wrote those keys, so `or_insert` only fills a genuinely-absent projection).
    for name in ["id", "type"] {
        let key = scope_env_key(&[root.to_string(), name.to_string()]);
        if let Some(v) = event.resolve_entity_attr(ty, id, &[name.to_string()]) {
            env.entry(key).or_insert(v);
        }
    }
}

/// The env binding key for a scope path (`["principal", "dept"]`). Prefixed
/// with `@` so the scope namespace cannot collide with a context field: the
/// `@` character never appears in a Dogwood identifier, so `@principal.dept`
/// is disjoint from every `context.<path>` key (which are bare dotted
/// identifiers). This is the same reserved-prefix trick the pre-Cedar-parity
/// code used for the scope aliases, generalized to carry an attribute tail.
fn scope_env_key(path: &[String]) -> String {
    format!("@{}", path.join("."))
}

/// Seed the request env with a field, flattening nested records into
/// dotted-path keys. `input: { user, server }` seeds `input.user` and
/// `input.server` (plus `input` itself, so a whole-group reference still
/// resolves). A scalar seeds just its key.
fn seed_env(env: &mut Env, key: &str, value: &Value) {
    if let Value::Object(members) = value {
        for (k, v) in members {
            seed_env(env, &format!("{key}.{k}"), v);
        }
    }
    env.insert(key.to_string(), value.clone());
}

#[cfg(test)]
mod tests {
    //! Evaluation of the general `exists` binder — deliberately *outside*
    //! the "replace `let` with `(agg) == n`" mode the migration produced.
    //! Each case builds a small in-memory trace and evaluates a
    //! `parse_condition`-parsed formula at a decision timepoint, checking
    //! the verdict for the right reason (paired positive/negative controls).

    use super::*;
    use crate::extension::temporal::parse::parse_condition;
    use crate::interpreter::value::{Event, EventData, Scope};

    /// Build a request event `Drupe::Action::"<action>"::request` whose
    /// `input` record holds the given `(field, value)` members.
    fn ev(action: &str, input: &[(&str, Value)]) -> EventData {
        let mut input_rec = BTreeMap::new();
        for (k, v) in input {
            input_rec.insert(k.to_string(), v.clone());
        }
        let mut logged = BTreeMap::new();
        logged.insert("input".to_string(), Value::Object(input_rec.clone()));
        // A temporal formula's `context.input.*` resolves from the current
        // request's `request_context` (Position A), so mirror `input` there —
        // the in-test analog of the corpus `request_context(...)` migration.
        let mut request_context = BTreeMap::new();
        request_context.insert("input".to_string(), Value::Object(input_rec));
        EventData {
            namespace: vec!["Drupe".to_string(), "Action".to_string()],
            action: action.to_string(),
            kind: "request".to_string(),
            logged,
            request_context,
            entities: BTreeMap::new(),
        }
    }

    /// A trace from `(timestamp, event)` points, no scope entities (the
    /// general-`exists` cases here never read `principal` / `resource`).
    fn trace(points: &[(i64, EventData)]) -> Trace {
        Trace {
            points: points
                .iter()
                .map(|(ts, event)| Event {
                    ts: *ts,
                    scope: Scope::default(),
                    event: event.clone(),
                })
                .collect(),
        }
    }

    /// A request event carrying a top-level `callerPrincipal` entity
    /// field (an `Drupe::OAuthUser`), plus an empty `input` record —
    /// for exercising an entity-typed `exists` binder.
    fn ev_pr(action: &str, principal_id: &str) -> EventData {
        let mut logged = BTreeMap::new();
        logged.insert("input".to_string(), Value::Object(BTreeMap::new()));
        logged.insert(
            "callerPrincipal".to_string(),
            Value::Entity {
                ty: "Drupe::OAuthUser".to_string(),
                id: principal_id.to_string(),
            },
        );
        EventData {
            namespace: vec!["Drupe".to_string(), "Action".to_string()],
            action: action.to_string(),
            kind: "request".to_string(),
            logged,
            request_context: BTreeMap::new(),
            entities: BTreeMap::new(),
        }
    }

    fn s(x: &str) -> Value {
        Value::String(x.to_string())
    }
    fn n(x: i64) -> Value {
        Value::Int(x)
    }

    /// Evaluate `body` at the last timepoint of `tr`.
    fn holds(tr: &Trace, body: &str) -> bool {
        let cond = parse_condition(body).unwrap_or_else(|e| panic!("parse `{body}`: {e}"));
        let i = tr.len() - 1;
        let env = request_env(tr, i);
        eval_condition(tr, i, &env, &cond)
    }

    // ─── exists binding a data var used as a comparison filter ──────

    #[test]
    fn exists_data_var_as_comparison_filter() {
        // `exists (a: Long). (formerly … Transfer{amount: a} && a > 100)` —
        // a value existential, NOT an aggregate. Holds iff some past
        // transfer's amount exceeds 100.
        let body = r#"exists (a: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a } && a > 100)"#;

        // Positive: a 150 transfer precedes the decision point.
        let pos = trace(&[
            (0, ev("Transfer", &[("amount", n(150))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            holds(&pos, body),
            "150 > 100 should satisfy the existential"
        );

        // Negative: the only transfer is 50 — no value exceeds 100.
        let neg = trace(&[
            (0, ev("Transfer", &[("amount", n(50))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            !holds(&neg, body),
            "50 > 100 is false, existential must fail"
        );
    }

    // ─── `!=` inequality as a comparison filter ─────────────────────

    #[test]
    fn not_equal_filters_out_matching_value() {
        // `formerly … Transfer{user: u} && context.input.amount != 100` —
        // the inequality holds for every past transfer whose amount is not
        // exactly 100, and is false for the boundary value 100 itself.
        let body = r#"formerly within 1h (Drupe::Action::"Transfer"::request{ input.user: context.input.user } && context.input.amount != 100)"#;

        // Positive: a 99 transfer (99 != 100) satisfies the inequality.
        let pos = trace(&[
            (
                0,
                ev("Transfer", &[("user", s("alice")), ("amount", n(99))]),
            ),
            (
                10,
                ev("Transfer", &[("user", s("alice")), ("amount", n(99))]),
            ),
        ]);
        assert!(holds(&pos, body), "99 != 100 should satisfy the filter");

        // Negative: the only transfer is exactly 100 — `!= 100` is false.
        let neg = trace(&[
            (
                0,
                ev("Transfer", &[("user", s("alice")), ("amount", n(100))]),
            ),
            (
                10,
                ev("Transfer", &[("user", s("alice")), ("amount", n(100))]),
            ),
        ]);
        assert!(!holds(&neg, body), "100 != 100 is false, filter must fail");
    }

    // ─── exists correlating two predicates through the bound var ────

    #[test]
    fn exists_correlates_two_events_by_bound_var() {
        // `exists (u: String). (formerly … Login{user: u} && formerly …
        // Transfer{user: u})` — "some user both logged in AND transferred".
        // The existential joins two distinct predicates on `u`.
        let body = r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && formerly within 1h Drupe::Action::"Transfer"::request{ input.user: u })"#;

        // Positive: alice both logs in and transfers.
        let pos = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (5, ev("Transfer", &[("user", s("alice"))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            holds(&pos, body),
            "alice logs in and transfers → correlated"
        );

        // Negative: alice logs in, BOB transfers — no single `u` does both.
        let neg = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (5, ev("Transfer", &[("user", s("bob"))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            !holds(&neg, body),
            "no single user both logged in and transferred"
        );
    }

    // ─── nested exists ──────────────────────────────────────────────

    #[test]
    fn nested_exists_inner_threshold() {
        // `exists (u). (Login{user:u} && exists (a: Long). (Transfer{user:u,
        // amount:a} && a > 100))` — a user who logged in AND made a transfer
        // over 100. The inner existential is scoped by the outer `u`.
        let body = r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && exists (a: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.user: u, input.amount: a } && a > 100))"#;

        // Positive: alice logs in and transfers 200.
        let pos = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (
                5,
                ev("Transfer", &[("user", s("alice")), ("amount", n(200))]),
            ),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            holds(&pos, body),
            "alice logged in and transferred 200 > 100"
        );

        // Negative: alice logs in but her only transfer is 50 (bob's big
        // transfer must NOT satisfy alice's inner existential).
        let neg = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (
                3,
                ev("Transfer", &[("user", s("alice")), ("amount", n(50))]),
            ),
            (5, ev("Transfer", &[("user", s("bob")), ("amount", n(999))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            !holds(&neg, body),
            "alice's own transfer is 50; bob's 999 is a different user"
        );
    }

    // ─── exists over a Timepoint, aggregate-free ───────────────────

    #[test]
    fn exists_timepoint_binder_outside_aggregate() {
        // `exists (t: Timepoint). (formerly within 1h (Login && tp(t)))` —
        // pure timepoint existence: "there is a past in-window timepoint at
        // which a Login held". tp(t) is used OUTSIDE an aggregate.
        let body = r#"exists (t: Timepoint). (formerly within 1h (Drupe::Action::"Login"::request{ input.user: u } && tp(t)))"#;

        let pos = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(holds(&pos, body), "a past Login timepoint exists in-window");

        // Negative: no Login at all.
        let neg = trace(&[
            (0, ev("Transfer", &[("amount", n(1))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(!holds(&neg, body), "no Login timepoint to witness");
    }

    // ─── negation outside a closed exists ───────────────────────────

    #[test]
    fn negated_exists_absence() {
        // `!exists (u: String). formerly … Login{user: u}` — "no login in
        // the window". Holds iff no Login precedes the decision point.
        let body = r#"!exists (u: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: u }"#;

        let absent = trace(&[
            (0, ev("Transfer", &[("amount", n(1))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(holds(&absent, body), "no login → !exists holds");

        let present = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(!holds(&present, body), "a login exists → !exists fails");
    }

    // ─── window sensitivity of the existential ──────────────────────

    #[test]
    fn exists_respects_the_window() {
        // The same value existential fails when the witnessing event falls
        // OUTSIDE the `formerly within 1h` window — proving the binder does
        // not see the whole trace, only the in-window past.
        let body = r#"exists (a: Long). (formerly within 1h Drupe::Action::"Transfer"::request{ input.amount: a } && a > 100)"#;

        // Transfer of 150 at t=0, decision at t=10 (within 1h=3600s): holds.
        let in_window = trace(&[
            (0, ev("Transfer", &[("amount", n(150))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(holds(&in_window, body), "150 transfer is within the window");

        // Same transfer at t=0 but decision at t=4000 (> 3600s): out of
        // window, so the witness is gone.
        let out_window = trace(&[
            (0, ev("Transfer", &[("amount", n(150))])),
            (4000, ev("Alert", &[])),
        ]);
        assert!(
            !holds(&out_window, body),
            "the 150 transfer is now outside the 1h window"
        );
    }

    // ─── two INDEPENDENT existentials (distinct vars, no join) ──────

    #[test]
    fn two_independent_existentials_no_join() {
        // `exists (u). Login{user:u} && exists (v). Transfer{user:v}` — two
        // separate binders, NOT correlated. Holds iff *some* login and
        // *some* transfer occurred, even by different users (contrast with
        // the shared-`u` correlation case, which requires the same user).
        let body = r#"exists (u: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && exists (v: String). formerly within 1h Drupe::Action::"Transfer"::request{ input.user: v }"#;

        // Different users satisfy it (this is the key difference from a join).
        let diff_users = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (5, ev("Transfer", &[("user", s("bob"))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            holds(&diff_users, body),
            "independent existentials: alice login + bob transfer suffices"
        );

        // Missing the transfer entirely → the second existential fails.
        let no_transfer = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            !holds(&no_transfer, body),
            "no transfer → second exists empty"
        );
    }

    // ─── field-to-field correlation within ONE event ───────────────

    #[test]
    fn exists_correlates_two_fields_of_one_event() {
        // `exists (u). Transfer{ input.user: u, input.recipient: u }` — the
        // SAME bound var appears in two fields of one predicate, so it holds
        // iff some transfer has user == recipient (a self-transfer).
        let body = r#"exists (u: String). formerly within 1h Drupe::Action::"Transfer"::request{ input.user: u, input.recipient: u }"#;

        // Positive: a self-transfer (user == recipient == alice).
        let pos = trace(&[
            (
                0,
                ev(
                    "Transfer",
                    &[("user", s("alice")), ("recipient", s("alice"))],
                ),
            ),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            holds(&pos, body),
            "user == recipient → the shared u unifies"
        );

        // Negative: user != recipient, so no single u satisfies both fields.
        let neg = trace(&[
            (
                0,
                ev("Transfer", &[("user", s("alice")), ("recipient", s("bob"))]),
            ),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            !holds(&neg, body),
            "user != recipient → the shared u cannot unify"
        );
    }

    // ─── `previous` (not `formerly`) inside an existential ──────────

    #[test]
    fn exists_with_previous_operator() {
        // `previous within W` checks only the immediately-preceding
        // timepoint. `exists (u). previous within 1h Login{user:u}` holds
        // iff the event just before the decision point is a matching Login.
        let body = r#"exists (u: String). previous within 1h Drupe::Action::"Login"::request{ input.user: u }"#;

        // Positive: Login is the immediately-preceding timepoint.
        let pos = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(holds(&pos, body), "the previous timepoint is a Login");

        // Negative: a Transfer sits between the Login and the decision, so
        // the *immediately* preceding event is not a Login.
        let neg = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (5, ev("Transfer", &[("user", s("alice"))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(
            !holds(&neg, body),
            "the immediately-preceding event is the Transfer, not the Login"
        );
    }

    // ─── existence is "≥1" regardless of witness multiplicity ───────

    #[test]
    fn exists_is_one_or_more_not_a_count() {
        // An existential is non-empty whether one or many witnesses match —
        // it must NOT behave like a count. Same formula, one vs. three
        // logins in window: both hold.
        let body = r#"exists (u: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: u }"#;

        let one = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (10, ev("Alert", &[])),
        ]);
        let many = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (1, ev("Login", &[("user", s("bob"))])),
            (2, ev("Login", &[("user", s("carol"))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(holds(&one, body), "one witness → exists holds");
        assert!(
            holds(&many, body),
            "three witnesses → exists still just holds"
        );

        // Zero witnesses → fails (the boundary the above must not cross).
        let none = trace(&[
            (0, ev("Transfer", &[("amount", n(1))])),
            (10, ev("Alert", &[])),
        ]);
        assert!(!holds(&none, body), "zero witnesses → exists fails");
    }

    // ─── closed-window boundary (inclusive edge) ────────────────────

    #[test]
    fn exists_window_boundary_is_inclusive() {
        // The window is closed: `ts(i) - ts(j) <= W`. A witness *exactly* W
        // seconds back is IN; one second further is OUT. 1h = 3600s.
        let body = r#"exists (u: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: u }"#;

        // Login exactly 3600s before the decision: inclusive → holds.
        let on_edge = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (3600, ev("Alert", &[])),
        ]);
        assert!(
            holds(&on_edge, body),
            "witness exactly at the edge is included"
        );

        // Login 3601s before: just outside → fails.
        let past_edge = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (3601, ev("Alert", &[])),
        ]);
        assert!(
            !holds(&past_edge, body),
            "witness one second past the edge is excluded"
        );
    }

    // ─── entity-typed exists binder ─────────────────────────────────

    #[test]
    fn exists_entity_typed_binder_correlates_principals() {
        // Bind an *entity* (not a String/Long): "some principal both logged
        // in AND was denied — the same principal entity". Exercises the
        // entity path through an `exists` binder and its correlation.
        let body = r#"exists (pr: Drupe::OAuthUser). (formerly within 1h Drupe::Action::"Login"::request{ callerPrincipal: pr } && formerly within 1h Drupe::Action::"Deny"::request{ callerPrincipal: pr })"#;

        // Positive: alice logs in and alice is denied.
        let same = trace(&[
            (0, ev_pr("Login", "alice")),
            (1, ev_pr("Deny", "alice")),
            (5, ev_pr("Alert", "alice")),
        ]);
        assert!(holds(&same, body), "same principal entity correlates");

        // Negative: alice logs in but BOB is denied — no single principal
        // entity does both.
        let diff = trace(&[
            (0, ev_pr("Login", "alice")),
            (1, ev_pr("Deny", "bob")),
            (5, ev_pr("Alert", "alice")),
        ]);
        assert!(
            !holds(&diff, body),
            "different principal entities do not correlate"
        );
    }

    // ─── temporal operator WRAPPING an exists (formerly-of-exists) ──

    #[test]
    fn formerly_of_exists_body() {
        // A `formerly` whose body is itself an `exists` — the temporal
        // operator nests OVER the existential (all prior cases had `exists`
        // outermost). "At some past in-window point, there existed a
        // transfer over 100." The inner `exists` is evaluated at each
        // scanned past timepoint.
        let body = r#"formerly within 1h (exists (a: Long). (Drupe::Action::"Transfer"::request{ input.amount: a } && a > 100))"#;

        let big = trace(&[
            (0, ev("Transfer", &[("amount", n(200))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(holds(&big, body), "a past transfer over 100 existed");

        let small = trace(&[
            (0, ev("Transfer", &[("amount", n(50))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(!holds(&small, body), "no past transfer exceeded 100");
    }

    // ─── compound exists body with a negated conjunct ───────────────

    #[test]
    fn exists_compound_body_with_negation() {
        // `exists (u). (formerly Login{u} && !formerly Logout{u})` — a
        // bounded-lookback "open session" (contrast ea_0016, which uses
        // `since`): some user logged in and has NO logout in the window.
        let body = r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && !formerly within 1h Drupe::Action::"Logout"::request{ input.user: u })"#;

        // alice logged in, never logged out → open.
        let open = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(holds(&open, body), "login with no logout → session open");

        // alice logged in AND out → closed (and no other user is open).
        let closed = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (1, ev("Logout", &[("user", s("alice"))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(!holds(&closed, body), "login then logout → session closed");
    }

    // ─── range constraint on the bound var (0 < n < 10) ─────────────

    #[test]
    fn exists_binder_with_range_constraint() {
        // `exists (n). ((count …) == n && n > 0 && n < 10)` — a compound
        // body constraining the bound var on BOTH sides (the
        // `let n = … in (0 < n && n < 2)` shape, which the migration
        // flattened; tested directly here).
        let body = r#"exists (nn: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp(t)))) == nn && nn > 0 && nn < 10)"#;

        // One login: 0 < 1 < 10 → holds.
        let one = trace(&[(0, ev("Login", &[])), (5, ev("Alert", &[]))]);
        assert!(holds(&one, body), "count 1 is in (0, 10)");

        // Zero logins: 0 is not > 0 → fails the lower bound.
        let none = trace(&[
            (0, ev("Transfer", &[("amount", n(1))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(!holds(&none, body), "count 0 fails the lower bound");
    }

    // ─── negated aggregate comparison in the body ──────────────────

    #[test]
    fn exists_negated_aggregate_comparison() {
        // `exists (n). ((count …) == n && !(n == 0))` — a negated
        // comparison on the bound var. Semantically "count is nonzero", but
        // exercises `!` wrapping a comparison inside an `exists` body.
        let body = r#"exists (nn: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp(t)))) == nn && !(nn == 0))"#;

        let one = trace(&[(0, ev("Login", &[])), (5, ev("Alert", &[]))]);
        assert!(holds(&one, body), "count 1 → !(1 == 0) holds");

        let none = trace(&[
            (0, ev("Transfer", &[("amount", n(1))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(!holds(&none, body), "count 0 → !(0 == 0) is false");
    }

    // ─── Relational binding through Previous / Since / Not ──────────
    //
    // The temporal operators are RELATIONAL (see the MFOTL monitoring
    // semantics): `previous ψ` binds
    // `free(ψ)` (its rows at i are ψ's rows at i-1), and `ψ since ψ'` binds
    // `free(ψ) ∪ free(ψ')` (the anchor ψ' held at some in-window j, ψ at
    // every step after). In relational context (inside `exists` / a `where`
    // body), a variable reached through these operators must actually bind
    // and correlate — not stay free. These tests pin that behavior.

    #[test]
    fn relational_previous_binds_and_correlates() {
        // `exists (u). (previous within 1h Login{user:u} && u == "alice")`.
        // The previous event is a Login by BOB, so `previous` binds u := bob
        // and `u == "alice"` fails → false. (A `previous` that failed to
        // bind would let the equality bind u freely, giving a spurious true.)
        let tr = trace(&[
            (0, ev("Login", &[("user", s("bob"))])),
            (5, ev("Alert", &[])),
        ]);
        let body = r#"exists (u: String). (previous within 1h Drupe::Action::"Login"::request{ input.user: u } && u == "alice")"#;
        assert!(
            !holds(&tr, body),
            "previous login was bob; u must bind to bob, so u==alice is false"
        );

        // Order-independence: eq first, previous second — same answer.
        let body_rev = r#"exists (u: String). (u == "alice" && previous within 1h Drupe::Action::"Login"::request{ input.user: u })"#;
        assert!(
            !holds(&tr, body_rev),
            "u==alice but previous login was bob → no witness"
        );

        // Positive control: previous login IS alice → true.
        let tr_alice = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(
            holds(&tr_alice, body),
            "previous login is alice → u binds alice → u==alice holds"
        );
    }

    #[test]
    fn relational_previous_counts_distinct_bound_rows() {
        // A `count` over a `previous`-bound var must reflect the ACTUAL
        // bound user, not just "was there a previous login". We filter the
        // `for` domain on a specific user: `count for (u). where (previous
        // Login{user:u} && u == "alice")`. When the previous login is BOB,
        // the correct count is 0 (bob != alice), so `n == 0` must hold — the
        // `previous` must carry the u binding into the count's projection.
        let body = r#"exists (n: Long). ((count for (u: String). where (previous within 1h Drupe::Action::"Login"::request{ input.user: u } && u == "alice")) == n && n == 0)"#;
        let prev_bob = trace(&[
            (0, ev("Login", &[("user", s("bob"))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(
            holds(&prev_bob, body),
            "previous login is bob, not alice → count of alice-logins is 0"
        );

        // Positive control: previous login IS alice → count 1, so n==0 is
        // false.
        let body_one = r#"exists (n: Long). ((count for (u: String). where (previous within 1h Drupe::Action::"Login"::request{ input.user: u } && u == "alice")) == n && n == 1)"#;
        let prev_alice = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(
            holds(&prev_alice, body_one),
            "previous login is alice → count of alice-logins is 1"
        );
    }

    #[test]
    fn relational_since_binds_anchor_and_correlates() {
        // `exists (u). ((!Logout{u}) since within 1h Login{u} && u == "bob")`
        // — the open-session pattern, but asking specifically about bob. The
        // `since` binds u to the anchoring Login's user. Only alice has an
        // open session, so u==bob must be false.
        let only_alice = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (5, ev("Alert", &[])),
        ]);
        let body_bob = r#"exists (u: String). (!Drupe::Action::"Logout"::request{ input.user: u } since within 1h Drupe::Action::"Login"::request{ input.user: u } && u == "bob")"#;
        assert!(
            !holds(&only_alice, body_bob),
            "only alice's session is open; u must bind alice, so u==bob is false"
        );

        // Positive control: ask about alice → true.
        let body_alice = r#"exists (u: String). (!Drupe::Action::"Logout"::request{ input.user: u } since within 1h Drupe::Action::"Login"::request{ input.user: u } && u == "alice")"#;
        assert!(
            holds(&only_alice, body_alice),
            "alice's session is open and u binds alice → u==alice holds"
        );
    }

    #[test]
    fn relational_since_every_step_holds_over_bound_var() {
        // `since` requires the LEFT to hold at every step in (j, i] under the
        // anchor's binding — including the decision point i. We use the
        // negated-left "open session" form (`!Logout{u}`), which is what
        // actually holds at a decision point (a positive-left since is
        // vacuously broken there, since the decision event matches neither).
        // The "every step" requirement then means: no Logout{u} at ANY step
        // after the login, under the bound u.
        let body = r#"exists (u: String). (!Drupe::Action::"Logout"::request{ input.user: u } since within 1h Drupe::Action::"Login"::request{ input.user: u })"#;

        // BROKEN: alice logs in @0, logs out @1 → the `!Logout` step fails at
        // k=1 under u=alice, so the since is false for alice (and no other
        // user is open).
        let broken = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (1, ev("Logout", &[("user", s("alice"))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(
            !holds(&broken, body),
            "alice logged out at a step after login → !Logout fails, since false"
        );

        // HELD: alice logs in and never logs out → `!Logout` holds at every
        // step after the login, so the since holds under u=alice.
        let held = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (1, ev("Read", &[("user", s("alice"))])),
            (2, ev("Read", &[("user", s("alice"))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(
            holds(&held, body),
            "alice never logged out → !Logout at every step → since holds"
        );
    }

    #[test]
    fn relational_guarded_negation_antijoin() {
        // Guarded negation `α ∧ ¬β` sharing a bound var: `exists (u).
        // (formerly Login{u} && !formerly Logout{u})` — some user logged in
        // and did NOT log out (an open session). The `!formerly Logout{u}`
        // must anti-join the u bound by the left; negation
        // contributes no range restriction, so `u` is bound by the Login and
        // the negation only filters it. (An UNGUARDED `exists (u). !…{u}` is
        // rejected by the checker — negation restricts nothing.)
        let body = r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && !formerly within 1h Drupe::Action::"Logout"::request{ input.user: u })"#;

        // alice logs in, BOB logs out → alice's session is open (the anti-
        // join must NOT let bob's logout cancel alice) → true.
        let alice_open = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (1, ev("Logout", &[("user", s("bob"))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(
            holds(&alice_open, body),
            "alice logged in and did not log out (bob's logout is a different u) → open"
        );

        // alice logs in AND out → her session is closed; no other user is
        // open → false. This is the anti-join actually removing alice.
        let alice_closed = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (1, ev("Logout", &[("user", s("alice"))])),
            (5, ev("Alert", &[])),
        ]);
        assert!(
            !holds(&alice_closed, body),
            "alice logged out → the anti-join removes u=alice, nobody open"
        );
    }

    // ─── Scope terms: `principal` / `resource` (± attribute tail) ───────
    //
    // A temporal formula's `principal` / `resource` is Cedar's request scope
    // entity, resolved against the **current** request at every timepoint the
    // operator scans. A bare root is the entity (identity); an attribute tail
    // (`principal.dept`) reads the entity's attribute from the current request's
    // entity store — the temporal analog of the provider-arg `principal.dept`
    // and a pure-Cedar `when { principal.dept }`.

    /// A `principal` entity value (`Drupe::OAuthUser::"<id>"`).
    fn oauth(id: &str) -> Value {
        Value::Entity {
            ty: "Drupe::OAuthUser".to_string(),
            id: id.to_string(),
        }
    }

    /// A single-timepoint trace whose current request has the given principal
    /// entity, that principal's supplied `attrs`, and an `input` record. This
    /// is the in-test analog of a `.log` line with a `scope(principal: …)` and
    /// an `entities(…)` envelope.
    fn scoped_trace(principal: Value, attrs: &[(&str, Value)], input: &[(&str, Value)]) -> Trace {
        let uid = match &principal {
            Value::Entity { ty, id } => super::super::value::entity_uid_string(ty, id),
            _ => panic!("principal must be an entity"),
        };
        let mut entities = BTreeMap::new();
        let mut attr_map = BTreeMap::new();
        for (k, v) in attrs {
            attr_map.insert(k.to_string(), v.clone());
        }
        entities.insert(
            uid,
            super::super::value::EntityRecord {
                attrs: attr_map,
                parents: Vec::new(),
            },
        );

        let mut event = ev("Read", input);
        event.entities = entities;
        // Mirror the scope principal into `logged["callerPrincipal"]`, exactly
        // as `EventBuilder::principal` / the `.log` scope envelope do — the
        // provider-arg resolver reads the scope-entity uid from there, so a
        // well-formed event keeps `scope.principal` and that logged alias in
        // sync.
        event
            .logged
            .insert("callerPrincipal".to_string(), principal.clone());

        Trace {
            points: vec![Event {
                ts: 0,
                scope: Scope {
                    principal: Some(principal),
                    resource: None,
                },
                event,
            }],
        }
    }

    #[test]
    fn temporal_reads_current_principal_attribute() {
        // `principal.dept == "eng"` reads the current request's principal
        // attribute from the entity store — the Stage-3 capability.
        let body = r#"principal.dept == "eng""#;

        let eng = scoped_trace(oauth("alice"), &[("dept", s("eng"))], &[]);
        assert!(holds(&eng, body), "alice.dept == eng should hold");

        // Paired negative: a different dept does not match.
        let sales = scoped_trace(oauth("alice"), &[("dept", s("sales"))], &[]);
        assert!(!holds(&sales, body), "alice.dept == sales, so eng is false");
    }

    #[test]
    fn temporal_reads_escaped_id_principal_attribute() {
        // The temporal `principal.<attr>` path must resolve for a principal
        // whose id contains an escaped quote (`a"b`). `seed_scope_env` keys the
        // store via `entity_uid_string` (escaped) and the lookup reconstructs
        // the same key, so an escaped id is not missed — the store-key
        // canonicalization on the temporal side, not just the provider side.
        let body = r#"principal.dept == "eng""#;
        let tr = scoped_trace(oauth("a\"b"), &[("dept", s("eng"))], &[]);
        assert!(
            holds(&tr, body),
            "escaped-id principal's dept must resolve in a temporal read"
        );
        // Also a backslash-only id (`a\b`), the other escape `entity_uid_string`
        // handles.
        let bs = scoped_trace(oauth("a\\b"), &[("dept", s("eng"))], &[]);
        assert!(
            holds(&bs, body),
            "backslash-id principal's dept must resolve too"
        );
    }

    #[test]
    fn temporal_reads_nested_principal_attribute() {
        // A nested attribute path (`principal.address.zone`) resolves by
        // descent — parity with the provider-arg nested case.
        let body = r#"principal.address.zone == "z1""#;

        let mut address = BTreeMap::new();
        address.insert("zone".to_string(), s("z1"));
        let tr = scoped_trace(oauth("alice"), &[("address", Value::Object(address))], &[]);
        assert!(holds(&tr, body), "nested principal.address.zone resolves");

        let mut other = BTreeMap::new();
        other.insert("zone".to_string(), s("z2"));
        let neg = scoped_trace(oauth("alice"), &[("address", Value::Object(other))], &[]);
        assert!(!holds(&neg, body), "z2 != z1");
    }

    #[test]
    fn temporal_scope_id_and_type_fall_back_to_uid() {
        // With no supplied attributes, `.id` / `.type` project the uid — the
        // fallback branch (guards identity-only traces).
        let tr = scoped_trace(oauth("alice"), &[], &[]);
        assert!(
            holds(&tr, r#"principal.id == "alice""#),
            ".id is the uid id"
        );
        assert!(
            holds(&tr, r#"principal.type == "Drupe::OAuthUser""#),
            ".type is the uid type"
        );
    }

    #[test]
    fn temporal_bare_principal_is_the_entity_identity() {
        // A bare `principal` compares as the whole entity (identity) — this is
        // the case the old `context.principal` alias served, now spelled
        // `principal`. Guards that the bare-root path still resolves after the
        // key-scheme change.
        let tr = scoped_trace(oauth("alice"), &[], &[]);
        assert!(
            holds(&tr, r#"principal == Drupe::OAuthUser::"alice""#),
            "bare principal equals its entity literal"
        );
        assert!(
            !holds(&tr, r#"principal == Drupe::OAuthUser::"bob""#),
            "bare principal is not a different entity"
        );
    }

    #[test]
    fn temporal_resource_attribute_symmetry() {
        // The resource side resolves symmetrically. Build a trace with a
        // resource scope + supplied resource attribute.
        let resource = Value::Entity {
            ty: "Drupe::Gateway".to_string(),
            id: "gw1".to_string(),
        };
        let mut attrs = BTreeMap::new();
        attrs.insert("owner".to_string(), s("alice"));
        let mut entities = BTreeMap::new();
        entities.insert(
            "Drupe::Gateway::\"gw1\"".to_string(),
            super::super::value::EntityRecord {
                attrs,
                parents: Vec::new(),
            },
        );
        let mut event = ev("Read", &[]);
        event.entities = entities;
        let tr = Trace {
            points: vec![Event {
                ts: 0,
                scope: Scope {
                    principal: None,
                    resource: Some(resource),
                },
                event,
            }],
        };
        assert!(
            holds(&tr, r#"resource.owner == "alice""#),
            "resource.owner resolves symmetrically to principal"
        );
    }

    #[test]
    fn temporal_unsupplied_attribute_does_not_match() {
        // An attribute the entity store does not carry is unresolved → the
        // comparison simply does not hold (fail-safe, no crash), matching the
        // provider side's `Value::Null`-for-absent behavior.
        let tr = scoped_trace(oauth("alice"), &[], &[]);
        assert!(
            !holds(&tr, r#"principal.dept == "eng""#),
            "no dept supplied → the comparison does not hold"
        );
    }

    #[test]
    fn temporal_context_principal_is_a_context_field_not_the_scope() {
        // Post-change, `context.principal` is an ordinary context field named
        // `principal` (Cedar semantics), NOT the scope entity. With no such
        // context field it is unresolved, so an identity comparison against the
        // scope entity does NOT hold — proving the alias is gone.
        let tr = scoped_trace(oauth("alice"), &[], &[]);
        assert!(
            !holds(&tr, r#"context.principal == Drupe::OAuthUser::"alice""#),
            "context.principal is a context field, not the scope entity"
        );
        // The scope entity is now reached via the bare `principal` root.
        assert!(holds(&tr, r#"principal == Drupe::OAuthUser::"alice""#));
    }

    #[test]
    fn temporal_supplied_id_attribute_overrides_uid_projection() {
        // A supplied attribute literally named `id` / `type` WINS over the uid
        // projection (the `entry().or_insert` "supplied wins" branch in
        // `seed_scope_env`), matching `resolve_scope_path`, where the supplied
        // attribute is looked up before the `.id`/`.type` uid fallback. Here the
        // supplied `id` is "override", not the uid's "alice".
        let tr = scoped_trace(
            oauth("alice"),
            &[("id", s("override")), ("type", s("Custom"))],
            &[],
        );
        assert!(
            holds(&tr, r#"principal.id == "override""#),
            "a supplied `id` attribute wins over the uid id"
        );
        assert!(
            !holds(&tr, r#"principal.id == "alice""#),
            "the uid projection must not shadow the supplied `id`"
        );
        assert!(
            holds(&tr, r#"principal.type == "Custom""#),
            "a supplied `type` attribute wins over the uid type"
        );
    }

    #[test]
    fn temporal_null_scope_attribute_does_not_match() {
        // A supplied `Value::Null` attribute means "absent" (consistent with the
        // Cedar-store Null-is-absent handling): `principal.dept == "x"` yields
        // `Null.dom_eq(String) == false`, so it does not match a present value —
        // never coerced to an empty/default that a guard could match.
        let tr = scoped_trace(oauth("alice"), &[("dept", Value::Null)], &[]);
        assert!(
            !holds(&tr, r#"principal.dept == "eng""#),
            "a Null scope attribute must not match a present value"
        );
        assert!(
            !holds(&tr, r#"principal.dept == """#),
            "a Null scope attribute must not coerce to the empty string"
        );
    }

    #[test]
    fn temporal_mid_path_scalar_deeper_path_is_unresolved() {
        // A deeper path whose intermediate segment is a scalar
        // (`principal.dept.x` where `dept` is a String) is unresolvable — the
        // scalar `@principal.dept` seeds no `@principal.dept.x` key, so the term
        // resolves to `None` and the comparison does not hold (parity with
        // `resolve_scope_path`'s "non-record mid-path → Null" arm). No crash.
        let tr = scoped_trace(oauth("alice"), &[("dept", s("eng"))], &[]);
        assert!(
            !holds(&tr, r#"principal.dept.x == "eng""#),
            "descending into a scalar attribute is unresolved, not a match"
        );
        // Control: the scalar itself still resolves at its own depth.
        assert!(holds(&tr, r#"principal.dept == "eng""#));
    }

    // ─── shared-resolver parity: temporal seeder ≡ provider resolver ────
    //
    // `seed_scope_env` (temporal) and `api::resolve_scope_path` (providers) both
    // delegate to `EventData::resolve_entity_attr`, so they must return the same
    // value for the same `principal.<path>` against the same entity store. This
    // drives BOTH consumers on one store across a battery of paths and asserts
    // agreement directly (the prior tests exercised each side separately). It is
    // the anti-drift guard for the "agree by construction" claim.

    #[test]
    fn scope_attr_resolution_agrees_between_temporal_and_provider() {
        use crate::api::resolve_scope_path;
        use crate::extension::temporal::ast::Term;

        // One event: principal alice with a scalar attr, a nested record attr,
        // and a supplied `id` that overrides the uid projection.
        let nested = Value::Object(BTreeMap::from([("city".to_string(), s("sea"))]));
        let tr = scoped_trace(
            oauth("alice"),
            &[
                ("dept", s("eng")),
                ("address", nested),
                ("id", s("override")),
            ],
            &[],
        );
        let i = tr.len() - 1;
        let env = request_env(&tr, i);
        let event = tr.event(i);

        // Every principal path shape the two resolvers must agree on. (A bare
        // `principal` is the whole-entity case both handle before descending —
        // covered by other tests — so this battery is the attribute paths.)
        let paths: &[&[&str]] = &[
            &["principal", "dept"],            // supplied scalar
            &["principal", "address", "city"], // nested descent
            &["principal", "address"],         // whole nested record
            &["principal", "id"],              // supplied `id` wins over uid
            &["principal", "type"],            // uid `.type` projection
            &["principal", "missing"],         // unsupplied → absent
            &["principal", "dept", "x"],       // mid-path scalar → absent
        ];

        for path in paths {
            let owned: Vec<String> = path.iter().map(|s| s.to_string()).collect();
            // Temporal side: resolve a `ScopeField` term against the seeded env.
            let temporal = resolve_term(&env, &Term::ScopeField(owned.clone()));
            // Provider side: resolve the same path (minus the `principal` root)
            // against the entity store. `resolve_scope_path` maps absent to
            // `Value::Null`; normalize the temporal `None` to `Null` so the two
            // "absent" encodings compare equal.
            let provider = resolve_scope_path("callerPrincipal", &owned[1..], event);
            let temporal = temporal.unwrap_or(Value::Null);
            assert_eq!(
                temporal,
                provider,
                "temporal and provider resolvers disagree on `{}`: {temporal:?} vs {provider:?}",
                path.join(".")
            );
        }
    }

    // ─── Binder shadowing / alpha-equivalence (scoping fix) ─────────
    //
    // These pin the fix for the `exists`/`for` shadowing bug: renaming a
    // *bound* variable must never change a formula's verdict (alpha-
    // equivalence), and a binder must genuinely shadow — never silently
    // degrade into an equality filter against an outer binding or a
    // same-named context field. See the interpreter's `Exists`/`eval_agg_expr`
    // arms and `request_env` (context vs. variable keyspace separation).

    /// Two alpha-equivalent formulas — inner binder `u` (shadowing the outer
    /// `u`) vs. inner binder `v` — must agree. The formula reads "some user
    /// logged in AND some user (any user) transferred"; the inner existential
    /// must quantify freshly regardless of the outer binder's name.
    #[test]
    fn exists_shadowing_alpha_equivalence() {
        // alice logs in; bob (and only bob) transfers.
        let tr = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (5, ev("Transfer", &[("user", s("bob"))])),
            (10, ev("Alert", &[])),
        ]);
        let shadowed = r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && exists (u: String). formerly within 1h Drupe::Action::"Transfer"::request{ input.user: u })"#;
        let renamed = r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && exists (v: String). formerly within 1h Drupe::Action::"Transfer"::request{ input.user: v })"#;
        let a = holds(&tr, shadowed);
        let b = holds(&tr, renamed);
        assert_eq!(a, b, "alpha-equivalent formulas disagree: shadowing bug");
        // Both must be true: alice logged in, bob transferred.
        assert!(a, "some login AND some transfer both occur; must hold");
    }

    /// The aggregate-`for` analogue: an inner `count for (u)` whose domain
    /// variable shadows an outer `exists (u)` must count all matching rows,
    /// not collapse to the single outer-bound value. Renaming the `for`
    /// binder must not change the count.
    #[test]
    fn for_binder_shadowing_alpha_equivalence() {
        // alice logs in; bob and carol transfer (two distinct transferers).
        let tr = trace(&[
            (0, ev("Login", &[("user", s("alice"))])),
            (3, ev("Transfer", &[("user", s("bob"))])),
            (5, ev("Transfer", &[("user", s("carol"))])),
            (10, ev("Alert", &[])),
        ]);
        // "alice logged in AND at least 2 distinct users transferred in the
        // past hour" — the inner `for` binder shadows the outer `u`.
        let shadowed = r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && (count for (u: String), (t: Timepoint). where (formerly within 1h (Drupe::Action::"Transfer"::request{ input.user: u } && tp(t)))) >= 2)"#;
        let renamed = r#"exists (u: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: u } && (count for (w: String), (t: Timepoint). where (formerly within 1h (Drupe::Action::"Transfer"::request{ input.user: w } && tp(t)))) >= 2)"#;
        let a = holds(&tr, shadowed);
        let b = holds(&tr, renamed);
        assert_eq!(
            a, b,
            "alpha-equivalent aggregate `for` binders disagree: shadowing bug"
        );
        // Both must be true: bob + carol are two distinct transferers.
        assert!(a, "two distinct users transferred; count >= 2 must hold");
    }

    /// A binder named after a **top-level context field** must quantify
    /// freshly — the binder's name coinciding with a context field must not
    /// pre-bind it (which would silently turn "some user" into "the user
    /// equal to the decision's `bar` field"). Part A (context/variable
    /// keyspace separation) + Part B (shadowing).
    #[test]
    fn binder_named_after_toplevel_context_field_quantifies_freshly() {
        // alice logs in; the DECISION's context carries an unrelated
        // top-level field `bar = "zzz"`.
        let mut decision = ev("Alert", &[]);
        decision.request_context.insert("bar".to_string(), s("zzz"));
        let tr = trace(&[(0, ev("Login", &[("user", s("alice"))])), (10, decision)]);
        // "some user logged in" — must not depend on the binder's name, and
        // must not be filtered by the same-named context field `bar`.
        let collides = r#"exists (bar: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: bar }"#;
        let control = r#"exists (other: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: other }"#;
        assert_eq!(
            holds(&tr, collides),
            holds(&tr, control),
            "binder named after a context field must quantify freshly"
        );
        assert!(holds(&tr, control), "alice logged in; existential holds");
    }

    /// Part A both directions: with the binder named after a context field,
    /// a `context.<that name>` reference inside the body must STILL resolve
    /// to the request field (not be shadowed by the fresh binder). Here the
    /// binder `bar` quantifies over Login users while `context.bar` continues
    /// to read the decision's `bar` field for a filter.
    ///
    /// This is a **stays-green guard**, not a currently-failing repro: it
    /// passes today (through the buggy pre-binding path — the same-named
    /// context field pre-binds `bar`, turning the predicate into a filter that
    /// happens to give the right answer here) AND must pass after the fix
    /// (through genuine `context.bar` resolution). It guards the Part-A/Part-B
    /// interaction: doing Part B (shed the binder from the env) WITHOUT Part A
    /// (move context to `context.`-keyed entries) would strand `context.bar`
    /// and flip this red.
    #[test]
    fn context_field_still_resolves_under_same_named_binder() {
        // A login by "zzz"; the decision's context has `bar = "zzz"`.
        let mut decision = ev("Alert", &[]);
        decision.request_context.insert("bar".to_string(), s("zzz"));
        let tr = trace(&[(0, ev("Login", &[("user", s("zzz"))])), (10, decision)]);
        // "some user logged in whose name equals the decision's context.bar".
        // The binder `bar` ranges over login users; `context.bar` must still
        // read the request field ("zzz"), so this matches the zzz login.
        let body = r#"exists (bar: String). (formerly within 1h Drupe::Action::"Login"::request{ input.user: bar } && bar == context.bar)"#;
        assert!(
            holds(&tr, body),
            "context.bar must resolve to the request field even under a binder named `bar`"
        );

        // Negative control: a login by a DIFFERENT user must not match, proving
        // `context.bar` is a real filter (="zzz"), not vacuously satisfied.
        let mut decision2 = ev("Alert", &[]);
        decision2
            .request_context
            .insert("bar".to_string(), s("zzz"));
        let tr2 = trace(&[(0, ev("Login", &[("user", s("alice"))])), (10, decision2)]);
        assert!(
            !holds(&tr2, body),
            "alice != context.bar (\"zzz\"); must not match"
        );
    }

    /// The Cedar-consistent split: `Term::ScopeField(["principal"])` is the
    /// request **scope entity**, while `Term::ContextField(["principal"])` is a
    /// context **field literally named `principal`** — two disjoint namespaces
    /// that must NOT collide, even when a context record happens to carry a
    /// field called `principal`. This is the resolver-level invariant the pin
    /// relativization depends on: a scope pin (`= principal`) reads the entity,
    /// a context pin (`= context.principal`) reads the field. (Before the split,
    /// `context.principal` was an alias for the scope entity; a regression to
    /// that would make these two resolve equal.)
    #[test]
    fn scope_field_and_context_field_named_principal_do_not_collide() {
        // A Read event whose scope principal is the alice entity, AND whose
        // request context carries a field literally named `principal` holding a
        // different (string) value.
        let mut event = ev("Read", &[]);
        event.request_context.insert(
            "principal".to_string(),
            Value::String("a-context-string".to_string()),
        );
        let tr = Trace {
            points: vec![Event {
                ts: 0,
                scope: Scope {
                    principal: Some(oauth("alice")),
                    resource: None,
                },
                event,
            }],
        };
        let env = request_env(&tr, tr.len() - 1);

        // Scope term → the request scope entity.
        assert_eq!(
            resolve_term(&env, &Term::ScopeField(vec!["principal".into()])),
            Some(oauth("alice")),
            "ScopeField(principal) must be the scope entity"
        );
        // Context term → the context field literally named `principal`.
        assert_eq!(
            resolve_term(&env, &Term::ContextField(vec!["principal".into()])),
            Some(Value::String("a-context-string".to_string())),
            "ContextField(principal) must be the context field, not the scope entity"
        );
        // And they are distinct — the whole point of the split.
        assert_ne!(
            resolve_term(&env, &Term::ScopeField(vec!["principal".into()])),
            resolve_term(&env, &Term::ContextField(vec!["principal".into()])),
        );
    }
}
