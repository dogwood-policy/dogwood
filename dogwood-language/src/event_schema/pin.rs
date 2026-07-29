//! Pin injection: conjoin each event's pinned fields onto every predicate
//! that names that event.
//!
//! A pinned field (declared `pin f: T = context.<...>` in the event schema,
//! formal spec §2.6 / guide "Pins" in `03-event-schema.md`) forces a correlation:
//! on *every* predicate for the event, the field is implicitly constrained to
//! a request-context value —
//! whether or not the policy author wrote it. This pass makes that implicit
//! constraint explicit by appending a `NamedArg` to each matching predicate,
//! after which the ordinary evaluator (`match_args`) enforces it like any
//! hand-written field.
//!
//! Runs after macro expansion (so `?s`-refinements are already folded to
//! concrete predicates) and before validation (so the pinned field is checked
//! like any other). The append reuses the same `NamedArg` shape a hand-written
//! or `{…}`-injected field uses — pins are indistinguishable from an authored
//! field once folded.
//!
//! The pin is appended *unconditionally*, even when the author already wrote
//! the pinned field: a pin is an invariant a policy cannot opt out of. If the
//! author's constraint agrees with the pin the second `NamedArg` is redundant
//! (both equality-check the same field against the same request value, so the
//! extra arg is a no-op); if it disagrees, the predicate becomes unsatisfiable
//! (the field cannot equal two different values at once) — so a hand-written
//! field can only *narrow* a pin, never bypass or relax it. This is the
//! double-refinement the design describes (agree → no-op; disagree →
//! unsatisfiable predicate), and it is what makes a pin unforgeable.

use super::ast::PinRoot;
use super::derive::DerivedEventSchema;
use crate::extension::temporal::ast::{
    AggExprKind, Condition, ConditionKind, NamedArg, Predicate, Term,
};

/// Inject every event's pins onto the predicates in `cond` that name it.
/// Mutates the condition in place.
pub fn inject_pins(cond: &mut Condition, schema: &DerivedEventSchema) {
    match &mut cond.kind {
        ConditionKind::And { left, right }
        | ConditionKind::Or { left, right }
        | ConditionKind::Since { left, right, .. } => {
            inject_pins(left, schema);
            inject_pins(right, schema);
        }
        ConditionKind::Not { inner }
        | ConditionKind::Formerly { body: inner, .. }
        | ConditionKind::Previous { body: inner, .. }
        | ConditionKind::Exists { body: inner, .. } => inject_pins(inner, schema),
        ConditionKind::Predicate(p) => inject_into_predicate(p, schema),
        // A refinement should be folded away before this pass (it runs after
        // macro expansion); recurse into the base defensively so a stray one
        // still gets its base predicate pinned.
        ConditionKind::Refine { base, .. } => inject_pins(base, schema),
        // An aggregate is a comparison operand (`Term::Agg`); pins reach the
        // predicates in its `where` body.
        ConditionKind::Comparison { left, right, .. } => {
            inject_into_operand(left, schema);
            inject_into_operand(right, schema);
        }
        // Leaves with no predicate to pin.
        ConditionKind::Tp { .. } | ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => {}
    }
}

/// Inject pins into an aggregate comparison operand's `where` body; a plain
/// term operand carries no predicate.
fn inject_into_operand(operand: &mut Term, schema: &DerivedEventSchema) {
    if let Term::Agg(agg) = operand {
        match &mut agg.kind {
            AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => {
                inject_pins(body, schema);
            }
            AggExprKind::Call(_) => {}
        }
    }
}

/// Append each pin of the predicate's event onto its args, unconditionally —
/// even if the author already wrote that field. A pin is an invariant the
/// policy cannot opt out of: an agreeing hand-written field makes the appended
/// arg a redundant no-op, and a disagreeing one makes the predicate
/// unsatisfiable, so a hand-written field can only narrow a pin, never bypass
/// it (see the module header).
fn inject_into_predicate(p: &mut Predicate, schema: &DerivedEventSchema) {
    let Some(event) = schema.get(&p.namespace, &p.action, &p.kind) else {
        // A predicate naming no derived event is caught by validation, not
        // here; nothing to pin.
        return;
    };
    if event.pins.is_empty() {
        return;
    }
    for pin in &event.pins {
        // A scope pin (`= principal` / `= resource`) lowers to a scope term; a
        // context pin (`= context.<path>`) to a context-field term. Both carry
        // the same dotted path shape, distinguished only by their root.
        let value = match pin.root {
            PinRoot::Scope => Term::ScopeField(pin.context_path.clone()),
            PinRoot::Context => Term::ContextField(pin.context_path.clone()),
        };
        p.args.push(NamedArg {
            name: pin.field_path.join("."),
            value,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event_schema::derive::derive;
    use crate::event_schema::parse::parse_event_schema;
    use crate::extension::temporal::parse::parse_condition;

    // A schema pinning `callerPrincipal` to the request principal, plus a
    // nested pinned session id.
    const PIN_SCHEMA: &str = r#"
        decision event <A>::request {
            ...inputs(A),
            pin callerPrincipal: principalType(A) = principal,
            requestId: String,
            __drupe: { pin session_id: String = context.__drupe.session_id },
        }
    "#;

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

    fn derived() -> DerivedEventSchema {
        let dsl = parse_event_schema(PIN_SCHEMA).unwrap();
        derive(&dsl, ACTION_SCHEMA).unwrap()
    }

    /// Parse a condition, inject pins, return the (single) predicate's arg
    /// names in order.
    fn inject_and_arg_names(body: &str) -> Vec<String> {
        let mut cond = parse_condition(body).expect("parses");
        inject_pins(&mut cond, &derived());
        let p = find_predicate(&cond).expect("has a predicate");
        p.args.iter().map(|a| a.name.clone()).collect()
    }

    fn find_predicate(c: &Condition) -> Option<&Predicate> {
        match &c.kind {
            ConditionKind::Predicate(p) => Some(p),
            ConditionKind::Not { inner }
            | ConditionKind::Formerly { body: inner, .. }
            | ConditionKind::Previous { body: inner, .. } => find_predicate(inner),
            ConditionKind::And { left, right } | ConditionKind::Since { left, right, .. } => {
                find_predicate(left).or_else(|| find_predicate(right))
            }
            _ => None,
        }
    }

    #[test]
    fn pin_is_conjoined_onto_a_bare_predicate() {
        // A hand-written predicate that mentions no reserved field still gains
        // both pins.
        let names = inject_and_arg_names(r#"Drupe::Action::"Login"::request{ input.user: u }"#);
        assert!(names.contains(&"input.user".to_string()), "{names:?}");
        assert!(
            names.contains(&"callerPrincipal".to_string()),
            "principal pin injected: {names:?}"
        );
        assert!(
            names.contains(&"__drupe.session_id".to_string()),
            "nested session pin injected: {names:?}"
        );
    }

    #[test]
    fn pin_value_is_the_context_reference() {
        let mut cond = parse_condition(r#"Drupe::Action::"Login"::request{}"#).expect("parses");
        inject_pins(&mut cond, &derived());
        let p = find_predicate(&cond).unwrap();
        let principal = p
            .args
            .iter()
            .find(|a| a.name == "callerPrincipal")
            .expect("principal pinned");
        // The scope pin (`= principal`) lowers to a scope term, not a context
        // field.
        match &principal.value {
            Term::ScopeField(path) => assert_eq!(path, &vec!["principal".to_string()]),
            other => panic!("expected scope ref, got {other:?}"),
        }
        let session = p
            .args
            .iter()
            .find(|a| a.name == "__drupe.session_id")
            .expect("session pinned");
        // The context pin (`= context.__drupe.session_id`) lowers to a
        // context-field term.
        match &session.value {
            Term::ContextField(path) => {
                assert_eq!(path, &vec!["__drupe".to_string(), "session_id".to_string()])
            }
            other => panic!("expected context ref, got {other:?}"),
        }
    }

    #[test]
    fn pin_reaches_a_predicate_nested_under_formerly() {
        // The pass must descend temporal operators — a predicate inside
        // `formerly` still gets pinned.
        let names = inject_and_arg_names(
            r#"formerly within 1h Drupe::Action::"Login"::request{ input.user: u }"#,
        );
        assert!(names.contains(&"callerPrincipal".to_string()), "{names:?}");
    }

    #[test]
    fn author_written_pinned_field_still_gets_the_pin_appended() {
        // A pin is unforgeable: even when the author wrote the pinned field
        // themselves, the pass still appends the pin's own arg. The predicate
        // then carries the field twice — the author's copy and the pin's — and
        // `match_args` equality-checks both (agree → no-op, disagree →
        // unsatisfiable). This is the "cannot be bypassed" guarantee.
        let names = inject_and_arg_names(
            r#"Drupe::Action::"Login"::request{ callerPrincipal: principal }"#,
        );
        let n = names.iter().filter(|a| *a == "callerPrincipal").count();
        assert_eq!(
            n, 2,
            "pin is appended even though the author wrote the field: {names:?}"
        );
    }

    #[test]
    fn appended_pin_carries_the_context_reference_even_when_author_disagrees() {
        // The author pins `callerPrincipal` to the *resource* (a weaker /
        // wrong correlation). The pass must still append the schema pin's
        // `principal` arg, so the predicate is forced to satisfy BOTH — an
        // unsatisfiable pair whenever principal ≠ resource. A skip-by-name
        // implementation would drop the pin here and let the author's value
        // win; always-inject makes the pin authoritative.
        let mut cond =
            parse_condition(r#"Drupe::Action::"Login"::request{ callerPrincipal: resource }"#)
                .expect("parses");
        inject_pins(&mut cond, &derived());
        let p = find_predicate(&cond).unwrap();
        let principal_args: Vec<&Term> = p
            .args
            .iter()
            .filter(|a| a.name == "callerPrincipal")
            .map(|a| &a.value)
            .collect();
        // Both the author's `resource` scope ref and the pin's `principal` scope
        // ref are present.
        assert_eq!(principal_args.len(), 2, "author arg + appended pin arg");
        let has_resource = principal_args
            .iter()
            .any(|v| matches!(v, Term::ScopeField(path) if path == &vec!["resource".to_string()]));
        let has_principal = principal_args
            .iter()
            .any(|v| matches!(v, Term::ScopeField(path) if path == &vec!["principal".to_string()]));
        assert!(has_resource, "author's resource ref kept: {p:?}");
        assert!(has_principal, "schema pin's principal ref appended: {p:?}");
    }

    #[test]
    fn nested_pin_appended_even_when_author_wrote_it() {
        // The unforgeability guarantee holds for a nested (dotted) pin too.
        let names = inject_and_arg_names(
            r#"Drupe::Action::"Login"::request{ __drupe.session_id: context.__drupe.session_id }"#,
        );
        let n = names.iter().filter(|a| *a == "__drupe.session_id").count();
        assert_eq!(
            n, 2,
            "nested pin appended alongside the author's arg: {names:?}"
        );
    }

    #[test]
    fn no_pins_leaves_predicate_untouched() {
        // Against a schema with no pins, injection is a no-op.
        let no_pin_dsl = parse_event_schema(
            r#"decision event <A>::request { ...inputs(A), requestId: String }"#,
        )
        .unwrap();
        let derived = derive(&no_pin_dsl, ACTION_SCHEMA).unwrap();
        let mut cond =
            parse_condition(r#"Drupe::Action::"Login"::request{ input.user: u }"#).unwrap();
        inject_pins(&mut cond, &derived);
        let p = find_predicate(&cond).unwrap();
        assert_eq!(p.args.len(), 1, "only the authored field remains");
    }

    // ─── Recursion into every condition structure ───────────────────
    //
    // `inject_pins` must reach every predicate, no matter how it is nested.
    // These tests parse a condition of each shape, inject, then collect the
    // arg names of *every* predicate in the tree (via a collector that mirrors
    // `inject_pins`'s own traversal) and assert each one received both pins.

    /// Collect the arg-name list of every predicate in `c`, descending exactly
    /// the structures `inject_pins` descends.
    fn all_predicate_arg_names(c: &Condition) -> Vec<Vec<String>> {
        let mut out = Vec::new();
        collect(c, &mut out);
        out
    }

    fn collect(c: &Condition, out: &mut Vec<Vec<String>>) {
        match &c.kind {
            ConditionKind::Predicate(p) => {
                out.push(p.args.iter().map(|a| a.name.clone()).collect())
            }
            ConditionKind::And { left, right }
            | ConditionKind::Or { left, right }
            | ConditionKind::Since { left, right, .. } => {
                collect(left, out);
                collect(right, out);
            }
            ConditionKind::Not { inner }
            | ConditionKind::Formerly { body: inner, .. }
            | ConditionKind::Previous { body: inner, .. }
            | ConditionKind::Exists { body: inner, .. } => collect(inner, out),
            ConditionKind::Refine { base, .. } => collect(base, out),
            ConditionKind::Comparison { left, right, .. } => {
                collect_term(left, out);
                collect_term(right, out);
            }
            ConditionKind::Tp { .. } | ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => {}
        }
    }

    fn collect_term(t: &Term, out: &mut Vec<Vec<String>>) {
        if let Term::Agg(agg) = t {
            match &agg.kind {
                AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => {
                    collect(body, out)
                }
                AggExprKind::Call(_) => {}
            }
        }
    }

    /// Parse `body`, inject pins, and assert that exactly `expected` predicates
    /// were found and *every* one carries both the principal and the nested
    /// session pin.
    fn assert_every_predicate_pinned(body: &str, expected: usize) {
        let mut cond = parse_condition(body).expect("parses");
        inject_pins(&mut cond, &derived());
        let preds = all_predicate_arg_names(&cond);
        assert_eq!(
            preds.len(),
            expected,
            "found {} predicates, expected {expected}: {preds:?}",
            preds.len()
        );
        for names in &preds {
            assert!(
                names.iter().any(|n| n == "callerPrincipal"),
                "principal pin reached predicate {names:?}"
            );
            assert!(
                names.iter().any(|n| n == "__drupe.session_id"),
                "nested session pin reached predicate {names:?}"
            );
        }
    }

    #[test]
    fn pin_reaches_both_conjuncts_of_an_and() {
        assert_every_predicate_pinned(
            r#"Drupe::Action::"Login"::request{ input.user: u } && Drupe::Action::"Login"::request{ input.user: v }"#,
            2,
        );
    }

    #[test]
    fn pin_reaches_a_predicate_under_negation() {
        assert_every_predicate_pinned(r#"!Drupe::Action::"Login"::request{ input.user: u }"#, 1);
    }

    #[test]
    fn pin_reaches_both_sides_of_a_since() {
        assert_every_predicate_pinned(
            r#"Drupe::Action::"Login"::request{ input.user: u } since within 1h Drupe::Action::"Login"::request{ input.user: v }"#,
            2,
        );
    }

    #[test]
    fn pin_reaches_a_predicate_under_exists() {
        assert_every_predicate_pinned(
            r#"exists (u: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: u }"#,
            1,
        );
    }

    #[test]
    fn pin_reaches_a_predicate_inside_a_count_aggregate_body() {
        // The predicate lives in the `where` body of a `count` aggregate, which
        // is a comparison operand — the deepest place `inject_pins` must reach.
        assert_every_predicate_pinned(
            r#"exists (n: Long). ((count for (t: Timepoint). where (Drupe::Action::"Login"::request{ input.user: _ } && tp(t))) == n && n > 0)"#,
            1,
        );
    }

    #[test]
    fn pin_reaches_a_predicate_inside_a_sum_aggregate_body() {
        assert_every_predicate_pinned(
            r#"exists (total: Long). ((sum a for (a: Long). where Drupe::Action::"Login"::request{ input.user: _, input.amount: a }) == total && total > 0)"#,
            1,
        );
    }
}
