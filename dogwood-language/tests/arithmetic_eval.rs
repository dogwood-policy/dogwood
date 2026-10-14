//! End-to-end pins for arithmetic evaluation in temporal comparisons —
//! chiefly the per-operation clamp (saturation) semantics, which the
//! example bundles cannot observe (their values sit far from the i64
//! bounds). Spec reference: guide 08 §5.4 — out-of-range results clamp,
//! per operation, in tree order; this differs observably from evaluating
//! the whole expression at a wider precision and clamping once. Also
//! pinned here: the unresolved-atom rule for compound operands, and
//! value-macro expansion into arithmetic contexts.
//!
//! EXPERIMENTAL-ARITHMETIC: runs only with the `experimental-arithmetic`
//! feature on; a default build rejects these policies at parse time.
#![cfg(feature = "experimental-arithmetic")]

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ServiceSchema, parse_trace,
};

const SCHEMA: &str = r#"namespace Ns {
  type ActInput = { x: Long };
  type ActOutput = { };
  type SystemContext = { now: datetime };
  entity User;
  entity Res = { limit: Long };
  action "Act" appliesTo {
    principal: [User], resource: [Res],
    context: { input: ActInput, output?: ActOutput, system: SystemContext }
  };
}"#;

/// One decision point; the count of matching `Act` requests at it is 1
/// (the reflexive window includes the event being decided), so the bound
/// `n` is 1 and `n - 1` is a tp-dependent zero to build expressions on.
const TRACE: &str = r#"@0 scope(principal: Ns::User::"u", resource: Ns::Res::"r") request_context(input: { x: 1 }) Ns::Action::"Act"::request(input: { x: 1 }, callerPrincipal: Ns::User::"u", callerResource: Ns::Res::"r", requestId: "a1")"#;

fn decisions(policy: &str, trace: &str) -> Vec<Decision> {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema parses");
    let service = ServiceSchema::defaults();
    let lowered = LoweredPolicySet::from_str(policy, &service, &schema).expect("policy validates");
    let events = parse_trace(trace).expect("trace parses");
    let mut authorizer = Authorizer::new(lowered);
    events
        .iter()
        .filter_map(|e| authorizer.is_authorized(e))
        .map(|r| r.decision())
        .collect()
}

fn sole_decision(policy: &str) -> Decision {
    let mut d = decisions(policy, TRACE);
    assert_eq!(d.len(), 1, "one decision point");
    d.pop().unwrap()
}

fn guard_policy(comparison: &str) -> String {
    format!(
        r#"permit (principal, action == Ns::Action::"Act", resource)
when temporal {{
    exists (n: Long). (
        (count for (t: Timepoint). where (Ns::Action::"Act"::request{{ input.x: * }} && tp(t))) == n
        && {comparison}
    )
}};"#
    )
}

#[test]
fn addition_clamps_per_operation_in_tree_order() {
    // n - 1 = 0, then 0 + MAX = MAX, then + 5 clamps to MAX, then - 10:
    // MAX - 10 = 9223372036854775797. Wide evaluation would give MAX - 5.
    let allow = guard_policy("n - 1 + 9223372036854775807 + 5 - 10 == 9223372036854775797");
    assert_eq!(sole_decision(&allow), Decision::Allow);

    // The wide-evaluation answer must NOT hold.
    let deny = guard_policy("n - 1 + 9223372036854775807 + 5 - 10 == 9223372036854775802");
    assert_eq!(sole_decision(&deny), Decision::Deny);
}

#[test]
fn subtraction_clamps_per_operation_in_tree_order() {
    // n - 1 = 0, then 0 - MAX = -MAX, then - 5 clamps to MIN, then + 10:
    // MIN + 10 = -9223372036854775798. Wide evaluation would give -MAX + 5.
    let allow = guard_policy("n - 1 - 9223372036854775807 - 5 + 10 == -9223372036854775798");
    assert_eq!(sole_decision(&allow), Decision::Allow);

    // The wide-evaluation answer must NOT hold.
    let deny = guard_policy("n - 1 - 9223372036854775807 - 5 + 10 == -9223372036854775802");
    assert_eq!(sole_decision(&deny), Decision::Deny);
}

#[test]
fn unresolved_entity_attribute_poisons_the_compound_to_false() {
    // Trace replay carries no entity store, so `resource.limit` never
    // resolves; one unresolved atom makes the whole comparison false
    // (fail closed), never a panic or a partial evaluation.
    let deny = guard_policy("n - 1 + resource.limit <= 100");
    assert_eq!(sole_decision(&deny), Decision::Deny);

    // The same shape with a resolved atom in its place allows.
    let allow = guard_policy("n - 1 + 100 <= 100");
    assert_eq!(sole_decision(&allow), Decision::Allow);
}

/// Two decision points: at `@0` requests−responses is 1−0, at `@10` it is
/// 2−1 (the reflexive window counts the request being decided).
const NET_TRACE: &str = r#"@0 scope(principal: Ns::User::"u", resource: Ns::Res::"r") request_context(input: { x: 1 }) Ns::Action::"Act"::request(input: { x: 1 }, callerPrincipal: Ns::User::"u", callerResource: Ns::Res::"r", requestId: "a1")
@1 scope(principal: Ns::User::"u", resource: Ns::Res::"r") Ns::Action::"Act"::response(input: { x: 1 }, callerPrincipal: Ns::User::"u", callerResource: Ns::Res::"r", requestId: "a1")
@10 scope(principal: Ns::User::"u", resource: Ns::Res::"r") request_context(input: { x: 2 }) Ns::Action::"Act"::request(input: { x: 2 }, callerPrincipal: Ns::User::"u", callerResource: Ns::Res::"r", requestId: "a2")"#;

const NET_MACRO: &str = r#"
def temporal net() {
    (count for (t: Timepoint). where (formerly within 1h (Ns::Action::"Act"::request{} && tp(t))))
    - (count for (u: Timepoint). where (formerly within 1h (Ns::Action::"Act"::response{} && tp(u))))
};
"#;

#[test]
fn difference_macro_body_expands_and_evaluates() {
    // net() is 1 at both decision points (1-0, then 2-1).
    let policy = format!(
        r#"{NET_MACRO}
permit (principal, action == Ns::Action::"Act", resource)
when temporal {{ net() <= 1 }};"#
    );
    assert_eq!(
        decisions(&policy, NET_TRACE),
        [Decision::Allow, Decision::Allow]
    );
    let strict = format!(
        r#"{NET_MACRO}
permit (principal, action == Ns::Action::"Act", resource)
when temporal {{ net() <= 0 }};"#
    );
    assert_eq!(
        decisions(&strict, NET_TRACE),
        [Decision::Deny, Decision::Deny]
    );
}

#[test]
fn difference_macro_splices_with_exact_precedence() {
    // At @10: 10 * net() must be 10 * (2 - 1) = 10, NOT (10 * 2) - 1 = 19.
    // The body splices as a subtree under the multiplication, so precedence
    // is structural, with no parenthesization step to get wrong.
    let right = format!(
        r#"{NET_MACRO}
permit (principal, action == Ns::Action::"Act", resource)
when temporal {{ 10 * net() == 10 }};"#
    );
    assert_eq!(
        decisions(&right, NET_TRACE),
        [Decision::Allow, Decision::Allow]
    );
    let broken_reading = format!(
        r#"{NET_MACRO}
permit (principal, action == Ns::Action::"Act", resource)
when temporal {{ 10 * net() == 19 }};"#
    );
    assert_eq!(
        decisions(&broken_reading, NET_TRACE),
        [Decision::Deny, Decision::Deny]
    );
}

#[test]
fn value_macro_call_expands_inside_macro_term_argument() {
    // A value-macro call nested in arithmetic inside a condition-macro
    // argument: `(net() - 1)` parses as a term argument, so the arg walker
    // must expand the inner call (regression: it previously survived to
    // evaluation and panicked). net() is 1 at both decision points, so
    // `net() - 1 > 0` is false and `net() + 1 > 0` is true.
    let policy = format!(
        r#"{NET_MACRO}
def temporal exceeds(?v) {{ ?v > 0 }};
permit (principal, action == Ns::Action::"Act", resource)
when temporal {{ exceeds((net() - 1)) }};"#
    );
    assert_eq!(
        decisions(&policy, NET_TRACE),
        [Decision::Deny, Decision::Deny]
    );
    let positive = format!(
        r#"{NET_MACRO}
def temporal exceeds(?v) {{ ?v > 0 }};
permit (principal, action == Ns::Action::"Act", resource)
when temporal {{ exceeds((net() + 1)) }};"#
    );
    assert_eq!(
        decisions(&positive, NET_TRACE),
        [Decision::Allow, Decision::Allow]
    );
}

#[test]
fn multiplication_clamps_at_the_bound() {
    // 1 * MAX = MAX, then * 2 clamps to MAX.
    let allow = guard_policy("n * 9223372036854775807 * 2 == 9223372036854775807");
    assert_eq!(sole_decision(&allow), Decision::Allow);
}

/// EXPERIMENTAL-ARITHMETIC: a policy set using arithmetic validates with
/// exactly one warning naming the feature, however many policies use it.
/// This test may be deleted with the gate when the feature is released.
#[test]
fn arithmetic_warns_once_per_policy_set() {
    use dogwood_language::Validator;
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema parses");
    let service = ServiceSchema::defaults();
    let two_arith = format!(
        "{}\n{}",
        guard_policy("n - 1 == 0"),
        guard_policy("n + 1 == 2")
    );
    let lowered =
        LoweredPolicySet::from_str(&two_arith, &service, &schema).expect("policies lower");
    let result = Validator::new().validate(&lowered);
    let warnings: Vec<String> = result
        .validation_warnings()
        .map(|w| w.to_string())
        .filter(|m| m.contains("experimental"))
        .collect();
    assert_eq!(
        warnings.len(),
        1,
        "expected exactly one experimental-arithmetic warning, got: {warnings:?}"
    );
    assert!(
        warnings[0].contains("arithmetic operators are experimental"),
        "unexpected warning text: {}",
        warnings[0]
    );
}
