//! Pins reach an aggregate inside a compound (arithmetic) operand (the
//! compound-operand pin-injection gap: correctness review §4, "shared with the
//! crate"; `dogwood-lean` README, "Pins and compound operands").
//!
//! Pin injection (`event_schema/pin.rs`) and the relativization rewrite
//! (`event_schema/relativize.rs`) handled a bare aggregate operand but skipped
//! `Term::Arith`, so under the default event schema `(count …) + 0 >= 1` counted
//! every principal's events while `(count …) >= 1` counted only the current
//! principal's. The specification injects pins through compound operands
//! (`Temporal.Term.injectPins`), and both forms deny alice on bob's history.
//!
//! EXPERIMENTAL-ARITHMETIC: runs only with the `experimental-arithmetic` feature
//! on; a default build rejects compound operands at parse time.
#![cfg(feature = "experimental-arithmetic")]

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ServiceSchema, parse_trace,
};

const SCHEMA: &str = r#"namespace Ns {
  type In = { amount: Long };
  type Out = { };
  entity User;
  entity Res;
  action "Refund" appliesTo {
    principal: [User], resource: [Res],
    context: { input: In, output?: Out }
  };
}"#;

/// Bob's settled refund, then alice's refund request.
const TRACE: &str = r#"@0 scope(principal: Ns::User::"bob", resource: Ns::Res::"r") Ns::Action::"Refund"::response(input: { amount: 5 }, output: { }, callerPrincipal: Ns::User::"bob", callerResource: Ns::Res::"r", requestId: "b1")
@10 scope(principal: Ns::User::"alice", resource: Ns::Res::"r") request_context(input: { amount: 5 }) Ns::Action::"Refund"::request(input: { amount: 5 }, callerPrincipal: Ns::User::"alice", callerResource: Ns::Res::"r", requestId: "a1")"#;

fn decisions(policy: &str, partitioned: bool) -> Vec<Decision> {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema parses");
    let lowered = LoweredPolicySet::from_str(policy, &ServiceSchema::defaults(), &schema)
        .expect("policy lowers");
    let mut builder = Authorizer::builder(lowered);
    if partitioned {
        builder = builder.partition_temporal();
    }
    let mut a = builder.build().expect("authorizer builds");
    parse_trace(TRACE)
        .expect("trace parses")
        .iter()
        .filter_map(|e| a.is_authorized(e).map(|r| r.decision()))
        .collect()
}

fn permit_when(operand: &str) -> String {
    format!(
        r#"permit (principal, action == Ns::Action::"Refund", resource)
when temporal {{ {operand} >= 1 }};"#
    )
}

const COUNT: &str = r#"(count for (t: Timepoint). where formerly within 1h (Ns::Action::"Refund"::response{} && tp(t)))"#;

/// The bare count, the count under `+ 0`, and the count under `0 +` and `1 *`
/// all deny alice: bob's refund is not hers. Under 1.1 the compound forms
/// allowed her in global mode.
#[test]
fn a_compound_operand_counts_only_the_current_principal_s_events() {
    for operand in [
        COUNT.to_string(),
        format!("{COUNT} + 0"),
        format!("0 + {COUNT}"),
        format!("1 * ({COUNT} + 0)"),
    ] {
        let policy = permit_when(&operand);
        assert_eq!(
            decisions(&policy, false),
            vec![Decision::Deny],
            "global: {operand}"
        );
        assert_eq!(
            decisions(&policy, true),
            vec![Decision::Deny],
            "partitioned: {operand}"
        );
    }
}

/// The exported leaf carries the pin inside the compound operand, as the
/// specification's pin injection does.
#[test]
fn the_exported_leaf_carries_the_pin_inside_the_compound_operand() {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
    let lowered = LoweredPolicySet::from_str(
        &permit_when(&format!("{COUNT} + 0")),
        &ServiceSchema::defaults(),
        &schema,
    )
    .unwrap();
    let leaf = lowered
        .nonrelativized_temporal_fields()
        .next()
        .expect("one leaf");
    let shown = format!("{:?}", leaf.condition.condition);
    assert!(
        shown.contains("callerPrincipal"),
        "the pin is missing: {shown}"
    );
}
