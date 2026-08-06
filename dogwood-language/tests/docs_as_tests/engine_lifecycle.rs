//! End-to-end demo of the canonical API: build a `ServiceSchema` and a
//! `PolicySchema`, parse + lower to a `LoweredPolicySet`, validate it, then
//! feed a stateful `Authorizer` one event at a time and check the
//! per-timepoint decisions.

use std::path::Path;

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ServiceSchema, Validator, parse_trace,
};

fn fixture() -> (String, String, String) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/docs_as_tests/temporal_cases/documentation_0300_formerly_within_short_window");
    let policy = std::fs::read_to_string(dir.join("policy_1.dw")).unwrap();
    let schema = std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap();
    let trace = std::fs::read_to_string(dir.join("trace_1.log")).unwrap();
    (policy, schema, trace)
}

#[test]
fn build_parse_validate_authorize_temporal_policy() {
    let (policy, action_schema_src, trace_log) = fixture();

    let event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .unwrap();

    // 1. Build the two schema halves: the service schema (the request/response
    //    event schema — passed explicitly here, though it is also the default)
    //    and the policy schema (the action schema).
    let service = ServiceSchema::builder()
        .event_schema_str(&event_schema)
        .build()
        .expect("service schema builds");
    let policy_schema =
        PolicySchema::from_cedarschema_str(&action_schema_src).expect("policy schema builds");

    // 2. Parse + lower to a LoweredPolicySet.
    let policies = LoweredPolicySet::from_str(&policy, &service, &policy_schema).expect("parse");

    // A temporal leaf was hoisted (so the compiled Cedar is NOT
    // self-contained). The public API exposes the *presence* of hoisted
    // temporal/provider leaves via `is_self_contained_cedar`, not their count.
    assert!(
        !policies.is_self_contained_cedar(),
        "the temporal guard should hoist a leaf, so the policy is not self-contained Cedar",
    );

    // 3. Validate cleanly against the (augmented) schema.
    let result = Validator::new().validate(&policies);
    assert!(
        result.validation_passed(),
        "validation errors: {:?}",
        result
            .validation_errors()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );

    // 4. Build a stateful authorizer, then feed events one at a time.
    let mut authorizer = Authorizer::new(policies);

    let events = parse_trace(&trace_log).expect("trace parses");
    let decisions: Vec<Option<Decision>> = events
        .iter()
        .map(|event| authorizer.is_authorized(event).map(|r| r.decision()))
        .collect();

    // tp0 ApproveSale: permit (scoped to SellShares) doesn't apply -> Deny.
    // tp1 SellShares(AMZN): ApproveSale(AMZN) within 1h -> `unless` fires -> Deny.
    // tp2 SellShares(MSFT): out of window + stock mismatch -> permit holds -> Allow.
    assert_eq!(
        decisions,
        vec![
            Some(Decision::Deny),
            Some(Decision::Deny),
            Some(Decision::Allow),
        ],
        "per-timepoint decisions"
    );
}
