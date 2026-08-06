//! Per-event authorization via the stateful `Authorizer`:
//! `is_authorized` returns a structured `Response` (decision + determining
//! Dogwood rules), backed by Cedar's authorizer.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, Response, ServiceSchema, parse_trace,
};

fn schema_src() -> String {
    let path = format!(
        "{}/tests/docs_as_tests/temporal_cases/documentation_0300_formerly_within_short_window/schema.cedarschema",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read_to_string(path).expect("schema")
}

/// Feed a whole `.log` trace through a fresh `Authorizer` one event at a
/// time, returning the response at each timepoint (`None` for non-decision
/// points).
fn run(policy: &str, action_schema: &str, trace_text: &str) -> Vec<Option<Response>> {
    // This temporal policy uses the request/response convention, so pass
    // that event schema explicitly (it is also the built-in default).
    let event_schema = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/request_response.dwschema"
    ))
    .expect("read request_response fixture");
    let service = ServiceSchema::builder()
        .event_schema_str(&event_schema)
        .build()
        .expect("service schema builds");
    let policy_schema =
        PolicySchema::from_cedarschema_str(action_schema).expect("policy schema builds");
    let policies = LoweredPolicySet::from_str(policy, &service, &policy_schema).expect("parse");
    let events = parse_trace(trace_text).expect("trace parses");
    let mut authorizer = Authorizer::new(policies);
    events
        .iter()
        .map(|event| authorizer.is_authorized(event))
        .collect()
}

#[test]
fn authorize_returns_verdict_with_determining_rule() {
    // A single permit gated by a temporal guard.
    let policy = r#"
        permit (
            principal,
            action == Drupe::Action::"SellShares",
            resource
        )
        when temporal {
            formerly within 1h Drupe::Action::"ApproveSale"::request{input.stock: context.input.stock}
        };
    "#;

    // ApproveSale(AMZN)@0, then SellShares(AMZN)@100 (within 1h -> guard
    // holds -> allow at tp1).
    let trace_text = r#"
@0 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: { shares: 5, stock: "AMZN" }) Drupe::Action::"ApproveSale"::request(input: { shares: 5, stock: "AMZN" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw1", requestId: "u1")
@100 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: { shares: 5, stock: "AMZN" }) Drupe::Action::"SellShares"::request(input: { shares: 5, stock: "AMZN" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw1", requestId: "u2")
"#;

    let verdicts = run(policy, &schema_src(), trace_text);

    // tp1 (SellShares) — guard holds -> Allow, determined by rule 0.
    let v1 = verdicts[1].as_ref().expect("tp1 is a decision point");
    assert_eq!(v1.decision(), Decision::Allow, "expected Allow");
    assert!(
        v1.diagnostics().reason().any(|r| r.rule_index == 0),
        "expected Dogwood rule 0 to be determining",
    );
}

#[test]
fn authorize_denies_when_guard_fails() {
    let policy = r#"
        permit (
            principal,
            action == Drupe::Action::"SellShares",
            resource
        )
        when temporal {
            formerly within 1h Drupe::Action::"ApproveSale"::request{input.stock: context.input.stock}
        };
    "#;

    // SellShares with NO prior ApproveSale -> guard fails -> Deny.
    let trace_text = r#"
@0 scope(principal: Drupe::OAuthUser::"bob", resource: Drupe::Gateway::"gw1") request_context(input: { shares: 5, stock: "MSFT" }) Drupe::Action::"SellShares"::request(input: { shares: 5, stock: "MSFT" }, callerPrincipal: Drupe::OAuthUser::"bob", callerResource: Drupe::Gateway::"gw1", requestId: "u1")
"#;

    let verdicts = run(policy, &schema_src(), trace_text);
    let v0 = verdicts[0].as_ref().expect("tp0 is a decision point");
    assert_eq!(
        v0.decision(),
        Decision::Deny,
        "expected Deny (guard failed)"
    );
}
