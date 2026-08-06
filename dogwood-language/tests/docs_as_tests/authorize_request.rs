//! A single stateless decision through the Cedar-parity API.
//!
//! A stateless, single-request authorization is just a fresh
//! [`Authorizer`] fed one `request`-kind [`Event`]: with no prior events,
//! there is no history for temporal leaves to see. We exercise it with a
//! pure-Cedar policy (no temporal/provider leaves) and assert the decision
//! flips with the event's input.

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema, Value,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type SellSharesInput = { shares: Long };
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  action "SellShares" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: SellSharesInput }
  };
}
"#;

// Permit SellShares only when the trade is small (a pure-Cedar `when`).
const POLICY: &str = r#"
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
when {
    context.input.shares < 100
};
"#;

/// Build a `SellShares` request-kind event whose `context.input.shares` is
/// `shares`.
fn request_event(shares: i64) -> Event {
    Event::builder("Drupe::Action::SellShares", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "shares", Value::Int(shares))
        .request_context("input", "shares", Value::Int(shares))
        .build()
}

/// Parse the policy and authorize one `SellShares` event.
fn authorize(shares: i64) -> dogwood_language::Response {
    // The default event schema (request/response) makes `request` a
    // decision kind, so `is_authorized` decides rather than returning `None`.
    let service = ServiceSchema::defaults();
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema");
    let policies = LoweredPolicySet::from_str(POLICY, &service, &policy_schema).expect("parse");
    let mut authorizer = Authorizer::new(policies);
    authorizer
        .is_authorized(&request_event(shares))
        .expect("request is a decision point")
}

#[test]
fn authorize_permits_small_trade() {
    // shares = 5 < 100 -> the `when` holds -> Allow.
    assert_eq!(authorize(5).decision(), Decision::Allow);
}

#[test]
fn authorize_denies_large_trade() {
    // shares = 500 >= 100 -> the `when` fails -> Deny.
    assert_eq!(authorize(500).decision(), Decision::Deny);
}

#[test]
fn authorize_reports_determining_rule_on_allow() {
    let response = authorize(5);
    assert_eq!(response.decision(), Decision::Allow);
    assert!(
        response.diagnostics().reason().any(|r| r.rule_index == 0),
        "expected Dogwood rule 0 to be determining",
    );
}
