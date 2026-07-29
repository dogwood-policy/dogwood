//! Regression coverage for partition routing on the **logged field**, not the
//! request-side scope/context value.
//!
//! μ (the relativization rewrite) matches a candidate event only through its
//! **logged** record (`match_args` reads `event.field_path(field_path)`); the
//! pin's request-side `context_path` only names the *decision* event's
//! scope/context on the other side of the comparison. So a partition must be
//! keyed on the logged `field_path`, or "in this partition" ≠ "is a μ-event".
//!
//! The `partition_engine_equivalence` suite only exercises a scope pin over
//! all-`request` traces, where `logged[field_path] == scope[context_path]` holds
//! on every event (the request mirror) — so it cannot distinguish field_path
//! routing from context_path routing. These two cases can: each carries an event
//! whose logged pin field is present but whose *request-side* value is absent, so
//! request-side routing would send it to a bogus `<none>` partition while μ still
//! matches it via `logged`. Both must show the partitioned engine (non-relativized
//! leaves) agreeing with the global relativized engine.
//!
//! Events are built as trace strings (`scope(...)` / `request_context(...)`
//! envelopes are optional) so logged and request-side data can be set
//! independently — the builder API mirrors them together and could not express
//! the divergence.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ServiceSchema, parse_trace,
};

const ACTION_SCHEMA: &str = r#"
namespace Drupe {
  type LoginInput = { user: String };
  type ReadInput  = { user: String };
  type Empty = { };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: LoginInput, output?: Empty }
  };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: ReadInput, output?: Empty }
  };
}
"#;

/// Run the same policy through a **global** authorizer (relativized leaves) and
/// a **partitioned** authorizer (non-relativized leaves + per-key routing) built
/// from `event_schema`, and assert they agree decision-for-decision on `log`.
/// Returns the partitioned engine's decision stream for verdict pinning.
fn assert_engines_agree(
    event_schema: &str,
    policy: &str,
    log: &str,
    label: &str,
) -> Vec<(String, Decision)> {
    let lower = || {
        let service = ServiceSchema::builder()
            .event_schema_str(event_schema)
            .build()
            .expect("service schema builds");
        let policy_schema =
            PolicySchema::from_cedarschema_str(ACTION_SCHEMA).expect("action schema parses");
        LoweredPolicySet::from_str(policy, &service, &policy_schema).expect("policy lowers")
    };

    assert!(
        !lower().partition_keys().is_empty(),
        "{label}: fixture must have a universal symmetric pin"
    );

    let events = parse_trace(log).expect("trace parses");
    let mut global = Authorizer::new(lower());
    let mut partitioned = Authorizer::builder(lower())
        .partition_temporal()
        .build()
        .expect("partitioned authorizer builds");

    let mut out = Vec::new();
    for event in &events {
        let who = event.principal().unwrap_or_default();
        let g = global.is_authorized(event).map(|r| r.decision());
        let p = partitioned.is_authorized(event).map(|r| r.decision());
        assert_eq!(
            g, p,
            "{label}: global(relativized) vs partitioned(non-relativized) differ \
             at {who}: {g:?} vs {p:?}"
        );
        if let Some(d) = p {
            out.push((who, d));
        }
    }
    out
}

// ── Case 1: a scope pin with a history (`response`) event lacking a scope
//    envelope. The response carries `callerPrincipal` in its logged record but
//    no `scope(principal: …)`, so request-side routing sends it to `<none>`. ──

const SCOPE_PINNED_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:  resourceType(A),
    requestId:       String,
}
event <A>::response {
    ...inputs(A),
    ...outputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

// Permit a Read if this principal formerly logged in (any kind) within 1h.
const P_FORMERLY_LOGIN: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{}
};
"#;

#[test]
fn scope_pin_history_event_without_scope_envelope() {
    // A Login *response* for alice, logged with callerPrincipal but NO scope(…)
    // envelope (a service logging a completed call — request-side scope absent).
    // Then a Read request by alice. μ matches the response via its logged
    // callerPrincipal; field_path routing must place it in alice's partition too.
    let log = format!(
        "{}\n{}",
        // response: logged callerPrincipal, no scope envelope, no request_context.
        r#"@1 Drupe::Action::"Login"::response(input: { user: "alice" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw1", requestId: "u1")"#,
        // read request by alice (well-formed, mirrored).
        r#"@2 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: { user: "alice" }) Drupe::Action::"Read"::request(input: { user: "alice" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw1", requestId: "u2")"#,
    );
    let decisions =
        assert_engines_agree(SCOPE_PINNED_SCHEMA, P_FORMERLY_LOGIN, &log, "scope/history");
    // The Read (only decision event) must be permitted: alice's own prior Login
    // response is in her partition. Under the OLD request-side routing the
    // response fell into `<none>`, so the partitioned engine would have denied.
    let read = decisions
        .iter()
        .find(|(who, _)| who.contains("alice"))
        .map(|(_, d)| *d);
    assert_eq!(
        read,
        Some(Decision::Allow),
        "alice's own Login *response* (logged, no scope envelope) must satisfy the formerly"
    );
}

// ── Case 2: a context pin (`pin sessionId = context.sessionId`). Context is
//    request-only / never persisted, so a history event carries sessionId only
//    in its logged record. Request-side routing → `<none>`; field_path routing
//    reads the logged sessionId, exactly as μ does. ──

const CONTEXT_PINNED_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin sessionId: String = context.sessionId,
    requestId: String,
}
event <A>::response {
    ...inputs(A),
    ...outputs(A),
    pin sessionId: String = context.sessionId,
    requestId: String,
}
"#;

// Permit a Read if a Login formerly occurred in the SAME session within 1h.
const P_FORMERLY_SESSION: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{}
};
"#;

#[test]
fn context_pin_history_event_correlates_by_session() {
    // A Login response in session "s1" — logged sessionId, but (being a history
    // record) NO request_context carrying sessionId. Then a Read request in the
    // same session s1, and a Read in a different session s2.
    let log = [
        // Login response: logged sessionId=s1, no request_context.
        r#"@1 Drupe::Action::"Login"::response(input: { user: "alice" }, sessionId: "s1", requestId: "u1")"#,
        // Read request in session s1 (its request_context supplies sessionId for
        // the decision event's own μ side; its logged sessionId=s1 routes it).
        r#"@2 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: { user: "alice" }, sessionId: "s1") Drupe::Action::"Read"::request(input: { user: "alice" }, sessionId: "s1", requestId: "u2")"#,
        // Read request in a different session s2 — must NOT see the s1 Login.
        r#"@3 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: { user: "alice" }, sessionId: "s2") Drupe::Action::"Read"::request(input: { user: "alice" }, sessionId: "s2", requestId: "u3")"#,
    ]
    .join("\n");

    let decisions = assert_engines_agree(
        CONTEXT_PINNED_SCHEMA,
        P_FORMERLY_SESSION,
        &log,
        "context/session",
    );
    // Two decision events (the two Reads), in order: s1 → Allow, s2 → Deny.
    let reads: Vec<Decision> = decisions.iter().map(|(_, d)| *d).collect();
    assert_eq!(
        reads,
        vec![Decision::Allow, Decision::Deny],
        "same-session Read permitted, cross-session Read denied (context pin routes by logged sessionId)"
    );
}
