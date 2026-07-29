//! Regression tests for the temporal-guard fail-open holes found in the
//! security self-audit (findings C1 and C7).
//!
//! The README's fail-closed guarantee governs evaluation *errors*: a provider
//! or guard that cannot be computed degrades to `Deny`. But a temporal guard
//! boolean that silently evaluates to `false` is *not* an error, and two
//! mechanisms could flip such a guard the wrong way:
//!
//!   * **C1** — a backward-scanning `formerly`/`since` used a `break` the
//!     instant an event fell outside the window, assuming strictly-monotone
//!     timestamps. A single out-of-order event (untrusted input) truncated the
//!     scan before it reached the real history event, so a history-gated
//!     `forbid` never fired → the action was wrongly Allowed. Fixed by scanning
//!     with `continue` (interpreter/eval.rs).
//!   * **C7** — a `within` window with a non-positive or i64-overflowing amount
//!     made the window test unsatisfiable, silently disabling the guard. Fixed
//!     by rejecting such windows at validation time
//!     (extension/temporal/validate.rs) and by saturating `Interval::seconds`.
//!
//! These tests pin the fixed behavior so the holes cannot silently reopen.

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema, Validator, Value,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type ReadInput = { document: String };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
  action "Blocklist" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

// A history-gated FORBID: deny a Read of a document that was formerly
// blocklisted within the last hour. The security property is that once the
// blocklist event is in history, the Read is denied — regardless of the order
// in which events happened to arrive.
const FORBID_AFTER_BLOCKLIST: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource );
forbid ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Blocklist"::request{
        input.document: context.input.document
    }
};
"#;

fn authorizer_for(policy: &str) -> Authorizer {
    let service = ServiceSchema::defaults();
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    let policies = LoweredPolicySet::from_str(policy, &service, &policy_schema).expect("lowers");
    Authorizer::new(policies)
}

// The guarded (decision) Read event. Its temporal guard reads
// `context.input.document` — a *request-context* reference — so the value must
// be set with `.request_context(...)`, which populates the request context the
// Cedar decision (and the guard's RHS) is built from. `.field(...)` would put
// it in the `logged` temporal-history record, which decision-time RHS
// resolution does not read.
fn read_event(ts: i64, document: &str) -> Event {
    Event::builder("Drupe::Action::Read", "request")
        .timestamp(ts)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .request_context("input", "document", Value::String(document.to_string()))
        .build()
}

// The history Blocklist event. The predicate `…::Blocklist::request{
// input.document: … }` matches against the *logged* record, so the value goes
// in `logged` via `.field(...)`. It also carries the same value in
// request_context so it is a well-formed decision-kind event, though only the
// logged copy is read by predicate matching.
fn blocklist_event(ts: i64, document: &str) -> Event {
    Event::builder("Drupe::Action::Blocklist", "request")
        .timestamp(ts)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "document", Value::String(document.to_string()))
        .request_context("input", "document", Value::String(document.to_string()))
        .build()
}

/// C1 — sanity: with strictly-monotone timestamps, a blocklisted document's
/// Read is denied. (Establishes the guard fires at all.)
#[test]
fn forbid_fires_with_monotone_timestamps() {
    let mut auth = authorizer_for(FORBID_AFTER_BLOCKLIST);
    auth.is_authorized(&blocklist_event(100, "secret"));
    let resp = auth
        .is_authorized(&read_event(200, "secret"))
        .expect("request is a decision point");
    assert_eq!(
        resp.decision(),
        Decision::Deny,
        "a Read of a formerly-blocklisted document must be denied"
    );
}

/// C1 — the fix: an out-of-order (non-monotone) event MUST NOT blind the
/// backward scan. Here a far-future-stamped event is ingested between the
/// blocklist and the Read; the decision Read's timestamp is *earlier* than
/// that intervening event. Before the fix, the backward scan hit the
/// future-stamped event, fell outside the window, and `break`'d before ever
/// reaching the real Blocklist event — so the forbid silently did not fire and
/// the Read was Allowed (fail-open). After the fix (scan with `continue`) the
/// Blocklist event is still found and the Read is denied.
#[test]
fn forbid_still_fires_when_an_out_of_order_event_precedes_the_decision() {
    let mut auth = authorizer_for(FORBID_AFTER_BLOCKLIST);
    // 1. The real blocklist event.
    auth.is_authorized(&blocklist_event(100, "secret"));
    // 2. An intervening event with a far-future timestamp (out of order vs the
    //    decision event that follows). Any decision-kind event works.
    auth.is_authorized(&read_event(1_000_000_000, "other"));
    // 3. The guarded Read, stamped *earlier* than the intervening event.
    let resp = auth
        .is_authorized(&read_event(150, "secret"))
        .expect("request is a decision point");
    assert_eq!(
        resp.decision(),
        Decision::Deny,
        "an out-of-order intervening event must not blind the `formerly` scan \
         (C1 fail-open regression): the blocklisted Read must still be denied"
    );
}

/// C1 — equal (non-strictly-increasing) timestamps must also not blind the
/// scan. The blocklist and the Read share a timestamp; the guard must fire.
#[test]
fn forbid_still_fires_with_equal_timestamps() {
    let mut auth = authorizer_for(FORBID_AFTER_BLOCKLIST);
    auth.is_authorized(&blocklist_event(100, "secret"));
    let resp = auth
        .is_authorized(&read_event(100, "secret"))
        .expect("request is a decision point");
    assert_eq!(
        resp.decision(),
        Decision::Deny,
        "equal timestamps (delta 0, in a closed window) must still match the guard"
    );
}

// ─── C7: window validation ──────────────────────────────────────────────

fn validate_policy(policy: &str) -> dogwood_language::ValidationResult {
    let service = ServiceSchema::defaults();
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    let policies = LoweredPolicySet::from_str(policy, &service, &policy_schema).expect("lowers");
    Validator::new().validate(&policies)
}

fn window_policy(window: &str) -> String {
    format!(
        r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {{
    formerly within {window} Drupe::Action::"Blocklist"::request{{
        input.document: context.input.document
    }}
}};
"#
    )
}

/// C7 — a negative window is rejected at validation time. A negative window
/// makes the closed-window test unsatisfiable, silently disabling the guard.
#[test]
fn negative_window_is_rejected() {
    let result = validate_policy(&window_policy("-1h"));
    assert!(
        result.validation_errors().any(|e| {
            let m = format!("{e}");
            m.contains("must be positive")
        }),
        "a negative `within` window must be a validation error, got: {result:?}"
    );
}

/// C7 — a window whose length in seconds overflows i64 is rejected, rather than
/// silently saturating and evading the `max_window` cap.
#[test]
fn overflowing_window_is_rejected() {
    // 9223372036854775807 days * 86400 s/day overflows i64.
    let result = validate_policy(&window_policy("9223372036854775807d"));
    assert!(
        result.validation_errors().any(|e| {
            let m = format!("{e}");
            m.contains("too large") || m.contains("overflow")
        }),
        "an i64-overflowing `within` window must be a validation error, got: {result:?}"
    );
}

/// C7 — a normal positive window still validates cleanly (the new checks do
/// not reject legitimate windows).
#[test]
fn ordinary_window_still_validates() {
    let result = validate_policy(&window_policy("1h"));
    assert!(
        result.validation_passed(),
        "an ordinary `within 1h` window must still validate, got: {result:?}"
    );
}

// ─── C6: stray macro sigil in comparison-operand position ────────────────

/// C6 — a bare macro parameter sigil (`?p`) used as a comparison operand
/// outside a macro body must be rejected at lower time, NOT survive to the
/// evaluator (where `resolve_term` would panic the authorization thread on a
/// policy that otherwise looked valid). The other sigil positions (binder,
/// `within`) were already rejected; this closes the operand hole.
#[test]
fn stray_operand_sigil_is_rejected_at_lowering() {
    let policy = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    Drupe::Action::"Blocklist"::request{ input.document: context.input.document }
    && context.input.document == ?p
};
"#;
    let service = ServiceSchema::defaults();
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    let result = LoweredPolicySet::from_str(policy, &service, &policy_schema);
    assert!(
        result.is_err(),
        "a stray `?p` operand sigil must be a lowering error, not a runtime panic"
    );
    let msg = format!("{}", result.err().unwrap());
    assert!(
        msg.contains("macro parameter reference") || msg.contains("?p"),
        "the error should identify the stray sigil, got: {msg}"
    );
}
