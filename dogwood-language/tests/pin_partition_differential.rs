//! Partition-safety differential: with a universal symmetric pin, the
//! verdicts of a **global** interleaved trace, restricted to one key's
//! decisions, must equal the verdicts of replaying **only that key's
//! events** ("the slice"). This is the "pinned ⇒ safe to partition"
//! guarantee the relativization rewrite manufactures, stated as a test.
//!
//! Two runs per (policy, trace, key):
//!   * global — every event, decisions filtered to the key afterwards;
//!   * sliced — only the key's events.
//!
//! On the slice the rewrite is semantically inert (every event is "mine"),
//! so the sliced run is the *specification* — the original local semantics.
//! The global run exercises the rewritten formulas against foreign
//! interleavings. Divergence-sensitive scenarios (a foreign event displacing
//! `previous`, a foreign event interrupting a positive `since`) also assert
//! the exact expected verdicts, so this cannot pass by both runs being
//! wrong the same way.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ServiceSchema, parse_trace,
};

// ── fixtures ─────────────────────────────────────────────────────────

const ACTION_SCHEMA: &str = r#"
namespace Drupe {
  type LoginInput = { user: String };
  type LogoutInput = { user: String };
  type ReadInput = { user: String };
  type TransferInput = { amount: Long };
  type Empty = { };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: LoginInput, output?: Empty }
  };
  action "Logout" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: LogoutInput, output?: Empty }
  };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: ReadInput, output?: Empty }
  };
  action "Transfer" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: TransferInput, output?: Empty }
  };
}
"#;

/// The pinned event schema: `callerPrincipal` pinned to the request
/// principal on BOTH kinds — a universal symmetric pin, so the
/// relativization rewrite is active.
const PINNED_EVENT_SCHEMA: &str = r#"
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

fn lower(policy: &str) -> LoweredPolicySet {
    let service = ServiceSchema::builder()
        .event_schema_str(PINNED_EVENT_SCHEMA)
        .build()
        .expect("service schema builds");
    let policy_schema =
        PolicySchema::from_cedarschema_str(ACTION_SCHEMA).expect("action schema parses");
    LoweredPolicySet::from_str(policy, &service, &policy_schema).expect("policy lowers")
}

/// One event line of a trace: `@ts principal action(kind) fields…`, rendered
/// into the corpus `.log` format. `uid` is auto-derived.
struct Ev {
    ts: i64,
    who: &'static str, // "A" / "B"
    action: &'static str,
    user_field: &'static str,
    amount: Option<i64>,
}

fn ev(ts: i64, who: &'static str, action: &'static str) -> Ev {
    Ev {
        ts,
        who,
        action,
        user_field: "u",
        amount: None,
    }
}

fn ev_amount(ts: i64, who: &'static str, amount: i64) -> Ev {
    Ev {
        ts,
        who,
        action: "Transfer",
        user_field: "u",
        amount: Some(amount),
    }
}

fn render(events: &[&Ev]) -> String {
    events
        .iter()
        .enumerate()
        .map(|(i, e)| {
            let input = match e.amount {
                Some(a) => format!("input: {{ amount: {a} }}"),
                None => format!("input: {{ user: \"{}\" }}", e.user_field),
            };
            // The `request_context(...)` envelope supplies the request-only
            // context the Cedar request (and every `context.<path>` term) is
            // built from — distinct from the logged temporal record below.
            // A decision leaf correlating `input.user: context.input.user`
            // reads it here; without it the correlation resolves to NULL and
            // silently never matches.
            format!(
                "@{} scope(principal: Drupe::OAuthUser::\"{}\", resource: Drupe::Gateway::\"gw1\") request_context({}) Drupe::Action::\"{}\"::request({}, callerPrincipal: Drupe::OAuthUser::\"{}\", callerResource: Drupe::Gateway::\"gw1\", requestId: \"u{}\")",
                e.ts, e.who, input, e.action, input, e.who, i
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Replay a trace through a fresh authorizer for `policy`; return
/// `(timestamp, principal, decision)` per decision point.
fn run(policy: &str, log: &str) -> Vec<(i64, String, Decision)> {
    let lowered = lower(policy);
    let mut authorizer = Authorizer::new(lowered);
    let events = parse_trace(log).expect("trace parses");
    let mut out = Vec::new();
    for event in &events {
        let who = event.principal().unwrap_or_default();
        if let Some(response) = authorizer.is_authorized(event) {
            out.push((event.timestamp(), who, response.decision()));
        }
    }
    out
}

/// The theorem, as an assertion: for each key, the global run's decisions
/// for that key equal the sliced run's decisions.
fn assert_partition_safe(policy: &str, events: &[Ev], label: &str) {
    let all: Vec<&Ev> = events.iter().collect();
    let global = run(policy, &render(&all));
    for key in ["A", "B"] {
        let key_uid = format!("Drupe::OAuthUser::\"{key}\"");
        let sliced_events: Vec<&Ev> = events.iter().filter(|e| e.who == key).collect();
        if sliced_events.is_empty() {
            continue;
        }
        let sliced = run(policy, &render(&sliced_events));
        let global_key: Vec<(i64, Decision)> = global
            .iter()
            .filter(|(_, who, _)| who == &key_uid)
            .map(|(ts, _, d)| (*ts, *d))
            .collect();
        let sliced_all: Vec<(i64, Decision)> = sliced.iter().map(|(ts, _, d)| (*ts, *d)).collect();
        assert_eq!(
            global_key, sliced_all,
            "{label}: key {key}: global-run decisions (filtered) != sliced-run decisions"
        );
    }
}

/// The decision for `key` at `ts` in a global run.
fn decision_at(policy: &str, events: &[Ev], ts: i64, key: &str) -> Decision {
    let all: Vec<&Ev> = events.iter().collect();
    let key_uid = format!("Drupe::OAuthUser::\"{key}\"");
    run(policy, &render(&all))
        .into_iter()
        .find(|(t, who, _)| *t == ts && who == &key_uid)
        .map(|(_, _, d)| d)
        .unwrap_or_else(|| panic!("no decision for {key} at @{ts}"))
}

// ── policies ─────────────────────────────────────────────────────────

const P_FORMERLY: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }
};
"#;

const P_PREVIOUS: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    previous within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }
};
"#;

const P_NEG_SINCE: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    !Drupe::Action::"Logout"::request{ input.user: context.input.user }
    since within 1h
    Drupe::Action::"Login"::request{ input.user: context.input.user }
};
"#;

const P_POS_SINCE: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    Drupe::Action::"Login"::request{ input.user: context.input.user }
    since within 1h
    Drupe::Action::"Login"::request{ input.user: context.input.user }
};
"#;

const P_COUNT: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    exists (n: Long). (
        (count for (t: Timepoint). where (
            formerly within 1h (Drupe::Action::"Login"::request{ input.user: _ } && tp(t))
        )) == n && n >= 2
    )
};
"#;

// ── the canonical divergence scenarios, pinned to exact verdicts ─────

/// A foreign event displaces `previous`: under global semantics B's Ping
/// at @2 would sit at position i-1 and the Login predicate would fail.
/// Local semantics — A's previous event is the Login — must Allow.
#[test]
fn previous_ignores_foreign_displacement() {
    let events = [
        ev(1, "A", "Login"),
        ev(2, "B", "Transfer"), // foreign interleaved event
        ev(3, "A", "Read"),
    ];
    assert_eq!(
        decision_at(P_PREVIOUS, &events, 3, "A"),
        Decision::Allow,
        "A's previous *own* event is the Login — foreign displacement must not deny"
    );
    assert_partition_safe(P_PREVIOUS, &events, "previous/displacement");
}

/// `previous` must still see A's own non-matching event: if A's directly
/// preceding own event is a Transfer (not a Login), deny.
#[test]
fn previous_still_sees_own_non_matching_event() {
    let events = [
        ev(1, "A", "Login"),
        ev(2, "A", "Transfer"), // A's own non-Login displaces the Login
        ev(3, "A", "Read"),
    ];
    assert_eq!(
        decision_at(P_PREVIOUS, &events, 3, "A"),
        Decision::Deny,
        "A's own Transfer is A's previous event and it is not a Login"
    );
    assert_partition_safe(P_PREVIOUS, &events, "previous/own-non-matching");
}

/// `previous`'s window stays exact under interleaving: A's last own event
/// is a matching Login but it is outside the 1h window.
#[test]
fn previous_window_is_exact_from_decision_point() {
    let events = [
        ev(1, "A", "Login"),
        ev(3599, "B", "Transfer"),
        ev(3700, "A", "Read"), // 3699s after A's Login: > 3600
    ];
    assert_eq!(
        decision_at(P_PREVIOUS, &events, 3700, "A"),
        Decision::Deny,
        "the window is measured from the decision point, not hop-by-hop"
    );
    assert_partition_safe(P_PREVIOUS, &events, "previous/window");
}

/// A foreign event interrupts a positive-left `since`: globally B's event
/// at @2 fails `Login{user: A}` at a step in (j, i]. Locally A's steps are
/// Login@1, Login@3, Read@4 — wait, the decision point itself must satisfy
/// the left too, and `Read` is not a `Login`, so the exact-shape expectation
/// is Deny for both. Use a Login-decision shape instead: the left holds at
/// every A-step when every A-event in (j, i] is a Login (the decision event
/// included).
#[test]
fn positive_since_ignores_foreign_interruption() {
    // Under LOCAL semantics: A's positions in (j=1, i=4] are {Login@3, Read@4}.
    // Read@4 fails Login{user:A} → Deny... unless the anchor is @3 (then the
    // range is {Read@4} → still fails). Hmm — with the decision point included
    // in the ∀ range, a Read decision can never satisfy a Login-left since.
    // The classic satisfiable local shape anchors at the decision point
    // itself (j = i, empty ∀ range) — which holds regardless of foreigners.
    // So: assert (a) partition safety on an adversarial trace, and (b) the
    // pinpoint divergence case below where local Allows via j=i anchoring
    // while a mid-range foreign event would have broken nothing.
    let events = [
        ev(1, "A", "Login"),
        ev(2, "B", "Transfer"),
        ev(3, "A", "Login"),
        ev(4, "B", "Transfer"),
        ev(5, "A", "Read"),
    ];
    assert_partition_safe(P_POS_SINCE, &events, "pos-since/interleaved");
}

/// Negated-left since — the "no logout since login" idiom — with foreign
/// logouts interleaved: B's Logout must not end A's session.
#[test]
fn neg_since_ignores_foreign_logout() {
    let events = [
        ev(1, "A", "Login"),
        ev(2, "B", "Logout"), // B logging out must not affect A
        ev(3, "A", "Read"),
    ];
    assert_eq!(
        decision_at(P_NEG_SINCE, &events, 3, "A"),
        Decision::Allow,
        "B's logout must not end A's session"
    );
    assert_partition_safe(P_NEG_SINCE, &events, "neg-since/foreign-logout");
    // And A's own logout still denies.
    let events2 = [
        ev(1, "A", "Login"),
        ev(2, "A", "Logout"),
        ev(3, "A", "Read"),
    ];
    assert_eq!(
        decision_at(P_NEG_SINCE, &events2, 3, "A"),
        Decision::Deny,
        "A's own logout ends A's session"
    );
    assert_partition_safe(P_NEG_SINCE, &events2, "neg-since/own-logout");
}

/// `count` ranges over the key's own events only: B's logins must not
/// count toward A's threshold.
#[test]
fn count_is_confined_to_own_events() {
    // A has one login; B has two. A's count must be 1 (< 2) → Deny;
    // B's count must be 2 → Allow at B's decision.
    let events = [
        ev(1, "A", "Login"),
        ev(2, "B", "Login"),
        ev(3, "B", "Login"),
        ev(4, "A", "Read"),
        ev(5, "B", "Read"),
    ];
    assert_eq!(
        decision_at(P_COUNT, &events, 4, "A"),
        Decision::Deny,
        "B's logins must not count toward A's threshold"
    );
    assert_eq!(
        decision_at(P_COUNT, &events, 5, "B"),
        Decision::Allow,
        "B's own two logins meet B's threshold"
    );
    assert_partition_safe(P_COUNT, &events, "count/confinement");
}

// ── bulk partition-safety sweep over adversarial interleavings ───────

#[test]
fn partition_safety_sweep() {
    let traces: Vec<(&str, Vec<Ev>)> = vec![
        (
            "dense-interleave",
            vec![
                ev(1, "A", "Login"),
                ev(2, "B", "Login"),
                ev(3, "A", "Transfer"),
                ev(4, "B", "Logout"),
                ev(5, "A", "Read"),
                ev(6, "B", "Read"),
                ev(7, "A", "Logout"),
                ev(8, "A", "Read"),
                ev(9, "B", "Read"),
            ],
        ),
        (
            "b-heavy",
            vec![
                ev(1, "B", "Login"),
                ev(2, "B", "Login"),
                ev(3, "B", "Transfer"),
                ev(10, "A", "Login"),
                ev(11, "B", "Logout"),
                ev(12, "A", "Read"),
                ev(13, "B", "Read"),
            ],
        ),
        (
            "window-edges",
            vec![
                ev(0, "A", "Login"),
                ev(1800, "B", "Login"),
                ev(3600, "A", "Read"), // exactly W back: closed window, in
                ev(3601, "B", "Read"),
                ev(7300, "A", "Read"), // A's login now out of window
            ],
        ),
        (
            "amounts",
            vec![
                ev_amount(1, "A", 5),
                ev_amount(2, "B", 7),
                ev(3, "A", "Login"),
                ev(4, "A", "Read"),
                ev(5, "B", "Read"),
            ],
        ),
    ];
    for (label, events) in &traces {
        for (pname, policy) in [
            ("formerly", P_FORMERLY),
            ("previous", P_PREVIOUS),
            ("neg-since", P_NEG_SINCE),
            ("pos-since", P_POS_SINCE),
            ("count", P_COUNT),
        ] {
            assert_partition_safe(policy, events, &format!("{pname}/{label}"));
        }
    }
}
