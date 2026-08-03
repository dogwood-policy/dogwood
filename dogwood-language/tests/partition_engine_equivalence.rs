//! Partition-engine equivalence differential: the built-in in-memory temporal
//! engine, run in **partition mode** over the **non-relativized** leaves, must
//! produce the same decisions as the default engine run in **global** mode over
//! the **relativized** leaves — on the same interleaved-multi-key trace.
//!
//! This is the implementation-level companion to `pin_partition_differential`.
//! That test validates the *theorem* (global-rewritten decisions, filtered to a
//! key, equal that key's sliced decisions). This one validates the *engine
//! wiring* that exploits it:
//!
//!   * `Authorizer::new(lowered)` — default `InMemoryTemporalEngine` in Global
//!     mode, evaluating `temporal_fields()` (the RELATIVIZED leaves).
//!   * `Authorizer::builder(lowered).partition_temporal().build()` — the same
//!     engine put in Partitioned mode by the builder handshake, evaluating
//!     `nonrelativized_temporal_fields()` routed by `partition_keys()`.
//!
//! If the partition routing (`extract`/`partition_value_of`) reads each event's
//! key the same way the μ-encoding does, the two authorizers agree decision for
//! decision. A divergence is a routing bug (or a relativization bug) — either
//! way, exactly what this differential is for.
//!
//! Fixtures (schema, pinned event schema, trace renderer, policies) mirror
//! `pin_partition_differential` so the two tests exercise the same corpus.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ServiceSchema, parse_trace,
};

// ── fixtures (shared shape with pin_partition_differential) ──────────

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

/// `callerPrincipal` pinned on BOTH kinds — a universal symmetric pin, so the
/// schema yields a non-empty `partition_keys()` (root=Scope, path=["principal"])
/// and the relativization rewrite is active on the other path.
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

struct Ev {
    ts: i64,
    who: &'static str,
    action: &'static str,
    amount: Option<i64>,
}

fn ev(ts: i64, who: &'static str, action: &'static str) -> Ev {
    Ev {
        ts,
        who,
        action,
        amount: None,
    }
}
fn ev_amount(ts: i64, who: &'static str, amount: i64) -> Ev {
    Ev {
        ts,
        who,
        action: "Transfer",
        amount: Some(amount),
    }
}

fn render(events: &[Ev]) -> String {
    events
        .iter()
        .enumerate()
        .map(|(i, e)| {
            let input = match e.amount {
                Some(a) => format!("input: {{ amount: {a} }}"),
                None => "input: { user: \"u\" }".to_string(),
            };
            format!(
                "@{} scope(principal: Drupe::OAuthUser::\"{}\", resource: Drupe::Gateway::\"gw1\") request_context({}) Drupe::Action::\"{}\"::request({}, callerPrincipal: Drupe::OAuthUser::\"{}\", callerResource: Drupe::Gateway::\"gw1\", requestId: \"u{}\")",
                e.ts, e.who, input, e.action, input, e.who, i
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Replay `log` through a **global** authorizer (default engine, relativized
/// leaves) and a **partitioned** authorizer (partition_temporal, non-relativized
/// leaves), returning `(ts, principal, decision)` streams from each.
fn run_both(
    policy: &str,
    log: &str,
) -> (Vec<(i64, String, Decision)>, Vec<(i64, String, Decision)>) {
    let events = parse_trace(log).expect("trace parses");

    // Sanity: this schema must actually be in partition mode, else the test is
    // vacuous (both authorizers would run identical leaves).
    let keyed = lower(policy);
    assert!(
        !keyed.partition_keys().is_empty(),
        "fixture must have a universal symmetric pin (non-empty partition_keys)"
    );

    let mut global = Authorizer::new(lower(policy));
    let mut partitioned = Authorizer::builder(lower(policy))
        .partition_temporal()
        .build()
        .expect("partitioning engine (default in-memory) supports it");

    let mut g = Vec::new();
    let mut p = Vec::new();
    for event in &events {
        let who = event.principal().unwrap_or_default();
        if let Some(r) = global.is_authorized(event) {
            g.push((event.timestamp(), who.clone(), r.decision()));
        }
        if let Some(r) = partitioned.is_authorized(event) {
            p.push((event.timestamp(), who, r.decision()));
        }
    }
    (g, p)
}

fn assert_engines_agree(policy: &str, events: &[Ev], label: &str) {
    let log = render(events);
    let (global, partitioned) = run_both(policy, &log);
    assert_eq!(
        global, partitioned,
        "{label}: global(relativized) vs partitioned(non-relativized) decisions differ"
    );
}

// ── policies (same set as pin_partition_differential) ────────────────

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

const POLICIES: &[(&str, &str)] = &[
    ("formerly", P_FORMERLY),
    ("previous", P_PREVIOUS),
    ("neg-since", P_NEG_SINCE),
    ("pos-since", P_POS_SINCE),
    ("count", P_COUNT),
];

// ── the divergence-sensitive scenarios (mirrors pin_partition_differential) ──

#[test]
fn engines_agree_previous_displacement() {
    let events = [
        ev(1, "A", "Login"),
        ev(2, "B", "Transfer"),
        ev(3, "A", "Read"),
    ];
    assert_engines_agree(P_PREVIOUS, &events, "previous/displacement");
}

#[test]
fn engines_agree_previous_own_non_matching() {
    let events = [
        ev(1, "A", "Login"),
        ev(2, "A", "Transfer"),
        ev(3, "A", "Read"),
    ];
    assert_engines_agree(P_PREVIOUS, &events, "previous/own-non-matching");
}

#[test]
fn engines_agree_previous_window_edge() {
    let events = [
        ev(1, "A", "Login"),
        ev(3599, "B", "Transfer"),
        ev(3700, "A", "Read"),
    ];
    assert_engines_agree(P_PREVIOUS, &events, "previous/window");
}

#[test]
fn engines_agree_neg_since_foreign_logout() {
    let events = [
        ev(1, "A", "Login"),
        ev(2, "B", "Logout"),
        ev(3, "A", "Read"),
    ];
    assert_engines_agree(P_NEG_SINCE, &events, "neg-since/foreign-logout");
    let events2 = [
        ev(1, "A", "Login"),
        ev(2, "A", "Logout"),
        ev(3, "A", "Read"),
    ];
    assert_engines_agree(P_NEG_SINCE, &events2, "neg-since/own-logout");
}

#[test]
fn engines_agree_pos_since_interleaved() {
    let events = [
        ev(1, "A", "Login"),
        ev(2, "B", "Transfer"),
        ev(3, "A", "Login"),
        ev(4, "B", "Transfer"),
        ev(5, "A", "Read"),
    ];
    assert_engines_agree(P_POS_SINCE, &events, "pos-since/interleaved");
}

#[test]
fn engines_agree_count_confinement() {
    let events = [
        ev(1, "A", "Login"),
        ev(2, "B", "Login"),
        ev(3, "B", "Login"),
        ev(4, "A", "Read"),
        ev(5, "B", "Read"),
    ];
    // Pin the absolute verdicts too, so this can't pass by both engines being
    // wrong alike: A (one own login) Deny at @4; B (two own logins) Allow at @5.
    let (global, partitioned) = run_both(P_COUNT, &render(&events));
    let a_uid = "Drupe::OAuthUser::\"A\"".to_string();
    let b_uid = "Drupe::OAuthUser::\"B\"".to_string();
    let find = |v: &[(i64, String, Decision)], ts: i64, who: &str| {
        v.iter()
            .find(|(t, w, _)| *t == ts && w == who)
            .map(|(_, _, d)| *d)
    };
    assert_eq!(
        find(&partitioned, 4, &a_uid),
        Some(Decision::Deny),
        "A@4 count<2"
    );
    assert_eq!(
        find(&partitioned, 5, &b_uid),
        Some(Decision::Allow),
        "B@5 count>=2"
    );
    assert_eq!(global, partitioned, "count/confinement: engines differ");
}

// ── bulk sweep over adversarial interleavings ────────────────────────

#[test]
fn engines_agree_sweep() {
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
                ev(3600, "A", "Read"),
                ev(3601, "B", "Read"),
                ev(7300, "A", "Read"),
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
        (
            "three-keys",
            vec![
                ev(1, "A", "Login"),
                ev(2, "B", "Login"),
                ev(3, "C", "Login"),
                ev(4, "C", "Login"),
                ev(5, "A", "Read"),
                ev(6, "B", "Read"),
                ev(7, "C", "Read"),
            ],
        ),
    ];
    for (label, events) in &traces {
        for (pname, policy) in POLICIES {
            assert_engines_agree(policy, events, &format!("{pname}/{label}"));
        }
    }
}
