//! `LoweredPolicySet::check_event_conformance` runs exactly the event
//! conformance an `Authorizer` checks before it ingests an event.
//!
//! For each event, under each mirror rule, the method's answer is compared with
//! what a fresh authorizer built from the same set with that rule does with the
//! event: a history event it ingests (`submit` returns `Ok(None)`) or rejects
//! (`Err(Rejection::Nonconforming)`, which must equal the method's `Err`), and a
//! decision event it ingests or fails closed with
//! `nonconforming decision event: <reason>` (whose reason must equal the
//! method's). The cases cover every clause of the check, and the whole-corpus
//! test runs the comparison over every event of the test corpora.

#[path = "support/slicing.rs"]
mod support;

use std::path::Path;

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, MirrorRule, PolicySchema, Rejection,
    ServiceSchema, Value, parse_trace,
};

const SCHEMA: &str = r#"
namespace Drupe {
  entity Gateway;
  entity OAuthUser;
  entity Level enum ["low", "high"];
  type LoginInput = { user: String, level: Level };
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: LoginInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: LoginInput }
  };
}
"#;

/// `request` decides, `response` is history. `owner` is typed by text, once
/// qualified and once relative to the action's namespace.
const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource: resourceType(A),
    owner: Drupe::OAuthUser,
}
event <A>::response {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource: resourceType(A),
    owner: OAuthUser,
}
"#;

const POLICY: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
};
"#;

const RULES: [MirrorRule; 3] = [
    MirrorRule::Strict,
    MirrorRule::Current,
    MirrorRule::Unchecked,
];

fn lower() -> LoweredPolicySet {
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema parses");
    LoweredPolicySet::from_str(POLICY, &service, &schema).expect("policy lowers")
}

fn string(s: &str) -> Value {
    Value::String(s.to_string())
}

fn entity(ty: &str, id: &str) -> Value {
    Value::Entity {
        ty: ty.to_string(),
        id: id.to_string(),
    }
}

/// An event of `action` and `kind`, conforming unless a field is changed: by
/// alice on `gw`, its `input` (logged and in the request context) with `user`
/// and `level`, and the caller fields and `owner` logged. `None` leaves a field
/// out, except that `Event::builder` logs the caller fields of the scope it is
/// given (`scope: false` gives none).
#[derive(Clone)]
struct Spec {
    action: &'static str,
    kind: &'static str,
    scope: bool,
    user: Option<Value>,
    level: Option<Value>,
    caller: Option<Value>,
    owner: Option<Value>,
}

impl Spec {
    fn new(action: &'static str, kind: &'static str) -> Self {
        Spec {
            action,
            kind,
            scope: true,
            user: Some(string("alice")),
            level: Some(entity("Drupe::Level", "low")),
            caller: Some(entity("Drupe::OAuthUser", "alice")),
            owner: Some(entity("Drupe::OAuthUser", "alice")),
        }
    }

    fn event(&self, ts: i64) -> Event {
        let mut input = std::collections::BTreeMap::new();
        if let Some(user) = &self.user {
            input.insert("user".to_string(), user.clone());
        }
        if let Some(level) = &self.level {
            input.insert("level".to_string(), level.clone());
        }
        let input = Value::Object(input);
        let mut b = Event::builder(&format!("Drupe::Action::{}", self.action), self.kind)
            .timestamp(ts)
            .logged_field("input", input.clone())
            .request_context_field("input", input);
        // A scope-less event has no resource either, so it logs none.
        if self.scope {
            b = b
                .principal("Drupe::OAuthUser::\"alice\"")
                .resource("Drupe::Gateway::\"gw\"")
                .logged_field("callerResource", entity("Drupe::Gateway", "gw"));
        }
        if let Some(caller) = &self.caller {
            b = b.logged_field("callerPrincipal", caller.clone());
        }
        if let Some(owner) = &self.owner {
            b = b.logged_field("owner", owner.clone());
        }
        b.build()
    }
}

/// What a fresh authorizer built from `set` with `rule` does with `event`, as
/// the method reports it: `Ok(())` when it ingests the event, the rejection it
/// reports for a history event, and, for a decision event it fails closed as
/// nonconforming, the same rejection with the reason it gives.
fn authorizer_verdict(
    set: &LoweredPolicySet,
    rule: MirrorRule,
    event: &Event,
) -> Result<(), Rejection> {
    let mut authorizer = Authorizer::builder(set.clone())
        .mirror_rule(rule)
        .build()
        .expect("authorizer builds");
    match authorizer.submit(event) {
        Ok(None) => Ok(()),
        Ok(Some(response)) => {
            let reasons: Vec<&str> = response
                .diagnostics()
                .errors()
                .filter_map(|e| e.strip_prefix("nonconforming decision event: "))
                .collect();
            match reasons.as_slice() {
                [] => Ok(()),
                [reason] => {
                    assert_eq!(response.decision(), Decision::Deny);
                    Err(Rejection::Nonconforming {
                        reason: reason.to_string(),
                    })
                }
                more => panic!("several nonconformance errors: {more:?}"),
            }
        }
        Err(rejection) => Err(rejection),
    }
}

/// Assert the method and the authorizer agree on `event` under every rule;
/// return whether the method accepts it under `Strict`.
fn agree_on(set: &LoweredPolicySet, event: &Event) -> bool {
    for rule in RULES {
        assert_eq!(
            set.check_event_conformance(event, rule),
            authorizer_verdict(set, rule, event),
            "{event:?} under {rule}"
        );
    }
    set.check_event_conformance(event, MirrorRule::Strict)
        .is_ok()
}

/// [`agree_on`] for `spec`'s event as a decision event (`request`) and as a
/// history event (`response`).
fn agree(set: &LoweredPolicySet, spec: &Spec) -> [bool; 2] {
    ["request", "response"].map(|kind| {
        agree_on(
            set,
            &Spec {
                kind,
                ..spec.clone()
            }
            .event(1),
        )
    })
}

#[test]
fn a_conforming_event_is_accepted() {
    let set = lower();
    assert_eq!(agree(&set, &Spec::new("Login", "request")), [true, true]);
    let high = Spec {
        level: Some(entity("Drupe::Level", "high")),
        ..Spec::new("Login", "request")
    };
    assert_eq!(agree(&set, &high), [true, true]);
}

#[test]
fn a_missing_required_field_is_rejected() {
    let set = lower();
    for user in [None, Some(Value::Null)] {
        let spec = Spec {
            user,
            ..Spec::new("Login", "request")
        };
        assert_eq!(agree(&set, &spec), [false, false]);
    }
}

#[test]
fn a_field_of_the_wrong_type_is_rejected() {
    let set = lower();
    let spec = Spec {
        user: Some(Value::Int(7)),
        ..Spec::new("Login", "request")
    };
    assert_eq!(agree(&set, &spec), [false, false]);
}

/// `owner` is typed by text (`Drupe::OAuthUser`, and `OAuthUser` relative to
/// the namespace): a string, an entity of another declared type, and an entity
/// of an undeclared type are not values of it.
#[test]
fn a_field_typed_by_text_checks_its_entity_type() {
    let set = lower();
    for owner in [
        string("alice"),
        entity("Drupe::Gateway", "gw"),
        entity("Drupe::Ghost", "alice"),
    ] {
        let spec = Spec {
            owner: Some(owner.clone()),
            ..Spec::new("Login", "request")
        };
        assert_eq!(agree(&set, &spec), [false, false], "{owner:?}");
    }
}

/// `Drupe::Level::"medium"` is of the declared type, but not one of the
/// enumeration's ids, so not a valid entity of the action schema.
#[test]
fn an_entity_that_is_not_valid_in_the_action_schema_is_rejected() {
    let set = lower();
    let spec = Spec {
        level: Some(entity("Drupe::Level", "medium")),
        ..Spec::new("Login", "request")
    };
    assert_eq!(agree(&set, &spec), [false, false]);
}

#[test]
fn an_event_without_a_declared_signature_is_rejected() {
    let set = lower();
    // No `error` kind, and no `Logout` action.
    assert!(!agree_on(&set, &Spec::new("Login", "error").event(1)));
    assert_eq!(agree(&set, &Spec::new("Logout", "request")), [false, false]);
}

/// The pin clauses follow the rule: the unchecked rule accepts these events,
/// and `agree` compares every rule with the authorizer's.
#[test]
fn the_pin_clauses_follow_the_mirror_rule() {
    let set = lower();
    // `Event::builder` logs the caller fields of the scope it is given, so the
    // pinned `callerPrincipal` goes unlogged only on a scope-less event.
    let unlogged = Spec {
        scope: false,
        caller: None,
        ..Spec::new("Login", "request")
    };
    assert_eq!(agree(&set, &unlogged), [false, false]);
    let contradicting = Spec {
        caller: Some(entity("Drupe::OAuthUser", "bob")),
        ..Spec::new("Login", "request")
    };
    assert_eq!(agree(&set, &contradicting), [false, false]);
    let scopeless = Spec {
        scope: false,
        ..Spec::new("Login", "request")
    };
    assert_eq!(agree(&set, &scopeless), [false, false]);
    for spec in [&unlogged, &contradicting, &scopeless] {
        let event = spec.event(1);
        assert_eq!(
            set.check_event_conformance(&event, MirrorRule::Unchecked),
            Ok(())
        );
    }
    // The current rule accepts a caller logged by an event without a scope.
    assert_eq!(
        set.check_event_conformance(&scopeless.event(1), MirrorRule::Current),
        Ok(())
    );
}

/// The method's answer is the authorizer's ingestion: a rejected `Login`
/// response is not history a later `Read` can rely on, an accepted one is.
#[test]
fn an_accepted_history_event_is_history_and_a_rejected_one_is_not() {
    let set = lower();
    for (owner, ingested) in [
        (entity("Drupe::OAuthUser", "alice"), true),
        (string("alice"), false),
    ] {
        let login = Spec {
            owner: Some(owner),
            ..Spec::new("Login", "response")
        }
        .event(1);
        assert_eq!(
            set.check_event_conformance(&login, MirrorRule::Strict)
                .is_ok(),
            ingested
        );
        let mut authorizer = Authorizer::new(set.clone());
        let _ = authorizer.submit(&login);
        let read = Spec::new("Read", "request").event(2);
        let decision = authorizer
            .is_authorized(&read)
            .expect("a decision")
            .decision();
        assert_eq!(decision == Decision::Allow, ingested);
    }
}

/// The method borrows the set and changes nothing: asking twice, or before
/// building an authorizer, gives the same answers and the same decisions.
#[test]
fn the_check_has_no_side_effects() {
    let set = lower();
    let login = Spec::new("Login", "response").event(1);
    let read = Spec::new("Read", "request").event(2);
    for e in [&login, &read] {
        assert_eq!(set.check_event_conformance(e, MirrorRule::Strict), Ok(()));
        assert_eq!(set.check_event_conformance(e, MirrorRule::Strict), Ok(()));
    }
    let mut authorizer = Authorizer::new(set.clone());
    assert_eq!(
        authorizer.submit(&read).unwrap().unwrap().decision(),
        Decision::Deny
    );
    let mut authorizer = Authorizer::new(set);
    assert_eq!(authorizer.submit(&login), Ok(None));
    assert_eq!(
        authorizer.submit(&read).unwrap().unwrap().decision(),
        Decision::Allow
    );
}

#[test]
fn the_policy_set_keeps_its_traits() {
    fn traits<T: Clone + std::fmt::Debug + Send + Sync>() {}
    traits::<LoweredPolicySet>();
}

/// Every event of the test corpora (temporal, mixed, macros, providers), in
/// trace order: before the authorizer submits it, the method's answer under the
/// strict rule must be what the authorizer then does with it.
#[test]
fn the_check_agrees_with_ingestion_over_the_corpora() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut cases = support::corpus();
    let shared_event_schema =
        std::fs::read_to_string(root.join("tests/fixtures/request_response.dwschema")).unwrap();
    for (dir, shared) in [
        ("tests/passing/macros/corpus", String::new()),
        (
            "tests/passing/provider_only/corpus",
            std::fs::read_to_string(
                root.join("tests/passing/provider_only/shared_schema.cedarschema"),
            )
            .unwrap(),
        ),
    ] {
        cases.extend(
            support::case_dirs(&root.join(dir))
                .iter()
                .filter_map(|d| support::load_case(d, &shared, &shared_event_schema)),
        );
    }
    assert!(
        cases.len() > 500,
        "the corpora did not load: {}",
        cases.len()
    );

    // The cases are independent, so they run in parallel chunks.
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    let chunk = cases.len().div_ceil(threads);
    let results: Vec<Tally> = std::thread::scope(|scope| {
        let handles: Vec<_> = cases
            .chunks(chunk)
            .map(|cases| scope.spawn(move || cases.iter().map(check_case).collect::<Vec<_>>()))
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("a corpus thread panicked"))
            .collect()
    });
    let lowered = results.iter().filter(|t| t.lowered).count();
    let events: usize = results.iter().map(|t| t.events).sum();
    let rejected: usize = results.iter().map(|t| t.rejected).sum();
    let failures: Vec<String> = results.into_iter().flat_map(|t| t.failures).collect();
    eprintln!("{lowered} lowered bundles, {events} events, {rejected} rejected");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(events > 1000, "too few events: {events}");
    assert!(
        rejected > 0,
        "no event was rejected, so rejection went untested"
    );
}

/// What [`check_case`] found in one bundle.
#[derive(Default)]
struct Tally {
    lowered: bool,
    events: usize,
    rejected: usize,
    failures: Vec<String>,
}

/// Replay each trace of `case` through a fresh authorizer, comparing the
/// method's answer for each event, asked before the authorizer submits it, with
/// what the authorizer does.
fn check_case(case: &support::Case) -> Tally {
    let mut tally = Tally::default();
    let Ok(set) = case.lower() else {
        return tally;
    };
    tally.lowered = true;
    for (n, trace, _) in &case.traces {
        let Ok(trace) = parse_trace(trace) else {
            continue;
        };
        let mut authorizer = Authorizer::new(set.clone());
        for (i, event) in trace.iter().enumerate() {
            let checked = set.check_event_conformance(event, MirrorRule::Strict);
            let observed = match authorizer.submit(event) {
                Ok(None) => Ok(()),
                Ok(Some(response)) => match response
                    .diagnostics()
                    .errors()
                    .find_map(|e| e.strip_prefix("nonconforming decision event: "))
                {
                    Some(reason) => Err(Rejection::Nonconforming {
                        reason: reason.to_string(),
                    }),
                    None => Ok(()),
                },
                Err(rejection) => Err(rejection),
            };
            tally.events += 1;
            tally.rejected += usize::from(checked.is_err());
            if checked != observed {
                tally.failures.push(format!(
                    "{} trace_{n} event {i} (decision kind: {}): the method says {checked:?}, \
                     the authorizer {observed:?}",
                    case.name,
                    set.is_decision_kind(event.kind())
                ));
            }
        }
    }
    tally
}
