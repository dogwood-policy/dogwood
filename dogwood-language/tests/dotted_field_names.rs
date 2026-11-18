//! A field name that holds a `.` (Cedar allows any string as an attribute name,
//! as in `context.input["user.id"]`) is one path segment, not two.
//!
//! The temporal evaluator reads `context.<path>` and `principal.<path>` terms
//! from a request environment that flattens the request's context record and
//! the scope entities' attributes into one string key per path. Before the
//! escape (`src/field_path.rs`), the key was the path's segments joined by a
//! plain `.`, so the quoted attribute `input["user.id"]` and the nested member
//! `input.user.id` shared the key `context.input.user.id`, and whichever was
//! seeded last (the quoted one) answered for both. A temporal term or a pin
//! that reads `context.input.user.id` then compared the request's
//! `input["user.id"]` instead: a `permit … formerly …` denied the request it
//! should allow (fail closed), allowed one it should deny (fail open), and a
//! `forbid … formerly …` let through the request it should block (fail open).
//! The specification (`dogwood-lean`) keeps paths as lists, so it reads the
//! nested member. Each test runs with and without `partition_temporal()`.

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema, Value,
};

/// An action context whose `input` has both a quoted attribute `"user.id"` and
/// a nested record `user` with a member `id`: two different paths that a plain
/// dotted join writes alike.
const ACTION_SCHEMA: &str = r#"
namespace App {
  entity User = { "team.name": String, team: { name: String } };
  entity Svc;
  type In = { "user.id": String, user: { id: String } };
  action "Login" appliesTo { principal: [User], resource: [Svc], context: { input: In } };
  action "Logout" appliesTo { principal: [User], resource: [Svc], context: { input: In } };
  action "Read" appliesTo { principal: [User], resource: [Svc], context: { input: In } };
}
"#;

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
}
"#;

/// The same events, with a second pin whose request-side path is the nested
/// `context.input.user.id`.
const PINNED_OWNER_EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    pin owner: String = context.input.user.id,
}
"#;

fn string(s: &str) -> Value {
    Value::String(s.to_string())
}

fn record(members: &[(&str, Value)]) -> Value {
    Value::Object(
        members
            .iter()
            .map(|(k, v)| (k.to_string(), v.clone()))
            .collect(),
    )
}

/// `input` with the nested `user.id` and the quoted `"user.id"`.
fn input(nested: &str, quoted: &str) -> Value {
    record(&[
        ("user", record(&[("id", string(nested))])),
        ("user.id", string(quoted)),
    ])
}

/// A request event of `action` by `alice` whose `input` (logged and in the
/// request context) has the nested `user.id` `nested` and the quoted
/// `"user.id"` `quoted`; `owner` is logged when the event schema declares it.
fn event(ts: i64, action: &str, nested: &str, quoted: &str, owner: Option<&str>) -> Event {
    let mut b = Event::builder_for(&["App", "Action"], action, "request")
        .timestamp(ts)
        .principal("App::User::\"alice\"")
        .resource("App::Svc::\"s\"")
        .logged_field("input", input(nested, quoted))
        .logged_field(
            "callerPrincipal",
            Value::Entity {
                ty: "App::User".to_string(),
                id: "alice".to_string(),
            },
        )
        .request_context_field("input", input(nested, quoted));
    if let Some(owner) = owner {
        b = b.logged_field("owner", string(owner));
    }
    b.build()
}

/// The decision at the last event of `events`, under `policy` and
/// `event_schema`, with or without partitioned temporal evaluation.
fn last_decision(
    event_schema: &str,
    policy: &str,
    events: &[Event],
    partitioned: bool,
) -> Decision {
    let service = ServiceSchema::builder()
        .event_schema_str(event_schema)
        .build()
        .expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(ACTION_SCHEMA).expect("action schema parses");
    let lowered = LoweredPolicySet::from_str(policy, &service, &schema).expect("policy lowers");
    let mut builder = Authorizer::builder(lowered);
    if partitioned {
        builder = builder.partition_temporal();
    }
    let mut authorizer = builder.build().expect("authorizer builds");
    let mut last = None;
    for e in events {
        let response = authorizer
            .submit(e)
            .expect("event is ingested")
            .expect("every event is a decision event");
        assert!(
            response.diagnostics().errors().next().is_none(),
            "no decision fails: {response:?}"
        );
        last = Some(response.decision());
    }
    last.expect("at least one event")
}

fn both_modes(event_schema: &str, policy: &str, events: &[Event]) -> [Decision; 2] {
    [
        last_decision(event_schema, policy, events, false),
        last_decision(event_schema, policy, events, true),
    ]
}

const PERMIT_AFTER_LOGIN: &str = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal {
    formerly within 1h App::Action::"Login"::request{ input.user.id: context.input.user.id }
};
"#;

const FORBID_AFTER_LOGOUT: &str = r#"
permit (principal, action == App::Action::"Read", resource);
forbid (principal, action == App::Action::"Read", resource)
when temporal {
    formerly within 1h App::Action::"Logout"::request{ input.user.id: context.input.user.id }
};
"#;

/// The nested `user.id` of the Login and of the Read agree; the quoted
/// attributes differ. `context.input.user.id` is the nested member, so the
/// Read is allowed. Before the escape the term read the Read's quoted
/// attribute, and the Read was denied.
#[test]
fn permit_formerly_allows_on_the_nested_member() {
    let events = [
        event(1, "Login", "alice", "q-login", None),
        event(2, "Read", "alice", "q-read", None),
    ];
    assert_eq!(
        both_modes(EVENT_SCHEMA, PERMIT_AFTER_LOGIN, &events),
        [Decision::Allow; 2]
    );
}

/// The nested `user.id` of the Read is `bob`, so no Login matches and the Read
/// is denied. Before the escape the term read the Read's quoted attribute,
/// `alice`, which matched the Login's nested `user.id`, and the Read was
/// allowed.
#[test]
fn permit_formerly_denies_on_the_nested_member() {
    let events = [
        event(1, "Login", "alice", "q-login", None),
        event(2, "Read", "bob", "alice", None),
    ];
    assert_eq!(
        both_modes(EVENT_SCHEMA, PERMIT_AFTER_LOGIN, &events),
        [Decision::Deny; 2]
    );
}

/// The nested `user.id` of the Logout and of the Read agree, so the forbid
/// blocks the Read. Before the escape the term read the Read's quoted
/// attribute, no Logout matched, and the Read was allowed.
#[test]
fn forbid_formerly_blocks_on_the_nested_member() {
    let events = [
        event(1, "Logout", "alice", "q-logout", None),
        event(2, "Read", "alice", "q-read", None),
    ];
    assert_eq!(
        both_modes(EVENT_SCHEMA, FORBID_AFTER_LOGOUT, &events),
        [Decision::Deny; 2]
    );
}

/// The same collision through a pin: `pin owner = context.input.user.id`
/// correlates every predicate's `owner` with the request's nested `user.id`.
/// The Login's `owner` is the Read's nested `user.id`, so the Read is allowed.
/// Before the escape the pin read the Read's quoted attribute, and every
/// predicate of the pinned events failed to match: the permit denied, and the
/// forbid never fired.
#[test]
fn a_pin_reads_the_nested_member() {
    let permit = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Login"::request{} };
"#;
    let events = [
        event(1, "Login", "alice", "q-login", Some("alice")),
        event(2, "Read", "alice", "q-read", Some("alice")),
    ];
    assert_eq!(
        both_modes(PINNED_OWNER_EVENT_SCHEMA, permit, &events),
        [Decision::Allow; 2]
    );

    let forbid = r#"
permit (principal, action == App::Action::"Read", resource);
forbid (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Logout"::request{} };
"#;
    let events = [
        event(1, "Logout", "alice", "q-logout", Some("alice")),
        event(2, "Read", "alice", "q-read", Some("alice")),
    ];
    assert_eq!(
        both_modes(PINNED_OWNER_EVENT_SCHEMA, forbid, &events),
        [Decision::Deny; 2]
    );
}

/// The scope side: `principal.team.name` is the nested attribute of the
/// principal, not its quoted `"team.name"` attribute.
#[test]
fn a_scope_attribute_reads_the_nested_member() {
    let policy = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal {
    formerly within 1h App::Action::"Login"::request{ input.user.id: principal.team.name }
};
"#;
    let with_entity = |e: Event| {
        e.into_builder()
            .entity(
                "App::User::\"alice\"",
                [
                    ("team", record(&[("name", string("red"))])),
                    ("team.name", string("blue")),
                ],
            )
            .build()
    };
    let allowed = [
        with_entity(event(1, "Login", "red", "x", None)),
        with_entity(event(2, "Read", "y", "z", None)),
    ];
    assert_eq!(
        both_modes(EVENT_SCHEMA, policy, &allowed),
        [Decision::Allow; 2]
    );
    let denied = [
        with_entity(event(1, "Login", "blue", "x", None)),
        with_entity(event(2, "Read", "y", "z", None)),
    ];
    assert_eq!(
        both_modes(EVENT_SCHEMA, policy, &denied),
        [Decision::Deny; 2]
    );
}
