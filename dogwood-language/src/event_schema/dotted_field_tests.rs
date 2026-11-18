//! A pin on a field whose name holds a `.`.
//!
//! The specification (`dogwood-lean`) keeps a field path as a list of
//! segments, so a pinned field such as `["ids", "user.id"]` (the Cedar
//! attribute `context.ids["user.id"]`) is two segments. The crate keeps a
//! predicate argument's path as one string, [`NamedArg::name`]. Before the
//! escape (`crate::field_path`), pin injection and the relativization rewrite
//! wrote the name with a plain `.` join and the evaluator cut it at every `.`,
//! so the injected argument named `["ids", "user", "id"]`, which no event has,
//! and no predicate of the pinned event kind matched any event, silently: a
//! `permit … formerly …` always denied (fail closed) and a
//! `forbid … formerly …` never blocked (fail open), in both evaluation modes.
//!
//! The event-schema grammar spells field names as identifiers only, so these
//! tests build the schema from the DSL and then rename the pinned field in the
//! parsed schema. Each decision runs with and without `partition_temporal()`.
//!
//! [`NamedArg::name`]: crate::extension::temporal::ast::NamedArg

use crate::event_schema::ast::{EventSchema, FieldSpec, TypeExpr};
use crate::extension::temporal::ast::{Condition, ConditionKind, Predicate};
use crate::{Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema, Value};

const ACTION_SCHEMA: &str = r#"
namespace App {
  entity User;
  entity Svc;
  type In = { x: String };
  type Ids = { "user.id": String };
  action "Login" appliesTo { principal: [User], resource: [Svc], context: { input: In, ids: Ids } };
  action "Logout" appliesTo { principal: [User], resource: [Svc], context: { input: In, ids: Ids } };
  action "Read" appliesTo { principal: [User], resource: [Svc], context: { input: In, ids: Ids } };
}
"#;

/// `ids.user_id` is pinned to the request's `context.ids.user_id`; the tests
/// rename the segment `user_id` to `user.id` on both sides, which makes the pin
/// `ids["user.id"] = context.ids["user.id"]` (symmetric, so it is also a
/// partition key).
const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    ids: { pin user_id: String = context.ids.user_id },
}
"#;

/// Rename every `user_id` field name and pin path segment to `user.id`.
fn rename_user_id(schema: &mut EventSchema) {
    fn walk(fields: &mut [FieldSpec]) {
        for f in fields {
            if let FieldSpec::Named { name, ty, pin, .. } = f {
                if name == "user_id" {
                    *name = "user.id".to_string();
                }
                if let Some(pin) = pin {
                    for segment in &mut pin.context_path {
                        if segment == "user_id" {
                            *segment = "user.id".to_string();
                        }
                    }
                }
                if let TypeExpr::Record(inner) = ty {
                    walk(inner);
                }
            }
        }
    }
    for decl in &mut schema.decls {
        walk(&mut decl.fields);
    }
}

fn service() -> ServiceSchema {
    ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("service schema builds")
        .with_edited_event_schema(rename_user_id)
}

fn lower(policy: &str) -> LoweredPolicySet {
    let schema = PolicySchema::from_cedarschema_str(ACTION_SCHEMA).expect("action schema parses");
    LoweredPolicySet::from_str(policy, &service(), &schema).expect("policy lowers")
}

fn string(s: &str) -> Value {
    Value::String(s.to_string())
}

fn ids(user: &str) -> Value {
    Value::Object(
        [("user.id".to_string(), string(user))]
            .into_iter()
            .collect(),
    )
}

/// A request event of `action` by `alice` for the user id `user`, logged and in
/// the request context.
fn event(ts: i64, action: &str, user: &str) -> Event {
    let input = Value::Object([("x".to_string(), string("x"))].into_iter().collect());
    Event::builder_for(&["App", "Action"], action, "request")
        .timestamp(ts)
        .principal("App::User::\"alice\"")
        .resource("App::Svc::\"s\"")
        .logged_field("input", input.clone())
        .logged_field("ids", ids(user))
        .logged_field(
            "callerPrincipal",
            Value::Entity {
                ty: "App::User".to_string(),
                id: "alice".to_string(),
            },
        )
        .request_context_field("input", input)
        .request_context_field("ids", ids(user))
        .build()
}

fn last_decision(policy: &str, events: &[Event], partitioned: bool) -> Decision {
    let mut builder = Authorizer::builder(lower(policy));
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

fn both_modes(policy: &str, events: &[Event]) -> [Decision; 2] {
    [
        last_decision(policy, events, false),
        last_decision(policy, events, true),
    ]
}

const PERMIT_AFTER_LOGIN: &str = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Login"::request{} };
"#;

const FORBID_AFTER_LOGOUT: &str = r#"
permit (principal, action == App::Action::"Read", resource);
forbid (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Logout"::request{} };
"#;

fn predicates<'a>(c: &'a Condition, out: &mut Vec<&'a Predicate>) {
    match &c.kind {
        ConditionKind::Predicate(p) => out.push(p),
        ConditionKind::And { left, right }
        | ConditionKind::Or { left, right }
        | ConditionKind::Since { left, right, .. } => {
            predicates(left, out);
            predicates(right, out);
        }
        ConditionKind::Not { inner }
        | ConditionKind::Formerly { body: inner, .. }
        | ConditionKind::Previous { body: inner, .. }
        | ConditionKind::Exists { body: inner, .. } => predicates(inner, out),
        _ => {}
    }
}

/// The derived pin is the two-segment path, and every predicate of the
/// lowered leaf carries it under the escaped name `ids.user\.id`, which reads
/// back as that path.
#[test]
fn the_injected_argument_names_the_dotted_field() {
    let lowered = lower(PERMIT_AFTER_LOGIN);
    let pins: Vec<Vec<String>> = lowered
        .event_signatures()
        .flat_map(|s| {
            s.pins()
                .map(|p| p.field_path().to_vec())
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(
        pins.contains(&vec!["ids".to_string(), "user.id".to_string()]),
        "{pins:?}"
    );
    let mut seen = 0;
    for field in lowered.temporal_fields() {
        let mut preds = Vec::new();
        predicates(&field.condition.condition, &mut preds);
        for p in preds {
            let arg = p
                .args
                .iter()
                .find(|a| a.name == "ids.user\\.id")
                .unwrap_or_else(|| panic!("the pin is injected: {:?}", p.args));
            assert_eq!(
                arg.field_path(),
                vec!["ids".to_string(), "user.id".to_string()]
            );
            seen += 1;
        }
    }
    assert!(seen > 0, "the leaf has predicates");
}

/// A Login for the same user id, then a Read: allowed. A Read for another user
/// id: denied (the pin correlates).
#[test]
fn permit_formerly_on_a_dotted_pin() {
    assert_eq!(
        both_modes(
            PERMIT_AFTER_LOGIN,
            &[event(1, "Login", "u1"), event(2, "Read", "u1")]
        ),
        [Decision::Allow; 2]
    );
    assert_eq!(
        both_modes(
            PERMIT_AFTER_LOGIN,
            &[event(1, "Login", "u1"), event(2, "Read", "u2")]
        ),
        [Decision::Deny; 2]
    );
}

/// A Logout for the same user id, then a Read: blocked. A Read for another
/// user id: allowed.
#[test]
fn forbid_formerly_on_a_dotted_pin() {
    assert_eq!(
        both_modes(
            FORBID_AFTER_LOGOUT,
            &[event(1, "Logout", "u1"), event(2, "Read", "u1")]
        ),
        [Decision::Deny; 2]
    );
    assert_eq!(
        both_modes(
            FORBID_AFTER_LOGOUT,
            &[event(1, "Logout", "u1"), event(2, "Read", "u2")]
        ),
        [Decision::Allow; 2]
    );
}
