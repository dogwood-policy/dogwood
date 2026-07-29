//! Lifting a Cedar `Request` into a Dogwood `Event` via `Event::from_request`.
//!
//! The interop bridge (`api::request_to_event`) routes a Cedar `Request`'s
//! context into the event's **`request_context`** bag (what the Cedar request
//! is rebuilt from) and mirrors **only** the `input` group into **`logged`** (so
//! a replayed request participates in temporal correlation exactly as a native
//! `input.*` predicate would). This is the one composition path the `.log`
//! corpus never exercises — the corpus builds events through the trace parser,
//! not through `from_request`. These tests pin the routing in both directions:
//! a non-`input` context group reaches the Cedar request but NOT temporal
//! matching, while `input` reaches both.

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema,
};

// `cedar_policy` is a normal dependency, so a test can build a real `Request`.
use cedar_policy::{Context, EntityUid, Request, Schema};

/// An action whose context declares two groups: `input` (temporal-correlatable)
/// and `sys` (request-only).
const SCHEMA: &str = r#"
namespace Svc {
  type ReadInput = { user: String };
  type SysContext = { mode: String };
  entity Gateway;
  entity User = { id: String };
  action "Read" appliesTo {
    principal: [User], resource: [Gateway],
    context: { input: ReadInput, sys: SysContext }
  };
}
"#;

fn lower(policy: &str) -> LoweredPolicySet {
    LoweredPolicySet::from_str(
        policy,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(SCHEMA).expect("policy schema"),
    )
    .expect("lower")
}

/// Build a Cedar `Request` for `Svc::Read` by `alice` on `gw1`, with a
/// two-group context `{ input: { user }, sys: { mode } }`, then lift it into a
/// Dogwood `Event`.
fn lifted_event(user: &str, mode: &str) -> Event {
    let cedar_schema = Schema::from_cedarschema_str(SCHEMA)
        .map(|(s, _warnings)| s)
        .expect("cedar schema");
    let principal: EntityUid = r#"Svc::User::"alice""#.parse().expect("principal uid");
    let action: EntityUid = r#"Svc::Action::"Read""#.parse().expect("action uid");
    let resource: EntityUid = r#"Svc::Gateway::"gw1""#.parse().expect("resource uid");
    let context = Context::from_json_str(
        &format!(r#"{{ "input": {{ "user": "{user}" }}, "sys": {{ "mode": "{mode}" }} }}"#),
        Some((&cedar_schema, &action)),
    )
    .expect("context");
    let request =
        Request::new(principal, action, resource, context, Some(&cedar_schema)).expect("request");
    Event::from_request(&request).expect("lift request into event")
}

#[test]
fn cedar_request_reads_a_non_input_context_group() {
    // `sys` is a request-only group; after lifting, the Cedar request context
    // is rebuilt from `request_context`, which carries `sys`. So a pure-Cedar
    // `when { context.sys.mode == … }` resolves and the permit fires.
    let mut authorizer = Authorizer::new(lower(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { context.sys.mode == "admin" };"#,
    ));
    let resp = authorizer
        .is_authorized(&lifted_event("alice", "admin"))
        .expect("decision point");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "a Cedar request's non-input context group must reach the rebuilt Cedar context"
    );
}

// ─── entity-typed / decimal context values round-trip (Cedar JSON escapes) ──
//
// Cedar's `Context::to_json_value` encodes an entity-typed context field as
// `{"__entity":{"type","id"}}` and a decimal as `{"__extn":{"fn":"decimal",…}}`.
// `request_to_event`'s `json_to_value` must decode those to `Value::Entity` /
// `Value::Decimal`, else the rebuilt Cedar context carries a plain record and a
// policy reading the field as an entity/decimal fails closed.

const ENTITY_CTX_SCHEMA: &str = r#"
namespace Svc {
  type ReadInput = { owner: Svc::User, amount: decimal };
  entity Gateway;
  entity User;
  action "Read" appliesTo {
    principal: [User], resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

#[test]
fn entity_typed_and_decimal_context_fields_round_trip() {
    let cedar_schema = Schema::from_cedarschema_str(ENTITY_CTX_SCHEMA)
        .map(|(s, _w)| s)
        .expect("cedar schema");
    let action: EntityUid = r#"Svc::Action::"Read""#.parse().unwrap();
    // Context with an entity-typed field (`owner`) and a decimal (`amount`), in
    // Cedar's JSON escape form.
    let context = Context::from_json_str(
        r#"{ "input": {
                 "owner": { "__entity": { "type": "Svc::User", "id": "alice" } },
                 "amount": { "__extn": { "fn": "decimal", "arg": "1.5" } }
             } }"#,
        Some((&cedar_schema, &action)),
    )
    .expect("context");
    let request = Request::new(
        r#"Svc::User::"alice""#.parse().unwrap(),
        action,
        r#"Svc::Gateway::"gw1""#.parse().unwrap(),
        context,
        Some(&cedar_schema),
    )
    .expect("request");
    let event = Event::from_request(&request).expect("lift");

    // The entity-typed field compares equal to the entity literal, and the
    // decimal compares equal — both only if they decoded to Entity/Decimal (a
    // plain record would fail the type-check / comparison, fail-closed).
    let policy = r#"permit ( principal, action == Svc::Action::"Read", resource )
        when { context.input.owner == Svc::User::"alice"
            && context.input.amount == decimal("1.5") };"#;
    let mut authorizer = Authorizer::new(lower_with(ENTITY_CTX_SCHEMA, policy));
    let resp = authorizer.is_authorized(&event).expect("decision point");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "entity-typed and decimal context fields must round-trip to Value::Entity/Decimal"
    );
    assert_eq!(
        resp.diagnostics().errors().collect::<Vec<_>>().join(" | "),
        "",
        "no fail-closed evaluation error"
    );
}

const NESTED_ENTITY_CTX_SCHEMA: &str = r#"
namespace Svc {
  type Wrap = { owner: Svc::User };
  type ReadInput = { wrap: Wrap, owners: Set<Svc::User> };
  entity Gateway;
  entity User;
  action "Read" appliesTo {
    principal: [User], resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

#[test]
fn entity_refs_decode_when_nested_in_record_and_array() {
    // `json_to_value` must recurse through records AND arrays, decoding a Cedar
    // `{"__entity":{type,id}}` escape to `Value::Entity` at any depth — not only
    // at a top-level context field. A nested `owner` (record member) and an
    // `owners` set element must each compare equal to their entity literal; a
    // plain-record decode would fail the comparison (fail-closed).
    let cedar_schema = Schema::from_cedarschema_str(NESTED_ENTITY_CTX_SCHEMA)
        .map(|(s, _w)| s)
        .expect("cedar schema");
    let action: EntityUid = r#"Svc::Action::"Read""#.parse().unwrap();
    let context = Context::from_json_str(
        r#"{ "input": {
                 "wrap": { "owner": { "__entity": { "type": "Svc::User", "id": "alice" } } },
                 "owners": [ { "__entity": { "type": "Svc::User", "id": "bob" } } ]
             } }"#,
        Some((&cedar_schema, &action)),
    )
    .expect("context");
    let request = Request::new(
        r#"Svc::User::"alice""#.parse().unwrap(),
        action,
        r#"Svc::Gateway::"gw1""#.parse().unwrap(),
        context,
        Some(&cedar_schema),
    )
    .expect("request");
    let event = Event::from_request(&request).expect("lift");

    let policy = r#"permit ( principal, action == Svc::Action::"Read", resource )
        when { context.input.wrap.owner == Svc::User::"alice"
            && context.input.owners.contains(Svc::User::"bob") };"#;
    let mut authorizer = Authorizer::new(lower_with(NESTED_ENTITY_CTX_SCHEMA, policy));
    let resp = authorizer.is_authorized(&event).expect("decision point");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "entity refs nested in a record and an array must decode to Value::Entity"
    );
    assert_eq!(
        resp.diagnostics().errors().collect::<Vec<_>>().join(" | "),
        "",
        "no fail-closed evaluation error"
    );
}

fn lower_with(schema: &str, policy: &str) -> LoweredPolicySet {
    LoweredPolicySet::from_str(
        policy,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(schema).expect("policy schema"),
    )
    .expect("lower")
}

#[test]
fn cedar_request_reads_the_input_context_group() {
    // The `input` group likewise reaches the Cedar request.
    let mut authorizer = Authorizer::new(lower(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { context.input.user == "alice" };"#,
    ));
    let resp = authorizer
        .is_authorized(&lifted_event("alice", "admin"))
        .expect("decision point");
    assert_eq!(resp.decision(), Decision::Allow);
}

#[test]
fn lifted_input_group_participates_in_temporal_matching() {
    // `input` is mirrored into `logged`, so a temporal predicate field-arg can
    // correlate on it. A single lifted request whose `formerly` looks back at
    // itself on `input.user` matches (the closed window includes the current
    // timepoint), so the permit fires.
    let mut authorizer = Authorizer::new(lower(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when temporal {
               formerly within 1h Svc::Action::"Read"::request{ input.user: context.input.user }
           };"#,
    ));
    let resp = authorizer
        .is_authorized(&lifted_event("alice", "admin"))
        .expect("decision point");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "the lifted `input` group must be in `logged` for temporal correlation"
    );
}

#[test]
fn lifted_non_input_group_does_not_participate_in_temporal_matching() {
    // The reverse direction: `sys` is routed ONLY to `request_context`, never
    // mirrored into `logged`. A temporal predicate field-arg naming `sys.mode`
    // reads the matched event's `logged` record, where `sys` is absent — so the
    // predicate cannot match and the temporal leaf is false -> Deny. This is the
    // isolation that keeps request-only context out of the durable history.
    let mut authorizer = Authorizer::new(lower(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when temporal {
               formerly within 1h Svc::Action::"Read"::request{ sys.mode: "admin" }
           };"#,
    ));
    let resp = authorizer
        .is_authorized(&lifted_event("alice", "admin"))
        .expect("decision point");
    assert_eq!(
        resp.decision(),
        Decision::Deny,
        "a lifted non-input context group must NOT leak into temporal matching (logged)"
    );

    // Control: the SAME shape correlating on `input.user` (which IS mirrored to
    // logged) matches — confirming the Deny above is the `sys`-not-in-logged
    // isolation, not a spurious failure to match.
    let mut control = Authorizer::new(lower(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when temporal {
               formerly within 1h Svc::Action::"Read"::request{ input.user: context.input.user }
           };"#,
    ));
    assert_eq!(
        control
            .is_authorized(&lifted_event("alice", "admin"))
            .expect("decision point")
            .decision(),
        Decision::Allow,
        "control: correlating on the mirrored `input` group matches"
    );
}

#[test]
fn lifted_principal_with_escaped_id_matches_identity_scope() {
    // Regression: an entity id containing an escaped quote (`a"b`) must survive
    // the `Request` → `Event` lift so the lifted principal is the *same* entity
    // Cedar sees. `request_to_event` used to parse the uid without unescaping
    // (keeping a spurious backslash in `Value::Entity.id`), which then
    // double-escaped when the Cedar request was rebuilt — silently yielding a
    // DIFFERENT principal. An identity-scoped policy must still match.
    let cedar_schema = Schema::from_cedarschema_str(SCHEMA)
        .map(|(s, _warnings)| s)
        .expect("cedar schema");
    // Cedar uid literal for id `a"b`: Svc::User::"a\"b".
    let principal: EntityUid = "Svc::User::\"a\\\"b\"".parse().expect("principal uid");
    let action: EntityUid = r#"Svc::Action::"Read""#.parse().expect("action uid");
    let resource: EntityUid = r#"Svc::Gateway::"gw1""#.parse().expect("resource uid");
    let context = Context::from_json_str(
        r#"{ "input": { "user": "alice" }, "sys": { "mode": "admin" } }"#,
        Some((&cedar_schema, &action)),
    )
    .expect("context");
    let request =
        Request::new(principal, action, resource, context, Some(&cedar_schema)).expect("request");
    let event = Event::from_request(&request).expect("lift");

    // Scope-constrained to the escaped-id principal: the lifted event must
    // authorize as that entity (before the fix, the rebuilt principal was a
    // different, doubly-escaped uid and this Denied).
    let mut authorizer = Authorizer::new(lower(
        r#"permit ( principal == Svc::User::"a\"b", action == Svc::Action::"Read", resource );"#,
    ));
    let resp = authorizer.is_authorized(&event).expect("decision point");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "lifted escaped-id principal must match its own identity scope"
    );
}

// ─── action ids with a trailing `"` or `::` round-trip on the lift ──────────
//
// Cedar permits ANY string as an action `EntityId`, so an id may end in a quote
// (`a"`) or in `::` (`a::`). `request_to_event` decodes the request's action uid
// (`split_action_uid`) and `build_request` re-renders it (`qualified_action_uid`)
// at decision time; the two must be exact inverses or the lifted action silently
// stops matching its own scope. The entity path (`uid_to_value`) uses `find` +
// `strip_suffix('"')`; the action decoder must decode identically. A prior
// hand-rolled `rfind` + `trim_end_matches('"')` diverged for exactly these two
// id shapes (stripping both trailing quotes / mistaking a `::"` inside the id for
// the type separator), decoding the wrong `(namespace, id)`.

const ADVERSARIAL_ACTION_SCHEMA: &str = r#"
namespace Svc {
  entity Gateway;
  entity User;
  action "a\"" appliesTo {
    principal: [User], resource: [Gateway], context: {}
  };
  action "a::" appliesTo {
    principal: [User], resource: [Gateway], context: {}
  };
}
"#;

/// Lift a Cedar `Request` for the given action-id literal, then authorize it
/// against a policy scoped to that same action; returns the decision.
fn lifted_action_matches_scope(action_literal: &str) -> Decision {
    let cedar_schema = Schema::from_cedarschema_str(ADVERSARIAL_ACTION_SCHEMA)
        .map(|(s, _w)| s)
        .expect("cedar schema");
    let principal: EntityUid = r#"Svc::User::"alice""#.parse().expect("principal uid");
    let action: EntityUid = action_literal.parse().expect("action uid");
    let resource: EntityUid = r#"Svc::Gateway::"gw1""#.parse().expect("resource uid");
    let context = Context::from_json_str("{}", Some((&cedar_schema, &action))).expect("context");
    let request =
        Request::new(principal, action, resource, context, Some(&cedar_schema)).expect("request");
    let event = Event::from_request(&request).expect("lift");

    let policy = format!(r#"permit ( principal, action == {action_literal}, resource );"#);
    let mut authorizer = Authorizer::new(lower_with(ADVERSARIAL_ACTION_SCHEMA, &policy));
    authorizer
        .is_authorized(&event)
        .expect("decision point")
        .decision()
}

#[test]
fn lifted_action_id_ending_in_quote_matches_scope() {
    // Action id `a"` → uid literal `Svc::Action::"a\""`. `trim_end_matches('"')`
    // would strip BOTH trailing quotes (leaving a spurious `\`); `strip_suffix`
    // removes exactly one, preserving the id.
    assert_eq!(
        lifted_action_matches_scope("Svc::Action::\"a\\\"\""),
        Decision::Allow,
        "an action id ending in `\"` must survive the request lift and match its scope"
    );
}

#[test]
fn lifted_action_id_ending_in_colons_matches_scope() {
    // Action id `a::` → uid literal `Svc::Action::"a::"`. `rfind("::\"")` would
    // match the `::"` closing the literal and absorb part of the id into the
    // namespace; `find` takes the FIRST `::"` (the real separator).
    assert_eq!(
        lifted_action_matches_scope("Svc::Action::\"a::\""),
        Decision::Allow,
        "an action id ending in `::` must survive the request lift and match its scope"
    );
}
