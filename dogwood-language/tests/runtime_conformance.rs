//! Runtime conformance: an `Authorizer` checks the data a decision reads, and
//! fails the decision closed on data that does not conform to the schemas.
//!
//! The checks, and their order, follow the formal specification
//! (`dogwood-lean`, `Dogwood.Spec.Decision`, `PolicySet.decideWith`): a decision
//! event without a principal or a resource; a decision event whose logged record
//! does not conform to its signature; a request that does not conform to the
//! action schema; an entity store that does not; a provider that fails; a
//! provider output that is not of its declared type; and then the temporal
//! leaves, which must all be valued. Ingestion rejects a history event that does
//! not conform (`Dogwood.Spec.Ingest`, `Rejection.nonconforming`): it never
//! enters the history, and `Authorizer::submit` reports it. A nonconforming
//! decision event does not enter the history either.

use std::collections::BTreeMap;

use dogwood_language::{
    Authorizer, Decision, Error, Event, EventSignature, InMemoryTemporalEngine, LoweredPolicySet,
    PolicySchema, ProviderDeclarations, ProviderRequest, ProviderResolver, Rejection, Response,
    ServiceSchema, TemporalBindings, TemporalEngine, TemporalField, Value, cedar::Schema,
    parse_trace,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type LoginInput = { user: String };
  type ReadInput = { user: String, note?: String };
  entity Gateway;
  entity Bot;
  entity OAuthUser = { id: String, level: Long };
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: LoginInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: ReadInput, system: { now: datetime } }
  };
}
"#;

/// A `Read` is allowed after a `Login` request of its user within the hour.
const READ_AFTER_LOGIN: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }
};
"#;

/// A `Read` is allowed after a `Login` response of its user within the hour.
const READ_AFTER_LOGIN_RESPONSE: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
};
"#;

fn lower_with(policy: &str, service: &ServiceSchema) -> LoweredPolicySet {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    LoweredPolicySet::from_str(policy, service, &schema).expect("policy lowers")
}

fn authorizer(policy: &str) -> Authorizer {
    Authorizer::new(lower_with(policy, &ServiceSchema::defaults()))
}

fn string(s: &str) -> Value {
    Value::String(s.to_string())
}

fn now() -> Value {
    Value::extension("datetime", "2024-01-01T00:00:00Z")
}

/// A conforming `Login` request by `user`: its `input` in the logged record and
/// the request context, and the caller fields the default schema declares.
fn login(ts: i64, user: &str) -> Event {
    Event::builder("Drupe::Action::Login", "request")
        .timestamp(ts)
        .principal(&format!("Drupe::OAuthUser::\"{user}\""))
        .resource("Drupe::Gateway::\"gw\"")
        .field("input", "user", string(user))
        .request_context("input", "user", string(user))
        .build()
}

/// A conforming `Read` request by `user`.
fn read(ts: i64, user: &str) -> Event {
    Event::builder("Drupe::Action::Read", "request")
        .timestamp(ts)
        .principal(&format!("Drupe::OAuthUser::\"{user}\""))
        .resource("Drupe::Gateway::\"gw\"")
        .field("input", "user", string(user))
        .request_context("input", "user", string(user))
        .request_context("system", "now", now())
        .build()
}

fn decide(authorizer: &mut Authorizer, event: &Event) -> Response {
    authorizer
        .is_authorized(event)
        .expect("a decision event decides")
}

fn errors(response: &Response) -> Vec<String> {
    response
        .diagnostics()
        .errors()
        .map(str::to_string)
        .collect()
}

/// The response denies, with one error that starts with `prefix` and mentions
/// `detail`.
#[track_caller]
fn assert_fails_closed(response: &Response, prefix: &str, detail: &str) {
    let errors = errors(response);
    assert_eq!(response.decision(), Decision::Deny, "{errors:?}");
    assert!(
        errors.len() == 1 && errors[0].starts_with(prefix) && errors[0].contains(detail),
        "expected one error `{prefix} … {detail} …`, got {errors:?}"
    );
}

// ─── The baseline ────────────────────────────────────────────────────

#[test]
fn a_conforming_trace_decides() {
    let mut a = authorizer(READ_AFTER_LOGIN);
    assert_eq!(
        decide(&mut a, &login(0, "alice")).decision(),
        Decision::Deny
    );
    let response = decide(&mut a, &read(10, "alice"));
    assert_eq!(
        response.decision(),
        Decision::Allow,
        "{:?}",
        errors(&response)
    );
    assert!(errors(&response).is_empty());
}

// ─── Decision events ─────────────────────────────────────────────────

#[test]
fn a_decision_event_that_logs_a_field_of_the_wrong_type_fails_closed_and_is_not_ingested() {
    let mut a = authorizer(READ_AFTER_LOGIN);
    let bad_login = Event::builder("Drupe::Action::Login", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw\"")
        .field("input", "user", Value::Int(7))
        .request_context("input", "user", string("alice"))
        .build();
    assert_fails_closed(
        &decide(&mut a, &bad_login),
        "nonconforming decision event:",
        "`input.user`",
    );
    // The login never entered the history, so the read has nothing to rely on.
    assert_eq!(
        decide(&mut a, &read(10, "alice")).decision(),
        Decision::Deny
    );
}

#[test]
fn a_decision_event_that_does_not_log_a_required_field_fails_closed() {
    let mut a = authorizer(READ_AFTER_LOGIN);
    let event = Event::builder("Drupe::Action::Read", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw\"")
        .request_context("input", "user", string("alice"))
        .request_context("system", "now", now())
        .build();
    assert_fails_closed(
        &decide(&mut a, &event),
        "nonconforming decision event:",
        "does not log the field `input.user`, which its signature requires",
    );
}

#[test]
fn a_decision_event_that_does_not_log_its_pinned_field_fails_closed() {
    // The default event schema pins `callerPrincipal`; a `.log` line logs only
    // what it writes.
    let mut a = authorizer(READ_AFTER_LOGIN);
    let events = parse_trace(
        r#"@0 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw") request_context(input: { user: "alice" }) Drupe::Action::"Login"::request(input: { user: "alice" }, callerResource: Drupe::Gateway::"gw")"#,
    )
    .expect("trace parses");
    assert_fails_closed(
        &decide(&mut a, &events[0]),
        "nonconforming decision event:",
        "pinned field `callerPrincipal`",
    );
}

#[test]
fn a_caller_field_that_contradicts_the_request_fails_closed() {
    let mut a = authorizer(READ_AFTER_LOGIN);
    decide(&mut a, &login(0, "alice"));
    let events = parse_trace(
        r#"@10 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw") request_context(input: { user: "alice" }, system: { now: datetime("2024-01-01T00:00:00Z") }) Drupe::Action::"Read"::request(input: { user: "alice" }, callerPrincipal: Drupe::OAuthUser::"bob", callerResource: Drupe::Gateway::"gw")"#,
    )
    .expect("trace parses");
    assert_fails_closed(
        &decide(&mut a, &events[0]),
        "nonconforming decision event:",
        "logs `callerPrincipal` as `Drupe::OAuthUser::\"bob\"`, but the request's principal is \
         `Drupe::OAuthUser::\"alice\"`",
    );
}

#[test]
fn a_decision_event_of_an_undeclared_action_fails_closed() {
    let mut a = authorizer("permit (principal, action, resource);");
    let event = Event::builder("Drupe::Action::Ghost", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw\"")
        .build();
    assert_fails_closed(
        &decide(&mut a, &event),
        "nonconforming decision event:",
        "declares no event `Drupe::Action::\"Ghost\"::request`",
    );
}

// ─── History events ──────────────────────────────────────────────────

fn login_response(user: Value) -> Event {
    Event::builder("Drupe::Action::Login", "response")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw\"")
        .field("input", "user", user)
        .build()
}

#[test]
fn a_history_event_that_does_not_conform_is_rejected_and_reported() {
    let mut a = authorizer(READ_AFTER_LOGIN_RESPONSE);
    match a.submit(&login_response(Value::Int(7))) {
        Err(Rejection::Nonconforming { reason }) => assert!(
            reason.contains("`input.user`") && reason.contains("is a Long"),
            "{reason}"
        ),
        other => panic!("expected a rejection, got {other:?}"),
    }
    // Not ingested: the read has no login response to rely on.
    assert_eq!(
        decide(&mut a, &read(10, "alice")).decision(),
        Decision::Deny
    );

    // A conforming response is ingested, and the read is allowed.
    assert!(matches!(
        a.submit(&login_response(string("alice"))),
        Ok(None)
    ));
    assert_eq!(
        decide(&mut a, &read(20, "alice")).decision(),
        Decision::Allow
    );
}

#[test]
fn is_authorized_returns_no_decision_for_a_rejected_history_event() {
    let mut a = authorizer(READ_AFTER_LOGIN_RESPONSE);
    assert!(a.is_authorized(&login_response(Value::Int(7))).is_none());
    assert_eq!(
        decide(&mut a, &read(10, "alice")).decision(),
        Decision::Deny
    );
}

#[test]
fn a_rejection_names_its_reason() {
    let rejection = Rejection::Nonconforming {
        reason: "the event schema declares no event `X`".to_string(),
    };
    assert_eq!(
        rejection.to_string(),
        "nonconforming event: the event schema declares no event `X`"
    );
}

// ─── Requests ────────────────────────────────────────────────────────

#[test]
fn a_request_without_a_required_context_attribute_fails_closed() {
    let mut a = authorizer(READ_AFTER_LOGIN);
    let event = Event::builder("Drupe::Action::Read", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw\"")
        .field("input", "user", string("alice"))
        .request_context("input", "user", string("alice"))
        .build();
    assert_fails_closed(
        &decide(&mut a, &event),
        "nonconforming request:",
        "lacks the attribute `system`",
    );
}

#[test]
fn a_request_with_an_undeclared_context_attribute_fails_closed() {
    let mut a = authorizer(READ_AFTER_LOGIN);
    let event = login(0, "alice")
        .into_builder()
        .request_context_field("extra", Value::Int(1))
        .build();
    assert_fails_closed(
        &decide(&mut a, &event),
        "nonconforming request:",
        "has the attribute `extra`",
    );
}

#[test]
fn a_context_attribute_of_the_wrong_type_fails_closed() {
    let mut a = authorizer(READ_AFTER_LOGIN);
    let event = read(0, "alice")
        .into_builder()
        .request_context("input", "note", Value::Int(3))
        .build();
    assert_fails_closed(
        &decide(&mut a, &event),
        "nonconforming request:",
        "`input.note` is a Long, but its declared type is `String`",
    );
}

#[test]
fn a_principal_of_a_type_the_action_does_not_apply_to_fails_closed() {
    // An event schema without caller fields, so the event itself conforms.
    let service = ServiceSchema::builder()
        .event_schema_str("decision event <A>::request { ...inputs(A), }")
        .build()
        .expect("event schema builds");
    let mut a = Authorizer::new(lower_with(
        "permit (principal, action, resource);",
        &service,
    ));
    let event = Event::builder("Drupe::Action::Login", "request")
        .principal("Drupe::Bot::\"r2\"")
        .resource("Drupe::Gateway::\"gw\"")
        .field("input", "user", string("r2"))
        .request_context("input", "user", string("r2"))
        .build();
    assert_fails_closed(
        &decide(&mut a, &event),
        "nonconforming request:",
        "does not apply to a principal of type `Drupe::Bot`",
    );
}

/// [`SCHEMA`]'s shape with Cedar 4.14 (RFC 116) `external` declarations: an
/// action whose context is unknown, and an entity type a defined action applies to.
const EXTERNAL_SCHEMA: &str = r#"
namespace Drupe {
  entity Gateway;
  external entity Remote;
  action "Ping" appliesTo { principal: [Remote], resource: [Gateway], context: {} };
  external action "Outside";
}
"#;

fn external_authorizer() -> Authorizer {
    let service = ServiceSchema::builder()
        .event_schema_str("decision event <A>::request { ...inputs(A), }")
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(EXTERNAL_SCHEMA).expect("action schema builds");
    Authorizer::new(
        LoweredPolicySet::from_str("permit (principal, action, resource);", &service, &schema)
            .expect("policy lowers"),
    )
}

#[test]
fn a_request_for_an_external_action_fails_closed() {
    let mut a = external_authorizer();
    let event = Event::builder("Drupe::Action::Outside", "request")
        .principal("Drupe::Remote::\"r\"")
        .resource("Drupe::Gateway::\"gw\"")
        .build();
    assert_fails_closed(
        &decide(&mut a, &event),
        "nonconforming request:",
        "declares `Drupe::Action::\"Outside\"` `external`, so no request is valid for it",
    );
}

#[test]
fn a_request_may_name_an_entity_of_an_external_type() {
    let mut a = external_authorizer();
    let event = Event::builder("Drupe::Action::Ping", "request")
        .principal("Drupe::Remote::\"r\"")
        .resource("Drupe::Gateway::\"gw\"")
        .build();
    let response = decide(&mut a, &event);
    assert_eq!(
        response.decision(),
        Decision::Allow,
        "{:?}",
        errors(&response)
    );
}

/// The entity store is Cedar's to check, and Cedar 4.14 refuses an entity whose
/// own type is `external`: the schema does not define it, so no record of it
/// conforms. A request may still name one, bare (above).
#[test]
fn an_entity_record_of_an_external_type_fails_closed() {
    let mut a = external_authorizer();
    let event = Event::builder("Drupe::Action::Ping", "request")
        .principal("Drupe::Remote::\"r\"")
        .resource("Drupe::Gateway::\"gw\"")
        .entity("Drupe::Remote::\"r\"", [])
        .build();
    assert_fails_closed(
        &decide(&mut a, &event),
        "entity conformance:",
        "does not conform to the schema",
    );
}

#[test]
fn a_datetime_in_the_context_conforms_and_reaches_cedar() {
    let policy = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when { context.system.now > datetime("2020-01-01T00:00:00Z") };
"#;
    let at = |time: &str| {
        read(0, "alice")
            .into_builder()
            .request_context("system", "now", Value::extension("datetime", time))
            .build()
    };
    let mut a = authorizer(policy);
    let response = decide(&mut a, &at("2024-01-01T00:00:00Z"));
    assert_eq!(
        response.decision(),
        Decision::Allow,
        "{:?}",
        errors(&response)
    );
    let response = decide(&mut a, &at("2010-01-01T00:00:00Z"));
    assert_eq!(response.decision(), Decision::Deny);
    assert!(errors(&response).is_empty());
    assert_fails_closed(
        &decide(&mut a, &at("yesterday")),
        "nonconforming request:",
        "`system.now` is `datetime(\"yesterday\")`, which is not a `datetime` Cedar accepts",
    );
}

#[test]
fn an_event_lifted_from_a_cedar_request_carries_its_datetime() {
    let policy = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when { context.system.now > datetime("2020-01-01T00:00:00Z") };
"#;
    let context = cedar_policy::Context::from_json_value(
        serde_json::json!({
            "input": { "user": "alice" },
            "system": { "now": { "__extn": { "fn": "datetime", "arg": "2024-01-01T00:00:00Z" } } },
        }),
        None,
    )
    .expect("context builds");
    let request = cedar_policy::Request::new(
        r#"Drupe::OAuthUser::"alice""#.parse().expect("uid"),
        r#"Drupe::Action::"Read""#.parse().expect("uid"),
        r#"Drupe::Gateway::"gw""#.parse().expect("uid"),
        context,
        None,
    )
    .expect("request builds");
    let event = Event::from_request(&request).expect("event lifts");
    let response = decide(&mut authorizer(policy), &event);
    assert_eq!(
        response.decision(),
        Decision::Allow,
        "{:?}",
        errors(&response)
    );
}

// ─── The order of the checks ─────────────────────────────────────────

#[test]
fn a_missing_principal_comes_before_a_nonconforming_event() {
    let mut a = authorizer(READ_AFTER_LOGIN);
    let event = Event::builder("Drupe::Action::Read", "request")
        .resource("Drupe::Gateway::\"gw\"")
        .field("input", "user", Value::Int(7))
        .build();
    // The missing principal is reported first; the event's nonconformance
    // second, so that the caller learns the event was not ingested.
    let response = decide(&mut a, &event);
    let errors = errors(&response);
    assert_eq!(response.decision(), Decision::Deny, "{errors:?}");
    assert!(
        errors.len() == 2
            && errors[0] == "decision event has no principal in scope"
            && errors[1].starts_with("nonconforming decision event:")
            && errors[1].contains("`input.user`"),
        "{errors:?}"
    );
}

#[test]
fn a_nonconforming_event_comes_before_a_nonconforming_request() {
    let mut a = authorizer(READ_AFTER_LOGIN);
    let event = Event::builder("Drupe::Action::Read", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw\"")
        .field("input", "user", Value::Int(7))
        .build();
    assert_fails_closed(
        &decide(&mut a, &event),
        "nonconforming decision event:",
        "`input.user`",
    );
}

// ─── Entity data ─────────────────────────────────────────────────────

#[test]
fn supplied_data_for_an_action_entity_does_not_change_the_action_hierarchy() {
    // `Read` is not a member of `Login`. Entity data claiming it is cannot make
    // `action in [Login]` hold: the schema's action entities take precedence
    // (the specification's `PolicySet.decisionEntities`).
    let policy = r#"
permit (principal, action == Drupe::Action::"Read", resource);
forbid (principal, action in [Drupe::Action::"Login"], resource);
"#;
    let mut a = authorizer(policy);
    let event = read(0, "alice")
        .into_builder()
        .entity_parents("Drupe::Action::\"Read\"", ["Drupe::Action::\"Login\""])
        .build();
    let response = decide(&mut a, &event);
    assert_eq!(
        response.decision(),
        Decision::Allow,
        "{:?}",
        errors(&response)
    );
    assert!(errors(&response).is_empty());
}

#[test]
fn principal_id_is_the_entity_data_s_id_attribute() {
    // A temporal term reads `principal.id` off the entity data, as Cedar does: here the event
    // supplies `id` = "mallory" for the principal `alice`, so `alice`'s login with
    // `input.user` = "mallory" matches and her login as "alice" does not. (The default event
    // schema pins each predicate to the requesting principal, so both logins are `alice`'s.)
    let policy = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::request{ input.user: principal.id }
};
"#;
    let read_as = |ts, id: &str| {
        read(ts, "alice")
            .into_builder()
            .entity(
                "Drupe::OAuthUser::\"alice\"",
                [("id", string(id)), ("level", Value::Int(1))],
            )
            .build()
    };
    let mut a = authorizer(policy);
    decide(&mut a, &login(0, "alice"));
    let response = decide(&mut a, &read_as(10, "mallory"));
    assert_eq!(response.decision(), Decision::Deny, "{:?}", errors(&response));
    let login_as_mallory = Event::builder("Drupe::Action::Login", "request")
        .timestamp(20)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw\"")
        .field("input", "user", string("mallory"))
        .request_context("input", "user", string("mallory"))
        .build();
    decide(&mut a, &login_as_mallory);
    let response = decide(&mut a, &read_as(30, "mallory"));
    assert_eq!(response.decision(), Decision::Allow, "{:?}", errors(&response));
}

// ─── Information providers ───────────────────────────────────────────

const PROVIDERS: &str = r#"{
  "availableProviders": {
    "Risk::Score": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "risk": { "paramType": "string" } },
        "required": ["risk"]
      }
    }
  }
}"#;

const LOW_RISK: &str = r#"
permit (principal, action == Drupe::Action::"Login", resource)
when { Risk::Score(context.input.user).risk == "low" };
"#;

/// A resolver that answers every invocation with one value.
struct Fixed(Value);

impl ProviderResolver for Fixed {
    fn resolve(&self, _: ProviderRequest<'_>) -> Option<Result<Value, String>> {
        Some(Ok(self.0.clone()))
    }
}

fn provider_authorizer(policy: &str, output: Value) -> Authorizer {
    let service = ServiceSchema::builder()
        .providers(ProviderDeclarations::from_json(PROVIDERS).expect("declarations parse"))
        .build()
        .expect("service schema builds");
    Authorizer::builder(lower_with(policy, &service))
        .provider_resolver(Fixed(output))
        .build()
        .expect("authorizer builds")
}

fn record(pairs: &[(&str, Value)]) -> Value {
    Value::Object(
        pairs
            .iter()
            .map(|(k, v)| (k.to_string(), v.clone()))
            .collect::<BTreeMap<_, _>>(),
    )
}

#[test]
fn a_provider_output_of_its_declared_type_decides() {
    let mut a = provider_authorizer(LOW_RISK, record(&[("risk", string("low"))]));
    let response = decide(&mut a, &login(0, "alice"));
    assert_eq!(
        response.decision(),
        Decision::Allow,
        "{:?}",
        errors(&response)
    );
}

#[test]
fn a_provider_output_with_an_undeclared_attribute_fails_closed() {
    let output = record(&[("risk", string("low")), ("extra", Value::Int(1))]);
    let mut a = provider_authorizer(LOW_RISK, output);
    assert_fails_closed(
        &decide(&mut a, &login(0, "alice")),
        "nonconforming provider output:",
        "has the attribute `extra`",
    );
}

#[test]
fn a_provider_output_of_another_type_fails_closed() {
    let mut a = provider_authorizer(LOW_RISK, record(&[("risk", Value::Int(3))]));
    assert_fails_closed(
        &decide(&mut a, &login(0, "alice")),
        "nonconforming provider output:",
        "`risk` is a Long, but its declared type is `String`",
    );
}

#[test]
fn an_undeclared_provider_has_no_conforming_output() {
    let policy = r#"
permit (principal, action == Drupe::Action::"Login", resource)
when { Other::Score(context.input.user).risk == "low" };
"#;
    let mut a = provider_authorizer(policy, record(&[("risk", string("low"))]));
    assert_fails_closed(
        &decide(&mut a, &login(0, "alice")),
        "nonconforming provider output:",
        "`Other::Score` has no declared output type",
    );
}

// ─── Temporal leaves ─────────────────────────────────────────────────

/// A temporal engine that edits the bindings the in-memory engine computes.
struct Editing {
    inner: InMemoryTemporalEngine,
    edit: fn(&mut TemporalBindings),
}

impl TemporalEngine for Editing {
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        schema: &Schema,
        events: &[EventSignature],
    ) -> Result<(), Error> {
        self.inner.prepare(leaves, schema, events)
    }

    fn observe(&mut self, event: &Event) {
        self.inner.observe(event);
    }

    fn evaluate(&mut self) -> Result<TemporalBindings, String> {
        let mut bindings = self.inner.evaluate()?;
        (self.edit)(&mut bindings);
        Ok(bindings)
    }
}

/// Every `Read` is permitted, unless a `Login` of its user came first.
const FORBID_AFTER_LOGIN: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource);
forbid (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }
};
"#;

fn editing_authorizer(edit: fn(&mut TemporalBindings)) -> Authorizer {
    Authorizer::builder(lower_with(FORBID_AFTER_LOGIN, &ServiceSchema::defaults()))
        .temporal_engine(Editing {
            inner: InMemoryTemporalEngine::new(),
            edit,
        })
        .build()
        .expect("authorizer builds")
}

#[test]
fn a_missing_leaf_binding_fails_closed() {
    // Without the check, Cedar would report the absent `context.<id>` as an
    // error of the forbid, skip it, and the permit would allow the read.
    let mut a = editing_authorizer(|bindings| bindings.clear());
    decide(&mut a, &login(0, "alice"));
    assert_fails_closed(
        &decide(&mut a, &read(10, "alice")),
        "temporal evaluation:",
        "returned no value for the leaf",
    );
}

#[test]
fn a_binding_for_an_unknown_leaf_fails_closed() {
    let mut a = editing_authorizer(|bindings| {
        bindings.insert("not_a_leaf".to_string(), true);
    });
    assert_fails_closed(
        &decide(&mut a, &read(10, "alice")),
        "temporal evaluation:",
        "`not_a_leaf`, which is not a leaf of the policy set",
    );
}

#[test]
fn an_unedited_engine_decides_as_the_default() {
    let mut a = editing_authorizer(|_| {});
    assert_eq!(
        decide(&mut a, &read(0, "alice")).decision(),
        Decision::Allow
    );
    decide(&mut a, &login(5, "alice"));
    assert_eq!(
        decide(&mut a, &read(10, "alice")).decision(),
        Decision::Deny
    );
}

#[test]
fn an_authored_ordering_of_timepoints_is_false() {
    // Timepoints are equality-only. Validation rejects `s < t`; an authorizer
    // built without validation still never orders two timepoints. The control,
    // `s != t`, compares them for equality only, and holds on the same trace.
    let policy = |comparison: &str| {
        format!(
            r#"
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {{
    exists (s: Timepoint). exists (t: Timepoint). (
        formerly within 1h (Drupe::Action::"Login"::request{{ input.user: context.input.user }} && tp(s))
        && formerly within 1h (Drupe::Action::"Login"::response{{ input.user: context.input.user }} && tp(t))
        && {comparison}
    )
}};
"#
        )
    };
    for (comparison, expected) in [("s < t", Decision::Deny), ("s != t", Decision::Allow)] {
        let mut a = authorizer(&policy(comparison));
        decide(&mut a, &login(0, "alice"));
        assert!(
            a.submit(&login_response(string("alice")))
                .expect("conforms")
                .is_none()
        );
        let response = decide(&mut a, &read(10, "alice"));
        assert_eq!(
            response.decision(),
            expected,
            "{comparison}: {:?}",
            errors(&response)
        );
    }
}
