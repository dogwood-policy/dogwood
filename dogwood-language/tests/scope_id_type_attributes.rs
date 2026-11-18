//! `principal.id`, `principal.type`, `resource.id` and `resource.type` are ordinary entity
//! attributes, in temporal leaves and provider arguments as in the Cedar part.
//!
//! Cedar has no built-in `id` or `type` attribute: `principal.id` reads an attribute named `id`,
//! of whatever type the schema declares, and fails validation when the entity type declares none.
//! Dogwood used to give the four paths a meaning of their own outside the Cedar part — the uid's
//! id and type name, always a `String`, whatever the entity data held — so a temporal leaf or a
//! provider argument could read a different value from the Cedar part of the same rule. These
//! tests pin the Cedar meaning in both places.

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ProviderDeclarations,
    ServiceSchema, ValidationResult, Validator, Value,
};

/// `User` declares `id` and `type` attributes; `Bare` declares none; `Opt` declares an optional
/// `id`.
const SCHEMA: &str = r#"
namespace Svc {
  entity Gateway;
  entity User = { "id": String, "type": String };
  entity Bare;
  entity Opt = { "id"?: String };
  action "Read" appliesTo {
    principal: [User],
    resource: [Gateway],
    context: { input: { doc: String } }
  };
  action "Touch" appliesTo {
    principal: [Bare],
    resource: [Gateway],
    context: { input: { doc: String } }
  };
  action "Peek" appliesTo {
    principal: [Opt],
    resource: [Gateway],
    context: { input: { doc: String } }
  };
}
"#;

fn lower(policy: &str) -> LoweredPolicySet {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("policy schema");
    LoweredPolicySet::from_str(policy, &ServiceSchema::defaults(), &schema).expect("lower")
}

fn validate(policy: &str) -> ValidationResult {
    Validator::new().validate(&lower(policy))
}

/// A temporal leaf over `action` whose past predicate is the current event itself, conjoined with
/// `cond`, so that the leaf holds exactly when `cond` does.
fn temporal(action: &str, cond: &str) -> String {
    format!(
        r#"permit (principal, action == Svc::Action::"{action}", resource)
when temporal {{ formerly within 1h (Svc::Action::"{action}"::request{{ input.doc: context.input.doc }} && {cond}) }};"#
    )
}

/// A `Read` request by `Svc::User::"alice"`, whose `id` and `type` attributes differ from the
/// uid's id and type name.
fn read_by_alice() -> Event {
    Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("hello".to_string()))
        .request_context("input", "doc", Value::String("hello".to_string()))
        .entity(
            "Svc::User::\"alice\"",
            [
                ("id", Value::String("attr-id".to_string())),
                ("type", Value::String("attr-type".to_string())),
            ],
        )
        .build()
}

fn messages(r: &ValidationResult) -> Vec<String> {
    r.validation_errors().map(|e| e.to_string()).collect()
}

#[track_caller]
fn assert_rejects(r: &ValidationResult, needle: &str) {
    let errors = messages(r);
    assert!(
        errors.iter().any(|m| m.contains(needle)),
        "expected an error containing `{needle}`, got {errors:?}"
    );
}

fn decide(policy: &str, event: &Event) -> Decision {
    let lowered = lower(policy);
    let report = Validator::new().validate(&lowered);
    assert!(report.validation_passed(), "{policy}: {report:?}");
    Authorizer::new(lowered)
        .is_authorized(event)
        .expect("decision point")
        .decision()
}

// ── Temporal leaves ──────────────────────────────────────────────────

#[test]
fn temporal_reads_the_declared_id_and_type_attributes() {
    for (cond, want) in [
        (r#"principal.id == "attr-id""#, Decision::Allow),
        (r#"principal.id == "alice""#, Decision::Deny),
        (r#"principal.type == "attr-type""#, Decision::Allow),
        (r#"principal.type == "Svc::User""#, Decision::Deny),
    ] {
        assert_eq!(decide(&temporal("Read", cond), &read_by_alice()), want, "{cond}");
    }
}

#[test]
fn temporal_and_cedar_parts_agree() {
    for cond in [
        r#"principal.id == "attr-id""#,
        r#"principal.id == "alice""#,
        r#"principal.type == "attr-type""#,
    ] {
        let cedar = format!(
            r#"permit (principal, action == Svc::Action::"Read", resource) when {{ {cond} }};"#
        );
        assert_eq!(
            decide(&temporal("Read", cond), &read_by_alice()),
            decide(&cedar, &read_by_alice()),
            "{cond}"
        );
    }
}

#[test]
fn temporal_reading_an_undeclared_id_or_type_is_a_validation_error() {
    for (cond, attr, ety) in [
        (r#"principal.id == "alice""#, "id", "Svc::Bare"),
        (r#"principal.type == "Svc::Bare""#, "type", "Svc::Bare"),
        (r#"resource.id == "gw1""#, "id", "Svc::Gateway"),
        (r#"resource.type == "Svc::Gateway""#, "type", "Svc::Gateway"),
    ] {
        assert_rejects(&validate(&temporal("Touch", cond)), &format!("`{ety}` declares no attribute `{attr}`"));
    }
    // The same `principal` reads validate where the entity type declares them.
    assert!(validate(&temporal("Read", r#"principal.id == "alice""#)).validation_passed());
    assert!(validate(&temporal("Read", r#"principal.type == "x""#)).validation_passed());
}

#[test]
fn temporal_reading_an_optional_id_needs_a_has_guard() {
    let r = validate(&temporal("Peek", r#"principal.id == "alice""#));
    assert_rejects(&r, "`principal.id` reads the optional attribute `id` of `Svc::Opt`");
    // The guard comes from the rule's Cedar part, as for any optional attribute.
    let guarded = r#"permit (principal, action == Svc::Action::"Peek", resource)
when { principal has id }
when temporal { formerly within 1h (Svc::Action::"Peek"::request{ input.doc: context.input.doc } && principal.id == "alice") };"#;
    let r = validate(guarded);
    assert!(r.validation_passed(), "{r:?}");
}

#[test]
fn temporal_id_of_a_non_string_attribute_has_its_declared_type() {
    const LONG_ID: &str = r#"
namespace Svc {
  entity Gateway;
  entity User = { "id": Long };
  action "Read" appliesTo {
    principal: [User],
    resource: [Gateway],
    context: { input: { doc: String } }
  };
}
"#;
    let schema = PolicySchema::from_cedarschema_str(LONG_ID).expect("policy schema");
    let lower = |cond: &str| {
        let l = LoweredPolicySet::from_str(&temporal("Read", cond), &ServiceSchema::defaults(), &schema)
            .expect("lower");
        Validator::new().validate(&l)
    };
    assert!(lower("principal.id == 7").validation_passed());
    assert!(!lower(r#"principal.id == "alice""#).validation_passed());
}

// ── Provider arguments ───────────────────────────────────────────────

const DECLARATIONS: &str = r#"{
  "availableProviders": {
    "Access::Allowed": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "allowed": { "paramType": "bool" } },
        "required": ["allowed"]
      }
    }
  }
}"#;

fn validate_with_provider(action: &str, arg: &str) -> ValidationResult {
    let decls = ProviderDeclarations::from_json(DECLARATIONS).expect("declarations parse");
    let service = ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("policy schema");
    let policy = format!(
        r#"permit (principal, action == Svc::Action::"{action}", resource)
when guardrails {{ Access::Allowed({arg}).allowed == true }};"#
    );
    let l = LoweredPolicySet::from_str(&policy, &service, &schema).expect("lower");
    Validator::new().validate(&l)
}

#[test]
fn provider_argument_reads_the_declared_id_attribute() {
    let r = validate_with_provider("Read", "principal.id");
    assert!(r.validation_passed(), "{r:?}");
}

#[test]
fn provider_argument_reading_an_undeclared_id_or_type_is_a_validation_error() {
    for arg in ["principal.id", "principal.type", "resource.id", "resource.type"] {
        let (root, attr) = arg.split_once('.').expect("a path");
        let r = validate_with_provider("Touch", arg);
        assert_rejects(
            &r,
            &format!(
                "argument `{arg}` is not present on the `{root}` of action \
                 `Svc::Action::\"Touch\"` (no attribute `{attr}`)"
            ),
        );
    }
    // `principal.type` validates where the entity type declares it.
    assert!(validate_with_provider("Read", "principal.type").validation_passed());
}

#[test]
fn provider_argument_receives_the_attribute_value() {
    // The resolver behind provider arguments returns the entity data's `id`, not the uid's.
    let event = read_by_alice();
    assert_eq!(
        event.scope_attr("principal", &["id".to_string()]),
        Some(Value::String("attr-id".to_string()))
    );
    assert_eq!(
        event.scope_attr("principal", &["type".to_string()]),
        Some(Value::String("attr-type".to_string()))
    );
    // Without entity data there is no attribute to read.
    let bare = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .build();
    assert_eq!(bare.scope_attr("principal", &["id".to_string()]), None);
    assert_eq!(bare.scope_attr("resource", &["type".to_string()]), None);
}

// ── Resources, nested paths and pins ─────────────────────────────────

/// `Gateway` declares an `id`; `User` declares a record-valued `id`.
const RICH_SCHEMA: &str = r#"
namespace Svc {
  entity Gateway = { "id": String };
  entity User = { "id": { "x": String } };
  action "Login" appliesTo {
    principal: [User],
    resource: [Gateway],
    context: { input: { doc: String } }
  };
  action "Read" appliesTo {
    principal: [User],
    resource: [Gateway],
    context: { input: { doc: String } }
  };
}
"#;

fn lower_rich(policy: &str, service: &ServiceSchema) -> LoweredPolicySet {
    let schema = PolicySchema::from_cedarschema_str(RICH_SCHEMA).expect("policy schema");
    LoweredPolicySet::from_str(policy, service, &schema).expect("lower")
}

/// An event of `action` by `user` on `gw1`, whose entity data give the user `id.x` = `x` and the
/// gateway `id` = `gw_id`.
fn rich_event(ts: i64, action: &str, user: &str, x: &str, gw_id: &str) -> Event {
    Event::builder(&format!("Svc::Action::{action}"), "request")
        .timestamp(ts)
        .principal(&format!("Svc::User::\"{user}\""))
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("hello".to_string()))
        .request_context("input", "doc", Value::String("hello".to_string()))
        .entity(
            &format!("Svc::User::\"{user}\""),
            [(
                "id",
                Value::Object([("x".to_string(), Value::String(x.to_string()))].into()),
            )],
        )
        .entity("Svc::Gateway::\"gw1\"", [("id", Value::String(gw_id.to_string()))])
        .build()
}

fn decide_rich(policy: &str, event: &Event) -> Decision {
    let lowered = lower_rich(policy, &ServiceSchema::defaults());
    let report = Validator::new().validate(&lowered);
    assert!(report.validation_passed(), "{policy}: {report:?}");
    Authorizer::new(lowered)
        .is_authorized(event)
        .expect("decision point")
        .decision()
}

#[test]
fn temporal_resource_id_reads_the_resource_attribute() {
    let event = rich_event(0, "Read", "alice", "v", "attr-gw");
    for (cond, want) in [
        (r#"resource.id == "attr-gw""#, Decision::Allow),
        (r#"resource.id == "gw1""#, Decision::Deny),
    ] {
        assert_eq!(decide_rich(&temporal("Read", cond), &event), want, "{cond}");
    }
}

#[test]
fn temporal_reads_a_path_under_a_record_valued_id() {
    let event = rich_event(0, "Read", "alice", "v", "gw");
    assert_eq!(
        decide_rich(&temporal("Read", r#"principal.id.x == "v""#), &event),
        Decision::Allow
    );
    let l = lower_rich(
        &temporal("Read", r#"principal.id.y == "v""#),
        &ServiceSchema::defaults(),
    );
    assert!(!Validator::new().validate(&l).validation_passed());
}

#[test]
fn a_pin_on_principal_id_correlates_by_the_supplied_attribute() {
    // With no principal pin, a pin on `principal.id.x` matches any event that logged the same
    // `key`, whoever its principal: here bob's login, whose `key` equals alice's supplied
    // `id.x`, counts for alice. The uid plays no part.
    let event_schema = r#"
decision event <A>::request {
    ...inputs(A),
    pin key: String = principal.id.x,
}
"#;
    let service = ServiceSchema::builder()
        .event_schema_str(event_schema)
        .build()
        .expect("service schema builds");
    let policy = r#"permit (principal, action == Svc::Action::"Read", resource)
when temporal { formerly within 1h Svc::Action::"Login"::request{} };"#;
    let lowered = lower_rich(policy, &service);
    let report = Validator::new().validate(&lowered);
    assert!(report.validation_passed(), "{report:?}");
    let mut authorizer = Authorizer::new(lowered);
    let with_key = |e: Event, key: &str| {
        e.into_builder()
            .logged_field("key", Value::String(key.to_string()))
            .build()
    };
    authorizer
        .is_authorized(&with_key(rich_event(0, "Login", "bob", "shared", "gw"), "shared"))
        .expect("decision point");
    let decide = |a: &mut Authorizer, x: &str, ts| {
        a.is_authorized(&with_key(rich_event(ts, "Read", "alice", x, "gw"), x))
            .expect("decision point")
            .decision()
    };
    assert_eq!(decide(&mut authorizer, "shared", 10), Decision::Allow);
    assert_eq!(decide(&mut authorizer, "other", 20), Decision::Deny);
}
