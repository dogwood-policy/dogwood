//! `EventSignature::spec_fields` and `spec_entities`: the specification's typing of the event
//! signatures and its entity schema, as the specification's conformance bridge computes them
//! (`dogwood-lean/bridge/src/schema.rs`): a spliced field has the type Cedar resolves for the
//! context at its path (common types, another namespace), and is required when every attribute
//! along the path is; `principalType(A)` names resolve in the action's namespace first; any other
//! field has the type the event schema names, and is optional.

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ServiceSchema, SpecCedarType as T, SpecEntityType,
    SpecFieldType as F, spec_entities,
};

const SCHEMA: &str = r#"
namespace Shared {
  type Money = { amount: decimal, currency?: String };
}
namespace Drupe {
  type Amount = decimal;
  type PayInput = { to: String, money: Shared::Money, note?: String, tags: Set<String>, lines: Set<{ sku: String, qty?: Long }>, total: Amount, mode: Mode };
  type PayOutput = { ok: Bool };
  entity Gateway;
  entity OAuthUser = { id: String };
  entity Mode enum ["fast", "o'slow"];
  action "Pay" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: PayInput, output?: PayOutput }
  };
}
"#;

const EVENTS: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource: resourceType(A),
    requestId: String,
    when: datetime,
}
event <A>::response {
    ...inputs(A),
    ...outputs(A),
    callerPrincipal: principalType(A),
}
"#;

fn lower() -> LoweredPolicySet {
    let ps = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema");
    let service = ServiceSchema::builder()
        .event_schema_str(EVENTS)
        .build()
        .expect("service");
    let policy = "permit (principal, action == Drupe::Action::\"Pay\", resource)\nwhen temporal { formerly within 1h Drupe::Action::\"Pay\"::request{} };";
    LoweredPolicySet::from_str(policy, &service, &ps).expect("lower")
}

fn field(lowered: &LoweredPolicySet, kind: &str, path: &str) -> (Result<F, String>, bool) {
    let sig = lowered
        .event_signatures()
        .find(|s| s.action() == "Pay" && s.kind() == kind)
        .expect("signature");
    let f = sig
        .spec_fields(lowered.cedar_schema())
        .into_iter()
        .find(|f| f.path.join(".") == path)
        .unwrap_or_else(|| panic!("no field {path}"));
    (f.ty, f.required)
}

#[test]
fn spliced_fields_have_the_context_s_resolved_types_and_requiredness() {
    let l = lower();
    assert_eq!(
        field(&l, "request", "input.to"),
        (Ok(F::Cedar(T::String)), true)
    );
    // Through a common type of another namespace.
    assert_eq!(
        field(&l, "request", "input.money.amount"),
        (Ok(F::Cedar(T::Extension("decimal".into()))), true)
    );
    assert_eq!(
        field(&l, "request", "input.money.currency"),
        (Ok(F::Cedar(T::String)), false)
    );
    assert_eq!(
        field(&l, "request", "input.note"),
        (Ok(F::Cedar(T::String)), false)
    );
    assert_eq!(
        field(&l, "request", "input.tags"),
        (Ok(F::Cedar(T::Set(Box::new(T::String)))), true)
    );
    assert_eq!(
        field(&l, "request", "input.lines"),
        (
            Ok(F::Cedar(T::Set(Box::new(T::Record(vec![
                ("qty".into(), T::Long, false),
                ("sku".into(), T::String, true),
            ]))))),
            true
        )
    );
    // A common-type alias of a builtin is the builtin.
    assert_eq!(
        field(&l, "request", "input.total"),
        (Ok(F::Cedar(T::Extension("decimal".into()))), true)
    );
    assert_eq!(
        field(&l, "request", "input.mode"),
        (Ok(F::Cedar(T::Entity("Drupe::Mode".into()))), true)
    );
    // Under the optional `output`, nothing is required.
    assert_eq!(
        field(&l, "response", "output.ok"),
        (Ok(F::Cedar(T::Bool)), false)
    );
}

#[test]
fn event_schema_fields_are_optional_and_typed_by_name() {
    let l = lower();
    assert_eq!(
        field(&l, "request", "callerPrincipal"),
        (Ok(F::EntityTypes(vec!["Drupe::OAuthUser".into()])), false)
    );
    assert_eq!(
        field(&l, "request", "callerResource"),
        (Ok(F::EntityTypes(vec!["Drupe::Gateway".into()])), false)
    );
    assert_eq!(
        field(&l, "request", "requestId"),
        (Ok(F::Cedar(T::String)), false)
    );
    assert_eq!(
        field(&l, "request", "when"),
        (Ok(F::Cedar(T::Extension("datetime".into()))), false)
    );
}

#[test]
fn the_entity_schema_lists_enumerations_and_actions() {
    let l = lower();
    let e = spec_entities(l.cedar_schema());
    assert!(e.entity_types.contains(&SpecEntityType {
        name: "Drupe::Mode".into(),
        enum_ids: Some(vec!["fast".into(), "o'slow".into()])
    }));
    assert!(e.entity_types.contains(&SpecEntityType {
        name: "Drupe::OAuthUser".into(),
        enum_ids: None
    }));
    assert!(
        e.actions
            .contains(&("Drupe::Action".to_string(), "Pay".to_string()))
    );
}

/// Cedar 4.14 (RFC 116) `external` declarations: an entity type without ids
/// to enumerate, and an action whose context is unknown.
const EXTERNAL_SCHEMA: &str = r#"
namespace Drupe {
  entity Gateway;
  external entity Remote;
  action "Ping" appliesTo { principal: [Remote], resource: [Gateway], context: {} };
  external action "Outside";
}
"#;

fn lower_external() -> LoweredPolicySet {
    let ps = PolicySchema::from_cedarschema_str(EXTERNAL_SCHEMA).expect("schema");
    let service = ServiceSchema::builder()
        .event_schema_str(EVENTS)
        .build()
        .expect("service");
    LoweredPolicySet::from_str("permit (principal, action, resource);", &service, &ps)
        .expect("lower")
}

#[test]
fn an_external_entity_type_lists_no_ids_and_an_external_action_is_listed() {
    let l = lower_external();
    let e = spec_entities(l.cedar_schema());
    assert!(e.entity_types.contains(&SpecEntityType {
        name: "Drupe::Remote".into(),
        enum_ids: None
    }));
    assert!(
        e.actions
            .contains(&("Drupe::Action".to_string(), "Outside".to_string()))
    );
}

#[test]
fn an_external_action_s_fields_are_typed_by_the_event_schema() {
    let l = lower_external();
    let sig = l
        .event_signatures()
        .find(|s| s.action() == "Outside" && s.kind() == "request")
        .expect("signature of the external action");
    let fields = sig.spec_fields(l.cedar_schema());
    // No context to splice, so no `input.*` field, and every field is optional.
    assert!(
        fields
            .iter()
            .all(|f| f.path.first().map(String::as_str) != Some("input"))
    );
    let request_id = fields
        .iter()
        .find(|f| f.path == ["requestId"])
        .expect("requestId field");
    assert_eq!(request_id.ty, Ok(F::Cedar(T::String)));
    assert!(fields.iter().all(|f| !f.required), "{fields:?}");
}
