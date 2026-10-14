//! Exporting the augmented Cedar schema: `LoweredPolicySet::cedar_schema_str`
//! (`.cedarschema` text) and `cedar_schema_json` (the Cedar JSON schema form
//! a Cedar policy store's schema ingest accepts).
//!
//! Both derive from a single stored `SchemaFragment`. These tests pin that the
//! exports are well-formed, carry the hoisted `context.<id>` fields, and
//! survive non-trivial hoisted-field types — including the JSON export, which
//! is otherwise unexercised.

use dogwood_language::{
    ActionRef, AuthorizationDecision, AuthorizationRequest, Authorizer, CedarPolicyEngine,
    Decision, Error, Event, LoweredPolicySet, ParsedPolicySet, PolicyEngine, PolicySchema,
    ProviderDeclarations, ProviderRequest, ProviderResolver, ServiceSchema, Validator, Value,
};
use std::collections::BTreeMap;
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicUsize, Ordering},
};

const SCHEMA: &str = r#"
namespace Drupe {
  type ReadInput = { key: String };
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

// A temporal policy: hoists one `context.<id>` bool field onto `Read`.
const TEMPORAL_POLICY: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Read"::request{ input.key: context.input.key }
};
"#;

// A provider with a **record** output type (`{ body: String }`) — a non-trivial
// hoisted field type that must survive the fragment augment/serialize path.
const PROVIDERS: &str = r#"
{
  "availableProviders": {
    "Http::Fetch": {
      "argumentTypes": [ { "paramType": "string" }, { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "body": { "paramType": "string" } },
        "required": ["body"]
      },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(base, key) { if regex_is_match(\"^[a-z0-9_-]+(\\\\.[a-z0-9_-]+)*$\", key) { #{ body: http_get(base + \"/lookup/\" + key) } } else { #{ body: \"\" } } }"
      }
    }
  }
}
"#;

const PROVIDER_POLICY: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when { Http::Fetch("http://example.com", context.input.key).body != "BLOCKED" };
"#;

const PROVIDER_WRITE_POLICY: &str = r#"
permit ( principal, action == Drupe::Action::"Write", resource )
when { Http::Fetch("http://example.com", context.input.key).body != "BLOCKED" };
"#;

const TEMPORAL_WRITE_POLICY: &str = r#"
permit ( principal, action == Drupe::Action::"Write", resource )
when temporal {
    formerly within 1h Drupe::Action::"Write"::request{ input.key: context.input.key }
};
"#;

const TEMPORAL_READ_POLICY: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Read"::request{ input.key: context.input.key }
};
"#;

const CEDAR_ONLY_POLICY: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when { context.input.key == "allowed" };
"#;

const WORKFLOW_SCHEMA: &str = r#"
namespace Drupe {
  entity Gateway;
  entity OAuthUser;
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: { key: String } }
  };
  action "Write" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: { key: String } }
  };
  action "Delete" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: { key: String } }
  };
}
"#;

const COMPLEX_PROVIDERS: &str = r#"
{
  "availableProviders": {
    "Complex::Fetch": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": {
          "nested": {
            "paramType": "record",
            "fields": {
              "count": { "paramType": "long" },
              "note": { "paramType": "string" }
            },
            "required": ["count"]
          },
          "optionalFlag": { "paramType": "bool" },
          "requiredSet": {
            "paramType": "set",
            "items": { "paramType": "decimal" }
          }
        },
        "required": ["nested", "requiredSet"]
      },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(key) { #{ nested: #{ count: 1 }, requiredSet: [] } }"
      }
    },
    "Simple::Flag": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": { "paramType": "bool" },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(key) { true }"
      }
    }
  }
}
"#;

const COMPLEX_PROVIDER_POLICY: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when {
    Complex::Fetch(context.input.key).nested.count > 0 &&
    Complex::Fetch(context.input.key).requiredSet.contains(decimal("1.5")) &&
    (Complex::Fetch(context.input.key) has optionalFlag) &&
    (Complex::Fetch(context.input.key).nested has note)
};
"#;

const SIMPLE_PROVIDER_POLICY: &str = r#"
permit (principal, action == Drupe::Action::"Write", resource)
when { Simple::Flag(context.input.key) };
"#;

fn lower_temporal() -> LoweredPolicySet {
    LoweredPolicySet::from_str(
        TEMPORAL_POLICY,
        &ServiceSchema::defaults(),
        &policy_schema(),
    )
    .expect("temporal policy lowers")
}

fn policy_schema() -> PolicySchema {
    PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema")
}

fn workflow_schema() -> PolicySchema {
    PolicySchema::from_cedarschema_str(WORKFLOW_SCHEMA).expect("workflow action schema")
}

fn provider_service() -> ServiceSchema {
    let declarations =
        ProviderDeclarations::from_json(PROVIDERS).expect("provider declarations parse");
    ServiceSchema::builder()
        .providers(declarations)
        .build()
        .expect("service schema builds")
}

fn lower_with_distincter(
    policy: &str,
    service: &ServiceSchema,
    schema: &PolicySchema,
    distincter: &str,
) -> LoweredPolicySet {
    ParsedPolicySet::parse(policy, service)
        .expect("policy parses")
        .lower_with_distincter(schema, distincter)
        .expect("policy lowers")
}

/// Model a downstream persisted-schema conversion:
/// Dogwood text -> Cedar JSON -> Cedar fragment -> cedarschema text -> Dogwood.
fn reingest_json_schema(lowered: &LoweredPolicySet) -> PolicySchema {
    let json = lowered.cedar_schema_json().expect("schema exports as JSON");
    let fragment =
        cedar_policy::SchemaFragment::from_json_str(&json).expect("JSON schema re-ingests");
    let text = fragment
        .to_cedarschema()
        .expect("JSON fragment converts back to cedarschema");
    PolicySchema::from_cedarschema_str(&text).expect("converted schema re-ingests into Dogwood")
}

fn cedar_validates_against(
    policies: &cedar_policy::PolicySet,
    schema: &cedar_policy::Schema,
) -> bool {
    cedar_policy::Validator::new(schema.clone())
        .validate(policies, cedar_policy::ValidationMode::Strict)
        .validation_passed()
}

fn provider_reference_name(attribute: &serde_json::Value) -> Option<&str> {
    if attribute["type"] == "EntityOrCommon" {
        attribute["name"].as_str()
    } else {
        attribute["type"].as_str()
    }
}

fn assert_action_has_provider_and_temporal_fields(
    lowered: &LoweredPolicySet,
    action: &str,
    provider_field: &str,
    temporal_field: &str,
) {
    let json = lowered.cedar_schema_json().expect("schema exports");
    let schema: serde_json::Value = serde_json::from_str(&json).expect("schema JSON parses");
    let namespace = &schema["Drupe"];
    let context = namespace["actions"][action]["appliesTo"]["context"]["attributes"]
        .as_object()
        .expect("action context attributes");
    assert!(
        context.contains_key(temporal_field),
        "{action} is missing temporal field `{temporal_field}`"
    );
    let providers = context
        .get("providers")
        .expect("action retains providers reference");
    assert_eq!(provider_reference_name(providers), Some("DogwoodProviders"));
    assert!(
        namespace["commonTypes"]["DogwoodProviders"]["attributes"]
            .as_object()
            .expect("DogwoodProviders attributes")
            .contains_key(provider_field),
        "shared provider type is missing `{provider_field}`"
    );
}

/// #1 — `cedar_schema_json` (previously untested) emits valid JSON that
/// re-parses as a Cedar schema. This is exactly the Cedar JSON schema contract:
/// the JSON must be ingestible as a `SchemaFragment`.
#[test]
fn cedar_schema_json_is_valid_policy_store_input() {
    let set = lower_temporal();
    let json = set
        .cedar_schema_json()
        .expect("augmented schema serializes to JSON");

    // Must be well-formed JSON.
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("cedar_schema_json is valid JSON");
    assert!(
        parsed.is_object(),
        "Cedar JSON schema is a top-level object"
    );

    // And must round-trip as a Cedar schema fragment — the shape a Cedar
    // policy store's JSON schema ingest (SchemaDefinition::CedarJson) accepts.
    cedar_policy::SchemaFragment::from_json_str(&json)
        .expect("cedar_schema_json re-parses as a Cedar SchemaFragment");
}

/// #3 — both exports carry the hoisted `context.<id>` field and the base
/// action, and the text form re-parses. (Pins the serialized content, not just
/// that serialization succeeds.)
#[test]
fn exports_carry_the_hoisted_field_and_base_action() {
    let set = lower_temporal();

    // The hoisted temporal field's id (namespaced by its rule key).
    let field_id = set
        .temporal_fields()
        .next()
        .expect("one temporal leaf hoisted")
        .id
        .clone();

    let text = set
        .cedar_schema_str()
        .expect("serializes to cedarschema text");
    assert!(
        text.contains(&field_id),
        "cedarschema text must declare the hoisted field `{field_id}`:\n{text}"
    );
    assert!(
        text.contains("Read"),
        "cedarschema text keeps the base `Read` action"
    );
    // The text form is itself valid cedarschema (round-trips).
    PolicySchema::from_cedarschema_str(&text).expect("exported cedarschema text re-parses");

    let json = set.cedar_schema_json().expect("serializes to JSON");
    assert!(
        json.contains(&field_id),
        "JSON schema must declare the hoisted field `{field_id}`:\n{json}"
    );
}

/// #4 — a provider whose output is a **record** type hoists a
/// `context.providers.<id>` field of that record type; it must survive the
/// fragment augment/serialize path and the exports must remain well-formed and
/// re-ingestible.
#[test]
fn provider_record_type_survives_the_fragment_export() {
    let decls = ProviderDeclarations::from_json(PROVIDERS).expect("providers.json parses");
    let service = ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("service schema builds");
    let set = LoweredPolicySet::from_str(PROVIDER_POLICY, &service, &policy_schema())
        .expect("provider policy lowers");

    // A provider leaf was hoisted (so this is not self-contained Cedar).
    assert!(
        !set.is_self_contained_cedar(),
        "the provider leaf should have hoisted a context field"
    );

    // The augmented schema still validates the lowered policy against the
    // hoisted (record-typed) provider field.
    assert!(
        Validator::new().validate(&set).validation_passed(),
        "provider policy validates against its augmented schema"
    );

    // Both exports remain well-formed and re-ingestible — the nested record
    // type round-trips through the fragment.
    let text = set.cedar_schema_str().expect("cedarschema text");
    assert!(
        text.contains("providers"),
        "augmented schema declares the `providers` context group:\n{text}"
    );
    PolicySchema::from_cedarschema_str(&text).expect("provider-augmented text re-parses");
    let json = set.cedar_schema_json().expect("JSON");
    cedar_policy::SchemaFragment::from_json_str(&json)
        .expect("provider-augmented JSON re-parses as a Cedar SchemaFragment");
}

#[test]
fn provider_actions_share_one_all_provider_common_type() {
    let schema = PolicySchema::from_cedarschema_str(
        r#"
        namespace Drupe {
          entity Gateway;
          entity OAuthUser;
          action "Read" appliesTo {
            principal: [OAuthUser], resource: [Gateway],
            context: { input: { key: String } }
          };
          action "Write" appliesTo {
            principal: [OAuthUser], resource: [Gateway],
            context: { input: { key: String } }
          };
          action "Delete" appliesTo {
            principal: [OAuthUser], resource: [Gateway],
            context: { input: { key: String } }
          };
        }
        "#,
    )
    .expect("action schema");
    let policies = r#"
        permit (principal, action == Drupe::Action::"Read", resource)
        when { Http::Fetch("http://example.com", context.input.key).body != "BLOCKED" };

        permit (principal, action == Drupe::Action::"Write", resource)
        when { Http::Fetch("http://example.com", context.input.key).body != "BLOCKED" };
    "#;
    let declarations =
        ProviderDeclarations::from_json(PROVIDERS).expect("provider declarations parse");
    let service = ServiceSchema::builder()
        .providers(declarations)
        .build()
        .expect("service schema builds");
    let lowered =
        LoweredPolicySet::from_str(policies, &service, &schema).expect("provider policies lower");
    assert!(Validator::new().validate(&lowered).validation_passed());

    let field_ids: Vec<String> = lowered
        .provider_fields()
        .map(|field| field.id.clone())
        .collect();
    assert_eq!(field_ids.len(), 2);

    let text = lowered.cedar_schema_str().expect("text schema export");
    for field_id in &field_ids {
        assert_eq!(
            text.matches(field_id).count(),
            1,
            "field `{field_id}` should be defined once in the shared type:\n{text}"
        );
    }

    let json = lowered.cedar_schema_json().expect("JSON schema export");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("JSON parses");
    let namespace = &parsed["Drupe"];
    let shared = &namespace["commonTypes"]["DogwoodProviders"];
    assert_eq!(
        shared["annotations"]["dogwood_provider_context"], "1.1",
        "the generated type should carry its Dogwood representation version"
    );
    let shared_attrs = shared["attributes"]
        .as_object()
        .expect("DogwoodProviders is a record");
    assert_eq!(shared_attrs.len(), 2);
    for field_id in &field_ids {
        assert!(
            shared_attrs.contains_key(field_id),
            "shared type is missing `{field_id}`: {shared:#?}"
        );
    }

    for action in ["Read", "Write"] {
        let providers =
            &namespace["actions"][action]["appliesTo"]["context"]["attributes"]["providers"];
        assert_eq!(
            providers["type"], "DogwoodProviders",
            "{action} should reference the shared provider type: {providers:#?}"
        );
    }
    assert!(
        namespace["actions"]["Delete"]["appliesTo"]["context"]["attributes"]
            .as_object()
            .expect("Delete context attributes")
            .get("providers")
            .is_none(),
        "an action untouched by provider policies should omit providers"
    );

    cedar_policy::SchemaFragment::from_json_str(&json)
        .expect("shared-provider JSON re-parses as Cedar schema");
    assert!(
        text.contains("@dogwood_provider_context(\"1.1\")"),
        "text export should retain the representation marker:\n{text}"
    );
    PolicySchema::from_cedarschema_str(&text)
        .expect("shared-provider text re-parses as Dogwood schema");
}

#[test]
fn provider_scope_shapes_target_exact_requestable_actions() {
    const SCOPED_SCHEMA: &str = r#"
        namespace App {
          entity User;
          entity Doc;
          action "Readers";
          action "Read" in [Action::"Readers"] appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { key: String } }
          };
          action "Peek" in [Action::"Readers"] appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { key: String } }
          };
          action "Write" appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { key: String } }
          };
          action "Delete" appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { key: String } }
          };
        }
        namespace Audit {
          entity User;
          entity Doc;
          action "Inspect" appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { key: String } }
          };
          action "Archive" appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { key: String } }
          };
        }
    "#;
    const SCOPED_POLICIES: &str = r#"
        permit (principal, action == App::Action::"Read", resource)
        when { Http::Fetch("http://example.com", context.input.key).body == "SAFE" };

        permit (principal, action in [App::Action::"Readers"], resource)
        when { Http::Fetch("http://example.com", context.input.key).body == "SAFE" };

        permit (
            principal,
            action in [App::Action::"Readers", App::Action::"Write"],
            resource
        )
        when { Http::Fetch("http://example.com", context.input.key).body == "SAFE" };

        permit (principal, action == Audit::Action::"Inspect", resource)
        when { Http::Fetch("http://example.com", context.input.key).body == "SAFE" };
    "#;

    let schema = PolicySchema::from_cedarschema_str(SCOPED_SCHEMA).expect("scoped schema parses");
    let lowered = LoweredPolicySet::from_str(SCOPED_POLICIES, &provider_service(), &schema)
        .expect("provider policies with varied scopes lower");
    assert!(Validator::new().validate(&lowered).validation_passed());

    let target_sets: Vec<Vec<ActionRef>> = lowered
        .provider_fields()
        .map(|field| field.target_actions.clone())
        .collect();
    let app = |id: &str| ActionRef {
        namespace: Some("App".to_string()),
        id: id.to_string(),
    };
    let audit = |id: &str| ActionRef {
        namespace: Some("Audit".to_string()),
        id: id.to_string(),
    };
    for expected in [
        vec![app("Read")],
        vec![app("Peek"), app("Read")],
        vec![app("Peek"), app("Read"), app("Write")],
        vec![audit("Inspect")],
    ] {
        assert!(
            target_sets.contains(&expected),
            "missing provider target set {expected:?}; got {target_sets:?}"
        );
    }

    let json = lowered.cedar_schema_json().expect("scoped schema exports");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("scoped JSON parses");
    for action in ["Read", "Peek", "Write"] {
        assert_eq!(
            provider_reference_name(
                &parsed["App"]["actions"][action]["appliesTo"]["context"]["attributes"]["providers"]
            ),
            Some("DogwoodProviders"),
            "App::{action} should reference the shared provider type"
        );
    }
    assert!(
        parsed["App"]["actions"]["Delete"]["appliesTo"]["context"]["attributes"]
            .as_object()
            .expect("Delete context attributes")
            .get("providers")
            .is_none(),
        "untargeted App::Delete should remain provider-free"
    );
    assert_eq!(
        provider_reference_name(
            &parsed["Audit"]["actions"]["Inspect"]["appliesTo"]["context"]["attributes"]["providers"]
        ),
        Some("DogwoodProviders")
    );
    assert!(
        parsed["Audit"]["actions"]["Archive"]["appliesTo"]["context"]["attributes"]
            .as_object()
            .expect("Archive context attributes")
            .get("providers")
            .is_none(),
        "untargeted Audit::Archive should remain provider-free"
    );
    let fragment =
        cedar_policy::SchemaFragment::from_json_str(&json).expect("scoped JSON re-parses");
    cedar_policy::Schema::from_schema_fragments([fragment])
        .expect("schema with varied provider scopes compiles");
}

#[test]
fn provider_schema_feeds_forward_after_persisted_json_round_trip() {
    let service = provider_service();
    let base = workflow_schema();

    let read = lower_with_distincter(PROVIDER_POLICY, &service, &base, "read_policy");
    let read_field = read
        .provider_fields()
        .next()
        .expect("Read policy hoists one provider field")
        .id
        .clone();
    let carried = reingest_json_schema(&read);

    let write = lower_with_distincter(PROVIDER_WRITE_POLICY, &service, &carried, "write_policy");
    let write_field = write
        .provider_fields()
        .next()
        .expect("Write policy hoists one provider field")
        .id
        .clone();
    assert!(Validator::new().validate(&write).validation_passed());
    assert!(
        cedar_validates_against(read.as_cedar(), write.cedar_schema()),
        "the earlier Read policy must validate against the final combined schema"
    );

    let json = write.cedar_schema_json().expect("final schema exports");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("final JSON parses");
    let namespace = &parsed["Drupe"];
    let common_types = namespace["commonTypes"]
        .as_object()
        .expect("Drupe common types");
    let generated: Vec<_> = common_types
        .iter()
        .filter(|(_, ty)| {
            ty["annotations"]["dogwood_provider_context"] == serde_json::Value::String("1.1".into())
        })
        .collect();
    assert_eq!(generated.len(), 1, "there must be one generated type");
    assert_eq!(generated[0].0, "DogwoodProviders");
    let attrs = generated[0].1["attributes"]
        .as_object()
        .expect("provider type attributes");
    assert!(attrs.contains_key(&read_field));
    assert!(attrs.contains_key(&write_field));
    assert!(!json.contains("DogwoodProviders_1"));
    for action in ["Read", "Write"] {
        let providers =
            &namespace["actions"][action]["appliesTo"]["context"]["attributes"]["providers"];
        assert_eq!(provider_reference_name(providers), Some("DogwoodProviders"));
    }
    assert!(
        namespace["actions"]["Delete"]["appliesTo"]["context"]["attributes"]
            .as_object()
            .expect("Delete context attributes")
            .get("providers")
            .is_none()
    );
}

#[test]
fn provider_and_temporal_augmentation_feed_forward_in_both_orders() {
    let service = provider_service();

    let provider_first = lower_with_distincter(
        PROVIDER_POLICY,
        &service,
        &workflow_schema(),
        "provider_first",
    );
    let provider_field = provider_first
        .provider_fields()
        .next()
        .expect("provider field")
        .id
        .clone();
    let carried =
        PolicySchema::from_cedarschema_str(&provider_first.cedar_schema_str().unwrap()).unwrap();
    let temporal_second =
        lower_with_distincter(TEMPORAL_WRITE_POLICY, &service, &carried, "temporal_second");
    let temporal_field = temporal_second
        .temporal_fields()
        .next()
        .expect("temporal field")
        .id
        .clone();
    let final_text = temporal_second.cedar_schema_str().unwrap();
    assert!(final_text.contains(&provider_field));
    assert!(final_text.contains(&temporal_field));
    assert!(final_text.contains("@dogwood_provider_context(\"1.1\")"));
    assert!(
        Validator::new()
            .validate(&temporal_second)
            .validation_passed()
    );
    assert!(cedar_validates_against(
        provider_first.as_cedar(),
        temporal_second.cedar_schema()
    ));

    let temporal_first = lower_with_distincter(
        TEMPORAL_WRITE_POLICY,
        &service,
        &workflow_schema(),
        "temporal_first",
    );
    let temporal_field = temporal_first
        .temporal_fields()
        .next()
        .expect("temporal field")
        .id
        .clone();
    let carried =
        PolicySchema::from_cedarschema_str(&temporal_first.cedar_schema_str().unwrap()).unwrap();
    let provider_second =
        lower_with_distincter(PROVIDER_POLICY, &service, &carried, "provider_second");
    let provider_field = provider_second
        .provider_fields()
        .next()
        .expect("provider field")
        .id
        .clone();
    let final_text = provider_second.cedar_schema_str().unwrap();
    assert!(final_text.contains(&provider_field));
    assert!(final_text.contains(&temporal_field));
    assert!(
        Validator::new()
            .validate(&provider_second)
            .validation_passed()
    );
    assert!(cedar_validates_against(
        temporal_first.as_cedar(),
        provider_second.cedar_schema()
    ));
}

#[test]
fn independently_lowered_policy_validates_against_combined_provider_schema() {
    let service = provider_service();
    let base = workflow_schema();

    let read = lower_with_distincter(PROVIDER_POLICY, &service, &base, "read");
    let carried = PolicySchema::from_cedarschema_str(&read.cedar_schema_str().unwrap()).unwrap();
    let combined =
        lower_with_distincter(PROVIDER_WRITE_POLICY, &service, &carried, "candidate_write");

    // A downstream workflow may build the combined schema above, but lower an
    // attributable candidate Cedar statement independently against the
    // original schema.
    let independent =
        lower_with_distincter(PROVIDER_WRITE_POLICY, &service, &base, "candidate_write");
    assert!(
        cedar_validates_against(independent.as_cedar(), combined.cedar_schema()),
        "independently lowered candidate Cedar must typecheck against the combined schema"
    );
}

#[test]
fn provider_and_temporal_fields_coexist_on_the_same_action_in_both_orders() {
    let service = provider_service();

    let provider_first = lower_with_distincter(
        PROVIDER_POLICY,
        &service,
        &workflow_schema(),
        "same_action_provider_first",
    );
    let provider_field = provider_first
        .provider_fields()
        .next()
        .expect("provider field")
        .id
        .clone();
    let carried =
        PolicySchema::from_cedarschema_str(&provider_first.cedar_schema_str().unwrap()).unwrap();
    let temporal_second = lower_with_distincter(
        TEMPORAL_READ_POLICY,
        &service,
        &carried,
        "same_action_temporal_second",
    );
    let temporal_field = temporal_second
        .temporal_fields()
        .next()
        .expect("temporal field")
        .id
        .clone();
    assert_action_has_provider_and_temporal_fields(
        &temporal_second,
        "Read",
        &provider_field,
        &temporal_field,
    );
    assert!(cedar_validates_against(
        provider_first.as_cedar(),
        temporal_second.cedar_schema()
    ));
    assert!(
        Validator::new()
            .validate(&temporal_second)
            .validation_passed()
    );

    let temporal_first = lower_with_distincter(
        TEMPORAL_READ_POLICY,
        &service,
        &workflow_schema(),
        "same_action_temporal_first",
    );
    let temporal_field = temporal_first
        .temporal_fields()
        .next()
        .expect("temporal field")
        .id
        .clone();
    let carried =
        PolicySchema::from_cedarschema_str(&temporal_first.cedar_schema_str().unwrap()).unwrap();
    let provider_second = lower_with_distincter(
        PROVIDER_POLICY,
        &service,
        &carried,
        "same_action_provider_second",
    );
    let provider_field = provider_second
        .provider_fields()
        .next()
        .expect("provider field")
        .id
        .clone();
    assert_action_has_provider_and_temporal_fields(
        &provider_second,
        "Read",
        &provider_field,
        &temporal_field,
    );
    assert!(cedar_validates_against(
        temporal_first.as_cedar(),
        provider_second.cedar_schema()
    ));
    assert!(
        Validator::new()
            .validate(&provider_second)
            .validation_passed()
    );
}

#[test]
fn independently_lowered_policies_validate_against_accumulated_provider_schema() {
    let service = provider_service();
    let base = workflow_schema();

    let accumulated_read =
        lower_with_distincter(PROVIDER_POLICY, &service, &base, "accumulated_read");
    let read_field = accumulated_read
        .provider_fields()
        .next()
        .expect("Read provider field")
        .id
        .clone();
    let carried =
        PolicySchema::from_cedarschema_str(&accumulated_read.cedar_schema_str().unwrap()).unwrap();
    let accumulated_write = lower_with_distincter(
        PROVIDER_WRITE_POLICY,
        &service,
        &carried,
        "accumulated_write",
    );
    let write_field = accumulated_write
        .provider_fields()
        .next()
        .expect("Write provider field")
        .id
        .clone();

    let independent_read =
        lower_with_distincter(PROVIDER_POLICY, &service, &base, "accumulated_read");
    let independent_write =
        lower_with_distincter(PROVIDER_WRITE_POLICY, &service, &base, "accumulated_write");
    for (label, independent) in [("Read", &independent_read), ("Write", &independent_write)] {
        assert!(
            cedar_validates_against(independent.as_cedar(), accumulated_write.cedar_schema()),
            "independently lowered {label} policy must validate against the accumulated schema"
        );
    }

    let final_json = accumulated_write.cedar_schema_json().unwrap();
    let final_schema: serde_json::Value =
        serde_json::from_str(&final_json).expect("combined schema JSON parses");
    let namespace = &final_schema["Drupe"];
    let provider_attrs = namespace["commonTypes"]["DogwoodProviders"]["attributes"]
        .as_object()
        .expect("DogwoodProviders attributes");
    assert!(provider_attrs.contains_key(&read_field));
    assert!(provider_attrs.contains_key(&write_field));
    for action in ["Read", "Write"] {
        let providers =
            &namespace["actions"][action]["appliesTo"]["context"]["attributes"]["providers"];
        assert_eq!(provider_reference_name(providers), Some("DogwoodProviders"));
    }

    let write_only =
        lower_with_distincter(PROVIDER_WRITE_POLICY, &service, &base, "accumulated_write");
    assert!(
        !cedar_validates_against(independent_read.as_cedar(), write_only.cedar_schema()),
        "negative control: Read must not validate if its earlier augmentation is absent"
    );
}

#[test]
fn persisted_combined_schema_validates_independent_policy_artifacts() {
    let service = provider_service();
    let base = workflow_schema();

    // Model a schema-generation workflow that rebuilds one schema from the
    // existing policy collection plus a newly submitted policy.
    let accumulated_read = lower_with_distincter(PROVIDER_POLICY, &service, &base, "existing_read");
    let read_provider_field = accumulated_read
        .provider_fields()
        .next()
        .expect("existing Read provider field")
        .id
        .clone();
    let carried = reingest_json_schema(&accumulated_read);

    let accumulated_temporal = lower_with_distincter(
        TEMPORAL_WRITE_POLICY,
        &service,
        &carried,
        "existing_temporal",
    );
    let temporal_field = accumulated_temporal
        .temporal_fields()
        .next()
        .expect("existing temporal field")
        .id
        .clone();
    let carried = reingest_json_schema(&accumulated_temporal);

    let combined_schema =
        lower_with_distincter(PROVIDER_WRITE_POLICY, &service, &carried, "submitted_write");
    let write_provider_field = combined_schema
        .provider_fields()
        .next()
        .expect("submitted Write provider field")
        .id
        .clone();

    // Model the separate artifact path: every policy is lowered on its own
    // against the original action schema, using the same stable distincter it
    // had during combined schema generation.
    let independent_read = lower_with_distincter(PROVIDER_POLICY, &service, &base, "existing_read");
    let independent_temporal =
        lower_with_distincter(TEMPORAL_WRITE_POLICY, &service, &base, "existing_temporal");
    let independent_write =
        lower_with_distincter(PROVIDER_WRITE_POLICY, &service, &base, "submitted_write");

    let independent_artifacts = [&independent_read, &independent_temporal, &independent_write];
    assert!(
        independent_artifacts
            .iter()
            .all(|lowered| lowered.rules().count() == 1),
        "each independently lowered source should contain its one authored rule"
    );
    let expected_policy_count = independent_artifacts
        .iter()
        .map(|lowered| lowered.as_cedar().policies().count())
        .sum::<usize>();
    let mut policies = cedar_policy::PolicySet::new();
    for lowered in independent_artifacts {
        for policy in lowered.as_cedar().policies() {
            policies
                .add(policy.clone())
                .expect("independent policy ids are distinct");
        }
    }
    assert_eq!(
        policies.policies().count(),
        expected_policy_count,
        "combining the independently lowered artifacts must not drop a Cedar policy"
    );

    // Persist the combined schema in the representation accepted by a Cedar
    // policy store, then validate the independently produced artifacts against
    // that persisted form rather than Dogwood's in-memory schema.
    let json = combined_schema
        .cedar_schema_json()
        .expect("combined schema exports");
    let fragment =
        cedar_policy::SchemaFragment::from_json_str(&json).expect("persisted JSON re-ingests");
    let persisted_schema =
        cedar_policy::Schema::from_schema_fragments([fragment]).expect("persisted schema compiles");
    assert!(
        cedar_validates_against(&policies, &persisted_schema),
        "all independently lowered policies must validate against the persisted combined schema"
    );

    let parsed: serde_json::Value = serde_json::from_str(&json).expect("schema JSON parses");
    let namespace = &parsed["Drupe"];
    let provider_attributes = namespace["commonTypes"]["DogwoodProviders"]["attributes"]
        .as_object()
        .expect("shared provider attributes");
    assert!(provider_attributes.contains_key(&read_provider_field));
    assert!(provider_attributes.contains_key(&write_provider_field));
    for action in ["Read", "Write"] {
        assert_eq!(
            provider_reference_name(
                &namespace["actions"][action]["appliesTo"]["context"]["attributes"]["providers"]
            ),
            Some("DogwoodProviders"),
            "{action} must reference the shared provider type"
        );
    }
    assert!(
        namespace["actions"]["Write"]["appliesTo"]["context"]["attributes"]
            .as_object()
            .expect("Write context attributes")
            .contains_key(&temporal_field),
        "the accumulated temporal field must survive provider augmentation and JSON persistence"
    );
    let (base_fragment, _) = cedar_policy::SchemaFragment::from_cedarschema_str(WORKFLOW_SCHEMA)
        .expect("base schema parses in Cedar");
    let base_json: serde_json::Value = serde_json::from_str(
        &base_fragment
            .to_json_string()
            .expect("base schema exports as JSON"),
    )
    .expect("base schema JSON parses");
    assert_eq!(
        namespace["actions"]["Delete"]["appliesTo"]["context"],
        base_json["Drupe"]["actions"]["Delete"]["appliesTo"]["context"],
        "an action untouched by the policy collection must retain its complete original context"
    );
}

#[test]
fn policies_without_providers_never_create_a_provider_type() {
    let service = ServiceSchema::defaults();
    for (label, policy) in [
        ("Cedar-only", CEDAR_ONLY_POLICY),
        ("temporal-only", TEMPORAL_WRITE_POLICY),
    ] {
        let lowered = lower_with_distincter(policy, &service, &workflow_schema(), "no_provider");
        let text = lowered.cedar_schema_str().expect("schema exports");
        assert!(
            !text.contains("DogwoodProviders") && !text.contains("@dogwood_provider_context"),
            "{label} lowering unexpectedly generated provider schema:\n{text}"
        );
        assert_eq!(
            lowered.provider_fields().count(),
            0,
            "{label} policy unexpectedly hoisted provider fields"
        );
    }
}

#[test]
fn authorization_supplies_provider_outputs_to_targeted_and_untouched_actions() {
    let service = provider_service();
    let policies = format!(
        r#"
        {PROVIDER_POLICY}

        permit (principal, action == Drupe::Action::"Delete", resource);
        "#
    );
    let lowered = LoweredPolicySet::from_str(&policies, &service, &workflow_schema())
        .expect("mixed policy set lowers");
    assert!(Validator::new().validate(&lowered).validation_passed());
    let provider_field = lowered
        .provider_fields()
        .next()
        .expect("provider field")
        .id
        .clone();

    let json = lowered.cedar_schema_json().expect("schema exports");
    let schema: serde_json::Value = serde_json::from_str(&json).expect("schema JSON parses");
    assert!(
        schema["Drupe"]["actions"]["Delete"]["appliesTo"]["context"]["attributes"]
            .as_object()
            .expect("Delete context attributes")
            .get("providers")
            .is_none(),
        "Delete must remain provider-free in the schema"
    );

    struct CountingResolver {
        calls: Arc<AtomicUsize>,
    }
    impl ProviderResolver for CountingResolver {
        fn resolve(&self, _request: ProviderRequest<'_>) -> Option<Result<Value, String>> {
            self.calls.fetch_add(1, Ordering::SeqCst);
            Some(Ok(Value::Object(BTreeMap::from([(
                "body".to_string(),
                Value::String("SAFE".to_string()),
            )]))))
        }
    }

    struct CapturingPolicyEngine {
        inner: CedarPolicyEngine,
        contexts: Arc<Mutex<Vec<serde_json::Value>>>,
    }
    impl PolicyEngine for CapturingPolicyEngine {
        fn prepare(
            &mut self,
            policies: &cedar_policy::PolicySet,
            schema: &cedar_policy::Schema,
        ) -> Result<(), Error> {
            self.inner.prepare(policies, schema)
        }

        fn is_authorized(&self, request: AuthorizationRequest<'_>) -> AuthorizationDecision {
            let context = request
                .request
                .context()
                .expect("Dogwood supplies request context")
                .to_json_value()
                .expect("request context converts to JSON");
            self.contexts
                .lock()
                .expect("context capture lock")
                .push(context);
            self.inner.is_authorized(request)
        }
    }

    let calls = Arc::new(AtomicUsize::new(0));
    let captured_contexts = Arc::new(Mutex::new(Vec::new()));
    let mut authorizer = Authorizer::builder(lowered)
        .provider_resolver(CountingResolver {
            calls: calls.clone(),
        })
        .policy_engine(CapturingPolicyEngine {
            inner: CedarPolicyEngine::new(),
            contexts: captured_contexts.clone(),
        })
        .build()
        .expect("authorizer builds");
    let read = Event::builder("Drupe::Action::Read", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "key", Value::String("document".to_string()))
        .build();
    let read_response = authorizer
        .is_authorized(&read)
        .expect("Read request is a decision point");
    let delete = Event::builder("Drupe::Action::Delete", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "key", Value::String("document".to_string()))
        .build();
    let delete_response = authorizer
        .is_authorized(&delete)
        .expect("Delete request is a decision point");

    assert_eq!(calls.load(Ordering::SeqCst), 2);
    let contexts = captured_contexts.lock().expect("context capture lock");
    assert_eq!(contexts.len(), 2);
    for (action, context) in [("Read", &contexts[0]), ("Delete", &contexts[1])] {
        assert_eq!(
            context["providers"][&provider_field]["body"],
            serde_json::Value::String("SAFE".to_string()),
            "the resolved provider output must reach the {action} Cedar request"
        );
    }
    assert_eq!(read_response.decision(), Decision::Allow);
    assert_eq!(read_response.diagnostics().errors().count(), 0);
    assert_eq!(delete_response.decision(), Decision::Allow);
    assert_eq!(delete_response.diagnostics().errors().count(), 0);
}

#[test]
fn provider_policy_targeting_only_a_pure_action_group_leaves_schema_unchanged() {
    const GROUP_ONLY_SCHEMA: &str = r#"
        namespace App {
          type ReadContext = { input: { key: String } };
          entity User;
          entity Doc;
          action "EmptyGroup";
          action "Read" appliesTo {
            principal: [User], resource: [Doc],
            context: ReadContext
          };
        }
    "#;
    const GROUP_ONLY_POLICY: &str = r#"
        permit (principal, action in [App::Action::"EmptyGroup"], resource)
        when { Http::Fetch("http://example.com", "literal").body == "SAFE" };
    "#;

    let base =
        PolicySchema::from_cedarschema_str(GROUP_ONLY_SCHEMA).expect("group-only schema parses");
    let lowered = LoweredPolicySet::from_str(GROUP_ONLY_POLICY, &provider_service(), &base)
        .expect("provider policy over a pure group lowers");

    let provider_fields: Vec<_> = lowered.provider_fields().collect();
    assert_eq!(provider_fields.len(), 1);
    assert!(
        provider_fields[0].target_actions.is_empty(),
        "a pure action group has no requestable action-map targets"
    );
    let (base_fragment, _) = cedar_policy::SchemaFragment::from_cedarschema_str(GROUP_ONLY_SCHEMA)
        .expect("base schema parses in Cedar");
    let base_json: serde_json::Value = serde_json::from_str(
        &base_fragment
            .to_json_string()
            .expect("base schema exports as JSON"),
    )
    .expect("base schema JSON parses");
    let lowered_json: serde_json::Value = serde_json::from_str(
        &lowered
            .cedar_schema_json()
            .expect("lowered schema exports as JSON"),
    )
    .expect("lowered schema JSON parses");
    assert_eq!(
        lowered_json, base_json,
        "a provider policy with no requestable targets must be a complete schema no-op"
    );
    assert_eq!(
        provider_reference_name(&lowered_json["App"]["actions"]["Read"]["appliesTo"]["context"]),
        Some("ReadContext"),
        "the unrelated action must retain its named context reference"
    );
}

#[test]
fn suffixed_provider_type_is_reused_after_json_feed_forward() {
    const COLLIDING_SCHEMA: &str = r#"
        namespace App {
          type DogwoodProviders = { customer: Bool };
          entity User;
          entity Doc;
          action "Read" appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { key: String } }
          };
          action "Write" appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { key: String } }
          };
        }
    "#;
    const READ_POLICY: &str = r#"
        permit (principal, action == App::Action::"Read", resource)
        when { Http::Fetch("http://example.com", context.input.key).body == "SAFE" };
    "#;
    const WRITE_POLICY: &str = r#"
        permit (principal, action == App::Action::"Write", resource)
        when { Http::Fetch("http://example.com", context.input.key).body == "SAFE" };
    "#;

    let service = provider_service();
    let base = PolicySchema::from_cedarschema_str(COLLIDING_SCHEMA).expect("schema parses");
    let read = lower_with_distincter(READ_POLICY, &service, &base, "suffix_read");
    let read_field = read
        .provider_fields()
        .next()
        .expect("Read provider field")
        .id
        .clone();
    let read_json: serde_json::Value =
        serde_json::from_str(&read.cedar_schema_json().expect("Read schema exports"))
            .expect("Read schema JSON parses");
    let read_type =
        read_json["App"]["commonTypes"]["DogwoodProviders_1"]["attributes"][&read_field].clone();
    let carried = reingest_json_schema(&read);
    let write = lower_with_distincter(WRITE_POLICY, &service, &carried, "suffix_write");
    let write_field = write
        .provider_fields()
        .next()
        .expect("Write provider field")
        .id
        .clone();

    let json = write.cedar_schema_json().expect("final schema exports");
    let schema: serde_json::Value = serde_json::from_str(&json).expect("schema JSON parses");
    let common_types = schema["App"]["commonTypes"]
        .as_object()
        .expect("App common types");
    assert!(common_types.contains_key("DogwoodProviders"));
    assert!(common_types.contains_key("DogwoodProviders_1"));
    assert!(
        !common_types.contains_key("DogwoodProviders_2"),
        "JSON feed-forward must retain and reuse the exact suffixed generated name"
    );
    let attributes = common_types["DogwoodProviders_1"]["attributes"]
        .as_object()
        .expect("generated provider attributes");
    assert_eq!(
        attributes.get(&read_field),
        Some(&read_type),
        "the first lowering's field and type must survive JSON feed-forward"
    );
    assert!(
        attributes.contains_key(&write_field),
        "the second lowering's field must be added to the reused type"
    );
    for action in ["Read", "Write"] {
        let providers =
            &schema["App"]["actions"][action]["appliesTo"]["context"]["attributes"]["providers"];
        assert_eq!(
            provider_reference_name(providers),
            Some("DogwoodProviders_1"),
            "{action} must reference the retained generated type name"
        );
    }
    assert!(
        cedar_validates_against(read.as_cedar(), write.cedar_schema()),
        "the original Read policy must validate against the final accumulated schema"
    );

    let fragment =
        cedar_policy::SchemaFragment::from_json_str(&json).expect("final JSON schema parses");
    cedar_policy::Schema::from_schema_fragments([fragment])
        .expect("JSON-fed suffixed provider schema compiles");
}

#[test]
fn root_namespace_provider_type_survives_end_to_end_json_feed_forward() {
    const ROOT_SCHEMA: &str = r#"
        entity User;
        entity Doc;
        action "Read" appliesTo {
          principal: [User], resource: [Doc],
          context: { input: { key: String } }
        };
        action "Write" appliesTo {
          principal: [User], resource: [Doc],
          context: { input: { key: String } }
        };
    "#;
    const ROOT_READ_POLICY: &str = r#"
        permit (principal, action == Action::"Read", resource)
        when { Http::Fetch("http://example.com", context.input.key).body == "SAFE" };
    "#;
    const ROOT_WRITE_POLICY: &str = r#"
        permit (principal, action == Action::"Write", resource)
        when { Http::Fetch("http://example.com", context.input.key).body == "SAFE" };
    "#;

    let service = provider_service();
    let base = PolicySchema::from_cedarschema_str(ROOT_SCHEMA).expect("root schema parses");
    let read = lower_with_distincter(ROOT_READ_POLICY, &service, &base, "root_read");
    let read_provider = read
        .provider_fields()
        .next()
        .expect("root Read provider field");
    assert_eq!(
        read_provider.target_actions,
        vec![ActionRef {
            namespace: None,
            id: "Read".to_string(),
        }],
        "the root Read policy must resolve to Read alone"
    );
    let read_field = read_provider.id.clone();
    let read_json: serde_json::Value =
        serde_json::from_str(&read.cedar_schema_json().expect("root Read schema exports"))
            .expect("root Read schema JSON parses");
    assert_eq!(
        provider_reference_name(
            &read_json[""]["actions"]["Read"]["appliesTo"]["context"]["attributes"]["providers"]
        ),
        Some("DogwoodProviders"),
        "Read must receive the provider type after the first lowering"
    );
    assert!(
        read_json[""]["actions"]["Write"]["appliesTo"]["context"]["attributes"]
            .as_object()
            .expect("root Write context attributes")
            .get("providers")
            .is_none(),
        "the Read-only lowering must leave root Write provider-free"
    );

    let carried = reingest_json_schema(&read);
    let write = lower_with_distincter(ROOT_WRITE_POLICY, &service, &carried, "root_write");
    let write_provider = write
        .provider_fields()
        .next()
        .expect("root Write provider field");
    assert_eq!(
        write_provider.target_actions,
        vec![ActionRef {
            namespace: None,
            id: "Write".to_string(),
        }],
        "the root Write policy must resolve to Write alone"
    );
    let write_field = write_provider.id.clone();

    let json = write.cedar_schema_json().expect("root schema exports");
    let schema: serde_json::Value = serde_json::from_str(&json).expect("root schema JSON parses");
    let attributes = schema[""]["commonTypes"]["DogwoodProviders"]["attributes"]
        .as_object()
        .expect("root shared provider attributes");
    assert!(attributes.contains_key(&read_field));
    assert!(attributes.contains_key(&write_field));
    for action in ["Read", "Write"] {
        let providers =
            &schema[""]["actions"][action]["appliesTo"]["context"]["attributes"]["providers"];
        assert_eq!(
            provider_reference_name(providers),
            Some("DogwoodProviders"),
            "{action} must reference the root namespace provider type"
        );
    }
    assert!(
        cedar_validates_against(read.as_cedar(), write.cedar_schema()),
        "the original root Read policy must validate against the accumulated schema"
    );
    let fragment =
        cedar_policy::SchemaFragment::from_json_str(&json).expect("root final JSON parses");
    cedar_policy::Schema::from_schema_fragments([fragment])
        .expect("root JSON-fed provider schema compiles");
}

#[test]
fn legacy_inline_provider_records_migrate_through_json_feed_forward() {
    const LEGACY_SCHEMA: &str = r#"
        namespace App {
          entity User;
          entity Doc;
          action "Read" appliesTo {
            principal: [User], resource: [Doc],
            context: {
              input: { key: String },
              providers: { readLegacy: String }
            }
          };
          action "Write" appliesTo {
            principal: [User], resource: [Doc],
            context: {
              input: { key: String },
              providers: { writeLegacy: Long }
            }
          };
        }
    "#;
    const READ_POLICY: &str = r#"
        permit (principal, action == App::Action::"Read", resource)
        when { Http::Fetch("http://example.com", context.input.key).body == "SAFE" };
    "#;
    const WRITE_POLICY: &str = r#"
        permit (principal, action == App::Action::"Write", resource)
        when { Http::Fetch("http://example.com", context.input.key).body == "SAFE" };
    "#;

    let service = provider_service();
    let base = PolicySchema::from_cedarschema_str(LEGACY_SCHEMA).expect("legacy schema parses");
    let read = lower_with_distincter(READ_POLICY, &service, &base, "legacy_read");
    let read_field = read
        .provider_fields()
        .next()
        .expect("Read provider field")
        .id
        .clone();
    let read_json: serde_json::Value =
        serde_json::from_str(&read.cedar_schema_json().expect("Read schema exports"))
            .expect("Read schema JSON parses");
    let read_attrs = read_json["App"]["commonTypes"]["DogwoodProviders"]["attributes"]
        .as_object()
        .expect("Read shared provider attributes");
    assert!(read_attrs.contains_key("readLegacy"));
    assert!(read_attrs.contains_key(&read_field));
    assert!(
        read_json["App"]["actions"]["Write"]["appliesTo"]["context"]["attributes"]["providers"]
            ["attributes"]
            .as_object()
            .expect("untargeted Write retains its inline provider record")
            .contains_key("writeLegacy")
    );

    let carried = reingest_json_schema(&read);
    let write = lower_with_distincter(WRITE_POLICY, &service, &carried, "legacy_write");
    let write_field = write
        .provider_fields()
        .next()
        .expect("Write provider field")
        .id
        .clone();
    assert!(Validator::new().validate(&write).validation_passed());
    assert!(
        cedar_validates_against(read.as_cedar(), write.cedar_schema()),
        "the earlier Read policy must validate after the second legacy migration"
    );

    let json = write.cedar_schema_json().expect("final schema exports");
    let schema: serde_json::Value = serde_json::from_str(&json).expect("final JSON parses");
    let common_types = schema["App"]["commonTypes"]
        .as_object()
        .expect("App common types");
    let generated: Vec<_> = common_types
        .iter()
        .filter(|(_, ty)| {
            ty["annotations"]["dogwood_provider_context"] == serde_json::Value::String("1.1".into())
        })
        .collect();
    assert_eq!(
        generated.len(),
        1,
        "migration should use one generated type"
    );
    let attributes = generated[0].1["attributes"]
        .as_object()
        .expect("migrated shared provider attributes");
    for field in ["readLegacy", "writeLegacy", &read_field, &write_field] {
        assert!(
            attributes.contains_key(field),
            "migrated shared type is missing `{field}`"
        );
    }
    for action in ["Read", "Write"] {
        assert_eq!(
            provider_reference_name(
                &schema["App"]["actions"][action]["appliesTo"]["context"]["attributes"]["providers"]
            ),
            Some("DogwoodProviders"),
            "{action} must reference the migrated shared provider type"
        );
    }
    let fragment =
        cedar_policy::SchemaFragment::from_json_str(&json).expect("migrated JSON re-parses");
    cedar_policy::Schema::from_schema_fragments([fragment])
        .expect("migrated JSON-fed schema compiles");
}

#[test]
fn complex_provider_output_type_survives_incremental_json_conversion() {
    let declarations =
        ProviderDeclarations::from_json(COMPLEX_PROVIDERS).expect("complex providers parse");
    let service = ServiceSchema::builder()
        .providers(declarations)
        .build()
        .expect("service schema builds");
    let base = workflow_schema();

    let complex =
        lower_with_distincter(COMPLEX_PROVIDER_POLICY, &service, &base, "complex_provider");
    assert!(Validator::new().validate(&complex).validation_passed());
    let complex_fields: Vec<String> = complex
        .provider_fields()
        .map(|field| field.id.clone())
        .collect();
    assert!(
        !complex_fields.is_empty(),
        "the complex policy must emit provider fields"
    );
    let complex_json = complex.cedar_schema_json().expect("complex schema exports");
    let complex_schema: serde_json::Value =
        serde_json::from_str(&complex_json).expect("complex schema JSON parses");
    let original_attrs = complex_schema["Drupe"]["commonTypes"]["DogwoodProviders"]["attributes"]
        .as_object()
        .expect("original shared provider attributes");
    let original_types: BTreeMap<String, serde_json::Value> = complex_fields
        .iter()
        .map(|field| {
            (
                field.clone(),
                original_attrs
                    .get(field)
                    .unwrap_or_else(|| panic!("original complex field `{field}` exists"))
                    .clone(),
            )
        })
        .collect();

    let carried = reingest_json_schema(&complex);
    let simple = lower_with_distincter(
        SIMPLE_PROVIDER_POLICY,
        &service,
        &carried,
        "simple_provider",
    );
    assert!(Validator::new().validate(&simple).validation_passed());
    assert!(
        cedar_validates_against(complex.as_cedar(), simple.cedar_schema()),
        "the complex policy must retain its exact provider types after conversion"
    );

    let json = simple.cedar_schema_json().expect("final schema exports");
    let schema: serde_json::Value = serde_json::from_str(&json).expect("final schema JSON parses");
    let attrs = schema["Drupe"]["commonTypes"]["DogwoodProviders"]["attributes"]
        .as_object()
        .expect("shared provider attributes");
    for field in &complex_fields {
        assert_eq!(
            attrs.get(field),
            original_types.get(field),
            "complex provider field `{field}` changed type during JSON feed-forward"
        );
    }
    let simple_field = simple
        .provider_fields()
        .next()
        .expect("simple provider field")
        .id
        .as_str();
    assert!(attrs.contains_key(simple_field));

    let text = simple.cedar_schema_str().expect("final schema text");
    assert!(text.contains("optionalFlag?"));
    assert!(text.contains("note?"));
    assert!(text.contains("Set<"));
    assert!(text.contains("decimal"));
    PolicySchema::from_cedarschema_str(&text).expect("complex final schema re-ingests");
    cedar_policy::SchemaFragment::from_json_str(&json)
        .expect("complex final JSON re-ingests as Cedar schema");
}

/// Provider-declared enum entity types (`entityTypes` in `providers.json`) are
/// injected into the augmented schema, in the action schema's namespace, so
/// both exports carry them — with ids that need escaping and with their
/// annotations — and a plain Cedar consumer can validate the lowered policy
/// against the exported text alone.
#[test]
fn provider_entity_types_are_injected_into_the_exports() {
    const ENUM_PROVIDERS: &str = r#"{
      "entityTypes": {
        "Guard::Score": { "enum": ["LOW", "a\"b"], "annotations": { "doc": "severity bucket" } }
      },
      "availableProviders": {
        "Guard::Filter": {
          "argumentTypes": [ { "paramType": "string" } ],
          "outputType": { "paramType": "record",
            "fields": { "result": { "paramType": "entity", "entityType": "Guard::Score" } },
            "required": ["result"] },
          "implementation": { "kind": "rhai", "script": "fn evaluate(t) { #{ result: \"LOW\" } }" }
        }
      }
    }"#;
    const ENUM_POLICY: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when { Guard::Filter(context.input.key).result == Guard::Score::"a\"b" };
"#;
    let decls = ProviderDeclarations::from_json(ENUM_PROVIDERS).expect("providers.json parses");
    let service = ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("service schema");
    let set = LoweredPolicySet::from_str(ENUM_POLICY, &service, &policy_schema())
        .expect("enum policy lowers");
    assert!(Validator::new().validate(&set).validation_passed());

    let json: serde_json::Value =
        serde_json::from_str(&set.cedar_schema_json().expect("JSON export")).unwrap();
    // Exported into the action schema's namespace, tagged with its declared
    // name; no `Guard` namespace is added.
    assert!(json.get("Guard").is_none(), "{json:#}");
    let score = &json["Drupe"]["entityTypes"]["Guard_Score"];
    assert_eq!(
        score["enum"],
        serde_json::json!(["LOW", "a\"b"]),
        "{json:#}"
    );
    assert_eq!(score["annotations"]["doc"], "severity bucket", "{json:#}");
    assert_eq!(
        score["annotations"]["dogwood_provider_enum"], "Guard::Score",
        "{json:#}"
    );

    // The text export re-parses, and plain Cedar validates the lowered policy
    // against it: the enum and the enum-typed hoisted field travel together.
    let text = set.cedar_schema_str().expect("text export");
    let schema = cedar_policy::Schema::from_cedarschema_str(&text)
        .expect("exported cedarschema re-parses")
        .0;
    let result = cedar_policy::Validator::new(schema)
        .validate(set.as_cedar(), cedar_policy::ValidationMode::Strict);
    assert!(
        result.validation_passed(),
        "{:?}",
        result
            .validation_errors()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );
}
