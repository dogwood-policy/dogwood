//! Exporting the augmented Cedar schema: `LoweredPolicySet::cedar_schema_str`
//! (`.cedarschema` text) and `cedar_schema_json` (the Cedar JSON schema form
//! a Cedar policy store's schema ingest accepts).
//!
//! Both derive from a single stored `SchemaFragment`. These tests pin that the
//! exports are well-formed, carry the hoisted `context.<id>` fields, and
//! survive non-trivial hoisted-field types — including the JSON export, which
//! is otherwise unexercised.

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, Validator,
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
