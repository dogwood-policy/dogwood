//! `lower_many` over policies that use enum-typed provider values:
//!
//! - Each enum any entry uses is exported once into the merged schema, under
//!   the same name a single lowering gives it; enums no entry uses are not.
//! - Every entry's enum literals and provider fields use the exported name.
//! - Validation findings name the declared enum, not the exported one.
//! - An `Authorizer` over the merged set converts and fails closed as a single
//!   lowering does.
//! - A clash with the action schema fails only when some entry uses the enum.

use dogwood_language::{
    Authorizer, Decision, Distincter, Event, LoweredPolicySet, ParsedPolicySet, PolicySchema,
    ProviderDeclarations, ServiceSchema, Validator, Value, lower_many,
};

const SCHEMA: &str = r#"
namespace Drupe {
  entity Gateway;
  entity OAuthUser;
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: { document: String } }
  };
  action "Write" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: { document: String } }
  };
}
"#;

/// Two providers, each with its own enum. `Scan` returns a severity picked
/// from the document; `Rate` returns a confidence.
const PROVIDERS: &str = r#"
{
  "entityTypes": {
    "Vendor::Severity": { "enum": ["LOW", "HIGH"] },
    "Other::Confidence": { "enum": ["NONE", "SURE"] }
  },
  "availableProviders": {
    "Vendor::Scan": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "severity": { "paramType": "entity", "entityType": "Vendor::Severity" } },
        "required": ["severity"]
      },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(t) { if type_of(t) == \"()\" { return #{ severity: \"HIGH\" }; } if t.contains(\"bad\") { #{ severity: \"HIGH\" } } else if t.contains(\"odd\") { #{ severity: \"WEIRD\" } } else { #{ severity: \"LOW\" } } }"
      }
    },
    "Other::Rate": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "confidence": { "paramType": "entity", "entityType": "Other::Confidence" } },
        "required": ["confidence"]
      },
      "implementation": { "kind": "rhai", "script": "fn evaluate(t) { #{ confidence: \"NONE\" } }" }
    }
  }
}
"#;

const PERMIT_ALL: &str = r#"
permit ( principal, action, resource );
"#;

const FORBID_HIGH_READ: &str = r#"
forbid ( principal, action == Drupe::Action::"Read", resource )
when { Vendor::Scan(context.input.document).severity == Vendor::Severity::"HIGH" };
"#;

const FORBID_HIGH_WRITE: &str = r#"
forbid ( principal, action == Drupe::Action::"Write", resource )
when { Vendor::Scan(context.input.document).severity in [Vendor::Severity::"HIGH"] };
"#;

const FORBID_SURE: &str = r#"
forbid ( principal, action == Drupe::Action::"Read", resource )
when { Other::Rate(context.input.document).confidence == Other::Confidence::"SURE" };
"#;

const MISSPELLED: &str = r#"
forbid ( principal, action == Drupe::Action::"Write", resource )
when { Vendor::Scan(context.input.document).severity == Vendor::Severity::"HIHG" };
"#;

fn service() -> ServiceSchema {
    ServiceSchema::builder()
        .providers(ProviderDeclarations::from_json(PROVIDERS).expect("providers parse"))
        .build()
        .expect("service schema builds")
}

fn many_over(schema: &str, policies: &[(&str, &str)]) -> Result<LoweredPolicySet, String> {
    let service = service();
    let parsed: Vec<ParsedPolicySet> = policies
        .iter()
        .map(|(policy, _)| ParsedPolicySet::parse(policy, &service).expect("parses"))
        .collect();
    let entries: Vec<(&ParsedPolicySet, Distincter)> = parsed
        .iter()
        .zip(policies)
        .map(|(p, (_, d))| (p, d.parse().expect("distincter")))
        .collect();
    let schema = PolicySchema::from_cedarschema_str(schema).expect("action schema");
    lower_many(&entries, &schema).map_err(|e| e.to_string())
}

fn many(policies: &[(&str, &str)]) -> LoweredPolicySet {
    many_over(SCHEMA, policies).expect("lower_many")
}

fn schema_json(set: &LoweredPolicySet) -> serde_json::Value {
    serde_json::from_str(&set.cedar_schema_json().expect("serializes")).expect("JSON")
}

/// The names of the merged schema's `Drupe` entity types that are enums.
fn exported_enums(set: &LoweredPolicySet) -> Vec<String> {
    let json = schema_json(set);
    json["Drupe"]["entityTypes"]
        .as_object()
        .expect("entity types")
        .iter()
        .filter(|(_, ty)| ty.get("enum").is_some())
        .map(|(name, _)| name.clone())
        .collect()
}

#[test]
fn an_enum_used_by_two_entries_is_exported_once() {
    let set = many(&[(FORBID_HIGH_READ, "r"), (FORBID_HIGH_WRITE, "w")]);
    let json = schema_json(&set);
    // No namespace is added.
    assert_eq!(
        json.as_object().expect("schema").keys().collect::<Vec<_>>(),
        ["Drupe"]
    );
    assert_eq!(exported_enums(&set), ["Vendor_Severity"]);
    let severity = &json["Drupe"]["entityTypes"]["Vendor_Severity"];
    assert_eq!(severity["enum"], serde_json::json!(["LOW", "HIGH"]));
    assert_eq!(
        severity["annotations"]["dogwood_provider_enum"],
        "Vendor::Severity"
    );
    assert!(Validator::new().validate(&set).validation_passed());
}

#[test]
fn the_merged_enum_matches_a_single_lowering() {
    let merged = many(&[(FORBID_HIGH_READ, "r"), (FORBID_HIGH_WRITE, "w")]);
    let single = ParsedPolicySet::parse(FORBID_HIGH_READ, &service())
        .expect("parses")
        .lower(&PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema"))
        .expect("lowers");
    assert_eq!(
        schema_json(&merged)["Drupe"]["entityTypes"]["Vendor_Severity"],
        schema_json(&single)["Drupe"]["entityTypes"]["Vendor_Severity"]
    );
}

#[test]
fn only_enums_some_entry_uses_are_exported() {
    assert_eq!(
        exported_enums(&many(&[(PERMIT_ALL, "a"), (FORBID_HIGH_READ, "r")])),
        ["Vendor_Severity"]
    );
    assert!(exported_enums(&many(&[(PERMIT_ALL, "a"), (PERMIT_ALL, "b")])).is_empty());
    let mut both = exported_enums(&many(&[(FORBID_HIGH_READ, "r"), (FORBID_SURE, "s")]));
    both.sort();
    assert_eq!(both, ["Other_Confidence", "Vendor_Severity"]);
}

#[test]
fn every_entry_uses_the_exported_name() {
    let set = many(&[(FORBID_HIGH_READ, "r"), (FORBID_HIGH_WRITE, "w")]);
    let cedar = set.as_cedar().to_string();
    assert_eq!(
        cedar.matches(r#"Drupe::Vendor_Severity::"HIGH""#).count(),
        2,
        "{cedar}"
    );
    assert!(!cedar.contains("Vendor::Severity"), "{cedar}");
    for field in set.provider_fields() {
        assert_eq!(
            field
                .entity_type_names
                .get("Vendor::Severity")
                .map(String::as_str),
            Some("Drupe::Vendor_Severity"),
            "{}",
            field.id
        );
    }
}

#[test]
fn findings_name_the_declared_enum() {
    let set = many(&[(FORBID_HIGH_READ, "r"), (MISSPELLED, "m")]);
    let result = Validator::new().validate(&set);
    assert!(!result.validation_passed());
    let rendered = format!("{result:?}");
    assert!(
        rendered.contains(r#"Vendor::Severity::\"HIHG\""#),
        "{rendered}"
    );
    assert!(!rendered.contains("Drupe::Vendor_Severity"), "{rendered}");
}

#[test]
fn an_authorizer_over_the_merged_set_converts_and_fails_closed() {
    let set = many(&[
        (PERMIT_ALL, "a"),
        (FORBID_HIGH_READ, "r"),
        (FORBID_HIGH_WRITE, "w"),
    ]);
    let mut authorizer = Authorizer::new(set);
    let mut decide = |action: &str, document: &str| {
        let event = Event::builder(&format!("Drupe::Action::{action}"), "request")
            .principal("Drupe::OAuthUser::\"alice\"")
            .resource("Drupe::Gateway::\"gw\"")
            .request_context("input", "document", Value::String(document.to_string()))
            .build();
        let response = authorizer.is_authorized(&event).expect("decides");
        let errors: Vec<String> = response
            .diagnostics()
            .errors()
            .map(str::to_string)
            .collect();
        (response.decision(), errors)
    };
    assert_eq!(decide("Read", "fine"), (Decision::Allow, vec![]));
    assert_eq!(decide("Write", "fine"), (Decision::Allow, vec![]));
    assert_eq!(decide("Read", "bad").0, Decision::Deny);
    assert_eq!(decide("Write", "bad").0, Decision::Deny);
    let (decision, errors) = decide("Write", "odd");
    assert_eq!(decision, Decision::Deny);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("`WEIRD` is not a member of `Vendor::Severity`")),
        "{errors:?}"
    );
}

#[test]
fn a_clash_fails_only_when_an_entry_uses_the_enum() {
    let clashing = SCHEMA.replace(
        "entity Gateway;",
        "entity Gateway;\n  entity Vendor_Severity;",
    );
    let err = many_over(&clashing, &[(PERMIT_ALL, "a"), (FORBID_HIGH_WRITE, "w")])
        .expect_err("the exported name is taken");
    assert!(err.contains("Vendor_Severity"), "{err}");
    many_over(&clashing, &[(PERMIT_ALL, "a"), (FORBID_SURE, "s")])
        .expect("no entry uses Vendor::Severity");
}
