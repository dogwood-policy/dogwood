//! `lower_many` / `from_many_str` over policies that call information
//! providers, alone and beside temporal leaves:
//!
//! - A provider field's id is `<d>_<rule>_p_<ordinal>`, where the ordinal
//!   counter is shared with the rule's temporal leaves in source order.
//! - Provider ids depend only on their own entry and distincter.
//! - Every entry's provider fields land in one shared `DogwoodProviders`
//!   common type, referenced by exactly the actions some field targets.
//! - Provider findings render against their own entry's text, and an
//!   `Authorizer` decides over providers drawn from several entries.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};

use dogwood_language::{
    ActionRef, Authorizer, Decision, Distincter, Event, LoweredPolicySet, ParsedPolicySet,
    PolicySchema, ProviderDeclarations, ProviderField, ProviderRequest, ProviderResolver,
    ServiceSchema, TemporalField, Validator, Value, lower_many,
};

/// `Read` ungrouped; `Write` and `Delete` members of the `Mutate` group.
const SCHEMA: &str = r#"
namespace Drupe {
  entity Gateway;
  entity OAuthUser;
  action "Mutate";
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: { key: String } }
  };
  action "Write" in [Action::"Mutate"] appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: { key: String } }
  };
  action "Delete" in [Action::"Mutate"] appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: { key: String } }
  };
}
"#;

/// One provider with a record output (`{ body: String }`).
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
        "script": "fn evaluate(base, key) { #{ body: \"ok\" } }"
      }
    }
  }
}
"#;

const P_READ: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when { Http::Fetch("http://example.com", context.input.key).body != "BLOCKED" };
"#;

const P_WRITE: &str = r#"
permit ( principal, action == Drupe::Action::"Write", resource )
when { Http::Fetch("http://example.com", context.input.key).body != "BLOCKED" };
"#;

const P_GROUP: &str = r#"
permit ( principal, action in Drupe::Action::"Mutate", resource )
when { Http::Fetch("http://example.com", context.input.key).body != "BLOCKED" };
"#;

const T_READ: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Read"::request{ input.key: context.input.key }
};
"#;

/// One rule: a temporal clause, then a provider call.
const MIXED: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Read"::request{ input.key: context.input.key }
}
when { Http::Fetch("http://example.com", context.input.key).body != "BLOCKED" };
"#;

const CEDAR_ONLY: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when { context.input.key == "allowed" };
"#;

/// Calls a provider the declarations do not name.
const P_UNDECLARED: &str = r#"
forbid ( principal, action == Drupe::Action::"Read", resource )
when { Nope::Call("undeclared_arg") == "y" };
"#;

thread_local! {
    /// One service schema per test, so every parse uses a clone of it.
    static SERVICE: ServiceSchema = ServiceSchema::builder()
        .providers(ProviderDeclarations::from_json(PROVIDERS).expect("providers parse"))
        .build()
        .expect("service schema builds");
}

fn service() -> ServiceSchema {
    SERVICE.with(ServiceSchema::clone)
}

fn base_schema() -> PolicySchema {
    PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema")
}

fn distincter(d: &str) -> Distincter {
    d.parse()
        .unwrap_or_else(|e| panic!("`{d}` is a distincter: {e}"))
}

fn lower(policy: &str, distincter: &str) -> LoweredPolicySet {
    ParsedPolicySet::parse(policy, &service())
        .expect("parses")
        .lower_with_distincter(&base_schema(), distincter)
        .unwrap_or_else(|e| panic!("`{distincter}` lowers: {e}"))
}

fn many(policies: &[(&str, &str)]) -> LoweredPolicySet {
    let parsed: Vec<ParsedPolicySet> = policies
        .iter()
        .map(|(policy, _)| ParsedPolicySet::parse(policy, &service()).expect("parses"))
        .collect();
    let entries: Vec<(&ParsedPolicySet, Distincter)> = parsed
        .iter()
        .zip(policies)
        .map(|(p, (_, d))| (p, distincter(d)))
        .collect();
    lower_many(&entries, &base_schema()).expect("lower_many")
}

fn rule_ids(set: &LoweredPolicySet) -> Vec<String> {
    set.rules().map(|r| r.cedar_policy_id).collect()
}

fn provider_ids(set: &LoweredPolicySet) -> Vec<String> {
    set.provider_fields().map(|f| f.id.clone()).collect()
}

fn leaf_ids(set: &LoweredPolicySet) -> Vec<String> {
    set.temporal_fields().map(|f| f.id.clone()).collect()
}

fn schema_json(set: &LoweredPolicySet) -> serde_json::Value {
    serde_json::from_str(&set.cedar_schema_json().expect("serializes")).expect("JSON")
}

/// `Drupe::Action::"<action>"`'s context attributes.
fn context_attributes(
    json: &serde_json::Value,
    action: &str,
) -> serde_json::Map<String, serde_json::Value> {
    json["Drupe"]["actions"][action]["appliesTo"]["context"]["attributes"]
        .as_object()
        .unwrap_or_else(|| panic!("{action} context attributes"))
        .clone()
}

/// The field names of the shared `DogwoodProviders` common type.
fn shared_provider_fields(json: &serde_json::Value) -> BTreeSet<String> {
    let common = json["Drupe"]["commonTypes"]
        .as_object()
        .expect("common types");
    assert_eq!(
        common
            .keys()
            .filter(|k| k.as_str() == "DogwoodProviders")
            .count(),
        1
    );
    common["DogwoodProviders"]["attributes"]
        .as_object()
        .expect("DogwoodProviders is a record")
        .keys()
        .cloned()
        .collect()
}

/// The common type `context.providers` references, if any.
fn providers_reference(attributes: &serde_json::Map<String, serde_json::Value>) -> Option<&str> {
    let providers = attributes.get("providers")?;
    if providers["type"] == "EntityOrCommon" {
        providers["name"].as_str()
    } else {
        providers["type"].as_str()
    }
}

/// Rewrite every hoisted id in `set` to `r<rule index><suffix>`, so sets that
/// differ only in distincters agree.
fn id_normaliser(set: &LoweredPolicySet) -> BTreeMap<String, String> {
    let rules: Vec<String> = rule_ids(set);
    let mut out = BTreeMap::new();
    for id in provider_ids(set).into_iter().chain(leaf_ids(set)) {
        let (k, rule) = rules
            .iter()
            .enumerate()
            .filter(|(_, r)| {
                id.starts_with(&format!("{r}_p_")) || id.starts_with(&format!("{r}__"))
            })
            .max_by_key(|(_, r)| r.len())
            .unwrap_or_else(|| panic!("`{id}` has a rule prefix"));
        out.insert(id.clone(), format!("r{k}{}", &id[rule.len()..]));
    }
    out
}

/// `value` with every object key renamed through `names`.
fn renamed(value: &serde_json::Value, names: &BTreeMap<String, String>) -> serde_json::Value {
    match value {
        serde_json::Value::Object(map) => map
            .iter()
            .map(|(k, v)| (names.get(k).unwrap_or(k).clone(), renamed(v, names)))
            .collect::<serde_json::Map<_, _>>()
            .into(),
        serde_json::Value::Array(items) => items.iter().map(|v| renamed(v, names)).collect(),
        other => other.clone(),
    }
}

/// A provider field without its distincter, and without its source offsets.
fn normalised_provider(
    field: &ProviderField,
    names: &BTreeMap<String, String>,
) -> impl PartialEq + std::fmt::Debug {
    (
        names[&field.id].clone(),
        field.action.clone(),
        field.target_actions.clone(),
        field.principal.clone(),
        field.resource.clone(),
        field.invocation.function.clone(),
        field.invocation.args.clone(),
        field.methods.clone(),
        field.declaration.clone(),
    )
}

/// A temporal leaf without its distincter, and without its source span.
fn normalised_leaf(
    leaf: &TemporalField,
    names: &BTreeMap<String, String>,
) -> impl PartialEq + std::fmt::Debug {
    (
        names[&leaf.id].clone(),
        leaf.action.clone(),
        leaf.target_actions.clone(),
        leaf.principal.clone(),
        leaf.resource.clone(),
        leaf.condition.condition.clone(),
    )
}

fn action(id: &str) -> ActionRef {
    ActionRef {
        namespace: Some("Drupe".to_string()),
        id: id.to_string(),
    }
}

#[test]
fn provider_ids_have_the_distincter_shape() {
    let set = many(&[(P_READ, "pr"), (MIXED, "mx")]);
    assert_eq!(provider_ids(&set), ["pr_0_p_0", "mx_0_p_1"]);
    // MIXED's temporal clause precedes its provider call and takes ordinal 0.
    assert_eq!(leaf_ids(&set), ["mx_0__temporal_0"]);
}

#[test]
fn provider_ids_do_not_depend_on_other_entries() {
    let parts = [
        (P_READ, "pr"),
        (P_WRITE, "pw"),
        (P_GROUP, "pg"),
        (T_READ, "tr"),
        (MIXED, "mx"),
        (CEDAR_ONLY, "co"),
    ];
    let merged = many(&parts);
    let expected_providers: Vec<String> = parts
        .iter()
        .flat_map(|(p, d)| provider_ids(&lower(p, d)))
        .collect();
    let expected_leaves: Vec<String> = parts
        .iter()
        .flat_map(|(p, d)| leaf_ids(&lower(p, d)))
        .collect();
    assert_eq!(provider_ids(&merged), expected_providers);
    assert_eq!(leaf_ids(&merged), expected_leaves);

    let sorted = |set: &LoweredPolicySet| {
        let mut ids: Vec<String> = rule_ids(set)
            .into_iter()
            .chain(provider_ids(set))
            .chain(leaf_ids(set))
            .collect();
        ids.sort();
        ids
    };
    let mut reversed = parts.to_vec();
    reversed.reverse();
    assert_eq!(sorted(&many(&parts)), sorted(&many(&reversed)));
    let mut rotated = parts.to_vec();
    rotated.rotate_left(2);
    assert_eq!(sorted(&many(&parts)), sorted(&many(&rotated)));
}

#[test]
fn lower_many_with_providers_matches_lowering_the_concatenation() {
    // With providers the "union of standalone lowerings" oracle does not
    // apply to the schema: each standalone lowering's shared
    // `DogwoodProviders` type holds only its own fields. Lowering the
    // concatenation builds one shared type over every field, as
    // `lower_many` must, so it is the oracle here.
    let parts = [
        (P_READ, "pr"),
        (P_WRITE, "pw"),
        (MIXED, "mx"),
        (T_READ, "tr"),
    ];
    let merged = many(&parts);
    let text: Vec<&str> = parts.iter().map(|(p, _)| *p).collect();
    let concatenated = lower(&text.join("\n"), "all");
    let (m_names, c_names) = (id_normaliser(&merged), id_normaliser(&concatenated));

    assert_eq!(merged.rules().count(), concatenated.rules().count());
    assert_eq!(merged.provider_fields().count(), 3);
    assert_eq!(
        merged
            .provider_fields()
            .map(|f| normalised_provider(f, &m_names))
            .collect::<Vec<_>>(),
        concatenated
            .provider_fields()
            .map(|f| normalised_provider(f, &c_names))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        merged
            .temporal_fields()
            .map(|f| normalised_leaf(f, &m_names))
            .collect::<Vec<_>>(),
        concatenated
            .temporal_fields()
            .map(|f| normalised_leaf(f, &c_names))
            .collect::<Vec<_>>()
    );
    // `ProviderField` does not expose its Cedar type; the schema carries it.
    assert_eq!(
        renamed(&schema_json(&merged), &m_names),
        renamed(&schema_json(&concatenated), &c_names)
    );
}

#[test]
fn shared_provider_type_spans_entries() {
    let set = many(&[(P_READ, "pr"), (P_WRITE, "pw"), (CEDAR_ONLY, "co")]);
    let json = schema_json(&set);
    assert_eq!(
        shared_provider_fields(&json),
        BTreeSet::from(["pr_0_p_0".to_string(), "pw_0_p_0".to_string()])
    );
    for action in ["Read", "Write"] {
        let attributes = context_attributes(&json, action);
        assert_eq!(
            attributes["providers"]["type"], "DogwoodProviders",
            "{action}"
        );
    }
    assert!(!context_attributes(&json, "Delete").contains_key("providers"));

    let text = set.cedar_schema_str().expect("serializes");
    for id in provider_ids(&set) {
        assert_eq!(text.matches(&id).count(), 1, "`{id}` defined once:\n{text}");
    }
}

#[test]
fn only_one_entry_has_providers() {
    let set = many(&[(T_READ, "tr"), (P_WRITE, "pw"), (CEDAR_ONLY, "co")]);
    let json = schema_json(&set);

    let read = context_attributes(&json, "Read");
    assert_eq!(read["tr_0__temporal_0"]["type"], "Boolean", "{read:?}");
    assert!(!read.contains_key("providers"), "{read:?}");

    let write = context_attributes(&json, "Write");
    assert_eq!(providers_reference(&write), Some("DogwoodProviders"));
    assert!(
        !write.keys().any(|k| k.contains("__temporal_")),
        "{write:?}"
    );

    let delete = context_attributes(&json, "Delete");
    assert_eq!(delete.keys().collect::<Vec<_>>(), ["input"], "{delete:?}");

    assert_eq!(
        shared_provider_fields(&json),
        BTreeSet::from(["pw_0_p_0".to_string()])
    );
}

#[test]
fn group_scoped_provider_reaches_every_member() {
    let set = many(&[(P_GROUP, "pg"), (P_READ, "pr")]);
    let group = set
        .provider_fields()
        .find(|f| f.id == "pg_0_p_0")
        .expect("group-scoped field");
    let targets: BTreeSet<String> = group.target_actions.iter().map(|a| a.id.clone()).collect();
    assert_eq!(
        targets,
        BTreeSet::from(["Write".to_string(), "Delete".to_string()])
    );
    assert!(
        group
            .target_actions
            .iter()
            .all(|a| *a == action("Write") || *a == action("Delete"))
    );

    let json = schema_json(&set);
    for action in ["Read", "Write", "Delete"] {
        assert_eq!(
            providers_reference(&context_attributes(&json, action)),
            Some("DogwoodProviders"),
            "{action}"
        );
    }
    assert_eq!(
        shared_provider_fields(&json),
        BTreeSet::from(["pg_0_p_0".to_string(), "pr_0_p_0".to_string()])
    );
}

#[test]
fn provider_findings_render_against_their_own_entry() {
    // Undeclared providers lower (typed `String`); validation reports them.
    let set = many(&[(P_READ, "pr"), (P_UNDECLARED, "bad")]);
    let result = Validator::new().validate(&set);
    let rendered: Vec<String> = result
        .validation_errors()
        .filter(|e| e.to_string().contains("Nope::Call"))
        .map(|e| format!("{:?}", miette::Report::new(e.clone())))
        .collect();
    assert!(
        !rendered.is_empty(),
        "an undeclared-provider finding; got: {:?}",
        result
            .validation_errors()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    );
    for report in &rendered {
        assert!(
            report.contains(r#"Nope::Call("undeclared_arg")"#),
            "renders the second entry's text:\n{report}"
        );
        assert!(
            !report.contains("http://example.com"),
            "renders none of the first entry's text:\n{report}"
        );
    }
}

#[test]
fn provider_ids_are_injective_across_adversarial_distincters() {
    let distincters = ["a", "a_0", "a_0_p", "a_0_p_1", "a__temporal"];
    let parts: Vec<_> = distincters.iter().map(|d| (MIXED, *d)).collect();
    // `lower_many` succeeding means Cedar accepted every policy id as new.
    let merged = many(&parts);
    // Rule, temporal, and provider ids live in different namespaces (policy
    // ids, `context.<id>`, `context.providers.<id>`); each must be injective.
    for ids in [rule_ids(&merged), leaf_ids(&merged), provider_ids(&merged)] {
        assert_eq!(ids.len(), distincters.len(), "{ids:?}");
        let distinct: BTreeSet<_> = ids.iter().collect();
        assert_eq!(distinct.len(), ids.len(), "{ids:?}");
    }
    assert_eq!(
        shared_provider_fields(&schema_json(&merged)),
        provider_ids(&merged).into_iter().collect()
    );
}

/// Resolves every provider call to `{ body: <body> }`.
struct BodyResolver {
    body: Arc<Mutex<String>>,
}

impl ProviderResolver for BodyResolver {
    fn resolve(&self, _request: ProviderRequest<'_>) -> Option<Result<Value, String>> {
        let body = self.body.lock().expect("body lock").clone();
        Some(Ok(Value::Object(BTreeMap::from([(
            "body".to_string(),
            Value::String(body),
        )]))))
    }
}

#[test]
fn an_authorizer_decides_over_providers_from_two_entries() {
    let set = many(&[(P_READ, "pr"), (P_WRITE, "pw")]);
    assert!(Validator::new().validate(&set).validation_passed());
    let body = Arc::new(Mutex::new("ok".to_string()));
    let mut authorizer = Authorizer::builder(set)
        .provider_resolver(BodyResolver { body: body.clone() })
        .build()
        .expect("authorizer builds");
    let request = |action: &str| {
        Event::builder(&format!("Drupe::Action::{action}"), "request")
            .principal("Drupe::OAuthUser::\"alice\"")
            .resource("Drupe::Gateway::\"gw\"")
            .field("input", "key", Value::String("doc".to_string()))
            .build()
    };
    let reasons = |r: &dogwood_language::Response| -> Vec<(usize, String)> {
        r.diagnostics()
            .reason()
            .map(|r| (r.rule_index, r.cedar_policy_id.clone()))
            .collect()
    };

    let read = authorizer.is_authorized(&request("Read")).expect("decides");
    assert_eq!(read.decision(), Decision::Allow);
    assert_eq!(reasons(&read), [(0, "pr_0".to_string())]);

    let write = authorizer
        .is_authorized(&request("Write"))
        .expect("decides");
    assert_eq!(write.decision(), Decision::Allow);
    assert_eq!(reasons(&write), [(1, "pw_0".to_string())]);

    *body.lock().expect("body lock") = "BLOCKED".to_string();
    for action in ["Read", "Write"] {
        let blocked = authorizer.is_authorized(&request(action)).expect("decides");
        assert_eq!(blocked.decision(), Decision::Deny, "{action}");
        assert!(
            reasons(&blocked).is_empty(),
            "{action}: {:?}",
            reasons(&blocked)
        );
    }
}

#[test]
fn from_many_str_with_providers_equals_lower_many() {
    let parts = [
        (P_READ, "pr"),
        (P_WRITE, "pw"),
        (MIXED, "mx"),
        (T_READ, "tr"),
    ];
    let entries: Vec<(&str, Distincter)> = parts.iter().map(|(p, d)| (*p, distincter(d))).collect();
    let fused =
        LoweredPolicySet::from_many_str(&entries, &service(), &base_schema()).expect("fused");
    let two_phase = many(&parts);
    assert_eq!(provider_ids(&fused), provider_ids(&two_phase));
    assert_eq!(leaf_ids(&fused), leaf_ids(&two_phase));
    assert_eq!(
        fused.cedar_schema_str().expect("serializes"),
        two_phase.cedar_schema_str().expect("serializes")
    );
}
