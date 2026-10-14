//! Regression: an information provider that errors at runtime is denied by
//! THIS reference implementation, with the error in diagnostics.
//!
//! Under the provider contract (guide, 05-information-providers) an
//! erroring provider is UNDEFINED BEHAVIOR — no semantic guarantee exists,
//! and policy sets must not rely on deny-on-error (defensive scripts are
//! the only defense). What this test pins is narrower and still valuable:
//! the reference implementation's chosen handling. `Authorizer::
//! is_authorized` is infallible by design — evaluation failures fold into
//! the response's diagnostics — and this implementation resolves a
//! provider error to `Deny` rather than authorizing against a *partial*
//! context (where a `permit` whose guard can no longer be checked could
//! fire). If this implementation choice changes deliberately, update this
//! test; policies must not depend on it either way.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema,
    Value,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type ReadInput = { document: String };
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

// Permit Read only when the provider says so. The whole permit is gated on
// the provider output, so if the provider cannot run there is no safe way to
// let the request through.
const POLICY: &str = r#"
permit (
    principal,
    action == Drupe::Action::"Read",
    resource
)
when guardrails {
    Risk::Score(context.input.document).ok == true
};
"#;

// A provider whose script always errors at runtime (it references an
// undefined function), so evaluating it fails.
const PROVIDERS: &str = r#"
{
  "availableProviders": {
    "Risk::Score": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "ok": { "paramType": "bool" } },
        "required": ["ok"]
      },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(doc) { this_function_does_not_exist(doc) }"
      }
    }
  }
}
"#;

#[test]
fn provider_runtime_failure_fails_closed() {
    let decls = ProviderDeclarations::from_json(PROVIDERS).expect("providers parse");
    let service = ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let policies = LoweredPolicySet::from_str(POLICY, &service, &policy_schema).expect("parse");

    let mut authorizer = Authorizer::new(policies);
    let event = dogwood_language::Event::builder("Drupe::Action::Read", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "document", Value::String("hello".to_string()))
        .build();

    let response = authorizer
        .is_authorized(&event)
        .expect("request is a decision point");

    // The provider blew up; this reference implementation resolves that to
    // a Deny (an erroring provider is UB — this pins the implementation's
    // chosen handling, not a semantic guarantee; see the file header).
    assert_eq!(
        response.decision(),
        Decision::Deny,
        "this implementation resolves a provider runtime failure to Deny",
    );
    // …and the failure must be visible in diagnostics, not swallowed silently.
    assert!(
        response.diagnostics().errors().next().is_some(),
        "the provider evaluation error should be recorded in diagnostics",
    );
}

/// The same pin for the OTHER provider error path: an external
/// [`ProviderResolver`] returning `Some(Err(..))`. Per the contract this is
/// UB for the decision outcome; this reference implementation currently
/// denies with the error in diagnostics (as documented on the trait), and
/// this test keeps that handling deliberate. It also guards a specific
/// drift hazard: the resolver protocol is three-valued (`None` = declined,
/// fall back to Rhai; `Some(Ok)` = value; `Some(Err)` = handled-and-failed),
/// and a refactor conflating `Some(Err)` with `None` would silently turn a
/// failing external provider into a fallback to the declared script.
#[test]
fn resolver_error_currently_denies_with_diagnostics() {
    // The declared Rhai implementation would SUCCEED (defensively, ok:true
    // for a present document) — so if `Some(Err)` were wrongly treated as a
    // decline-and-fall-back, the script would run, the permit would fire,
    // and this test would catch the flip to Allow.
    let providers = r#"
    {
      "availableProviders": {
        "Risk::Score": {
          "argumentTypes": [ { "paramType": "string" } ],
          "outputType": {
            "paramType": "record",
            "fields": { "ok": { "paramType": "bool" } },
            "required": ["ok"]
          },
          "implementation": {
            "kind": "rhai",
            "script": "fn evaluate(doc) { if type_of(doc) == \"()\" { return #{ ok: false }; } #{ ok: true } }"
          }
        }
      }
    }
    "#;
    struct FailingResolver;
    impl dogwood_language::ProviderResolver for FailingResolver {
        fn resolve(
            &self,
            _request: dogwood_language::ProviderRequest<'_>,
        ) -> Option<Result<Value, String>> {
            Some(Err("external provider backend unavailable".to_string()))
        }
    }

    let decls = ProviderDeclarations::from_json(providers).expect("providers parse");
    let service = ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let policies = LoweredPolicySet::from_str(POLICY, &service, &policy_schema).expect("parse");

    let mut authorizer = Authorizer::builder(policies)
        .provider_resolver(FailingResolver)
        .build()
        .expect("authorizer builds");
    let event = dogwood_language::Event::builder("Drupe::Action::Read", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "document", Value::String("hello".to_string()))
        .build();

    let response = authorizer
        .is_authorized(&event)
        .expect("request is a decision point");

    assert_eq!(
        response.decision(),
        Decision::Deny,
        "this implementation resolves a resolver Some(Err) to Deny; if the \
         resolver error were wrongly treated as a decline, the declared Rhai \
         script would have permitted"
    );
    let errors: Vec<&str> = response.diagnostics().errors().collect();
    assert!(
        errors.iter().any(|e| e.contains("backend unavailable")),
        "the resolver's error text should be recorded in diagnostics, got: {errors:?}"
    );
}

// ─── Enum-typed provider values ──────────────────────────────────────
//
// A provider value at an `entity` slot must be one of its enum's ids. Unlike
// a provider that errors, a value outside the enum is not UB: Dogwood rejects
// it, and the request is denied. Otherwise `"CRITICAL"` would become an entity
// that matches nothing, and the `forbid` below would silently not fire.

const ENUM_PROVIDERS: &str = r#"
{
  "entityTypes": { "Guard::Score": { "enum": ["LOW", "HIGH"] } },
  "availableProviders": {
    "Guard::Filter": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "result": { "paramType": "entity", "entityType": "Guard::Score" } },
        "required": ["result"]
      },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(doc) { if type_of(doc) == \"()\" { return #{ result: \"HIGH\" }; } if doc == \"boom\" { #{ result: \"CRITICAL\" } } else { #{ result: \"LOW\" } } }"
      }
    }
  }
}
"#;

// Allow everything except a HIGH result.
const ENUM_POLICY: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource);
forbid (principal, action == Drupe::Action::"Read", resource)
when { Guard::Filter(context.input.document).result == Guard::Score::"HIGH" };
"#;

fn enum_authorizer(resolver: Option<FixedResult>) -> Authorizer {
    let decls = ProviderDeclarations::from_json(ENUM_PROVIDERS).expect("providers parse");
    let service = ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let policies =
        LoweredPolicySet::from_str(ENUM_POLICY, &service, &policy_schema).expect("lowers");
    match resolver {
        None => Authorizer::new(policies),
        Some(r) => Authorizer::builder(policies)
            .provider_resolver(r)
            .build()
            .expect("authorizer builds"),
    }
}

fn decide(authorizer: &mut Authorizer, document: &str) -> (Decision, Vec<String>) {
    let event = dogwood_language::Event::builder("Drupe::Action::Read", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .request_context("input", "document", Value::String(document.to_string()))
        .build();
    let response = authorizer
        .is_authorized(&event)
        .expect("request is a decision point");
    let errors = response
        .diagnostics()
        .errors()
        .map(str::to_string)
        .collect();
    (response.decision(), errors)
}

/// A resolver returning a fixed `result` value.
struct FixedResult(Value);
impl dogwood_language::ProviderResolver for FixedResult {
    fn resolve(
        &self,
        _request: dogwood_language::ProviderRequest<'_>,
    ) -> Option<Result<Value, String>> {
        Some(Ok(Value::Object(
            [("result".to_string(), self.0.clone())]
                .into_iter()
                .collect(),
        )))
    }
}

#[test]
fn rhai_value_outside_its_enum_denies_with_the_reason() {
    let mut authorizer = enum_authorizer(None);
    assert_eq!(decide(&mut authorizer, "hello").0, Decision::Allow);

    let (decision, errors) = decide(&mut authorizer, "boom");
    assert_eq!(decision, Decision::Deny, "a non-member must not fail open");
    assert!(
        errors.iter().any(|e| e.contains(
            "provider `Guard::Filter`.result: `CRITICAL` is not a member of `Guard::Score`"
        )),
        "got: {errors:?}"
    );
}

#[test]
fn resolver_enum_ids_are_converted_and_enforced() {
    // An external resolver (e.g. an adapter for a vendor API) returns the
    // contract's ids as plain strings; Dogwood converts them like Rhai output.
    let mut low = enum_authorizer(Some(FixedResult(Value::String("LOW".into()))));
    assert_eq!(decide(&mut low, "anything").0, Decision::Allow);
    let mut high = enum_authorizer(Some(FixedResult(Value::String("HIGH".into()))));
    assert_eq!(decide(&mut high, "anything").0, Decision::Deny);
}

#[test]
fn resolver_value_outside_its_enum_denies() {
    // A vendor value the adapter did not translate.
    let mut authorizer = enum_authorizer(Some(FixedResult(Value::String("severe".into()))));
    let (decision, errors) = decide(&mut authorizer, "anything");
    assert_eq!(decision, Decision::Deny);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("`severe` is not a member of `Guard::Score`")),
        "got: {errors:?}"
    );
}

#[test]
fn resolver_entity_of_another_type_denies() {
    let mut authorizer = enum_authorizer(Some(FixedResult(Value::Entity {
        ty: "Other::Level".into(),
        id: "LOW".into(),
    })));
    let (decision, errors) = decide(&mut authorizer, "anything");
    assert_eq!(decision, Decision::Deny);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("expected a `Guard::Score`, got a `Other::Level`")),
        "got: {errors:?}"
    );
}

// A resolver supplies the base and Rhai runs the methods on it. The method
// must see an enum the resolver returned as an entity as its bare id, as it
// would a Rhai base. As uid text, `isHigh` would always be false and the
// `forbid` would silently not fire.

const METHOD_PROVIDERS: &str = r#"
{
  "entityTypes": { "Guard::Score": { "enum": ["LOW", "HIGH"] } },
  "availableProviders": {
    "Guard::Filter": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "result": { "paramType": "entity", "entityType": "Guard::Score" } },
        "required": ["result"]
      },
      "availableMethods": {
        "isHigh": { "argumentTypes": [], "outputType": { "paramType": "bool" } },
        "escalated": {
          "argumentTypes": [],
          "outputType": { "paramType": "entity", "entityType": "Guard::Score" }
        },
        "isHighScore": { "argumentTypes": [], "outputType": { "paramType": "bool" } }
      },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(doc) { #{ result: \"HIGH\" } } fn isHigh(input) { if type_of(input) == \"()\" { return true; } input.result == \"HIGH\" } fn escalated(input) { \"CRITICAL\" } fn isHighScore(score) { score == \"HIGH\" }"
      }
    }
  }
}
"#;

const METHOD_POLICY: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource);
forbid (principal, action == Drupe::Action::"Read", resource)
when { Guard::Filter(context.input.document).isHigh() };
"#;

fn method_authorizer(result: Value) -> Authorizer {
    method_authorizer_with(METHOD_POLICY, result)
}

fn method_authorizer_with(policy: &str, result: Value) -> Authorizer {
    let decls = ProviderDeclarations::from_json(METHOD_PROVIDERS).expect("providers parse");
    let service = ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let policies = LoweredPolicySet::from_str(policy, &service, &policy_schema).expect("lowers");
    Authorizer::builder(policies)
        .provider_resolver(FixedResult(result))
        .build()
        .expect("authorizer builds")
}

#[test]
fn a_method_sees_a_resolver_entity_as_its_id() {
    // The resolver may name the entity by its declared or its exported type.
    for ty in ["Guard::Score", "Drupe::Guard_Score"] {
        let entity = |id: &str| Value::Entity {
            ty: ty.into(),
            id: id.into(),
        };
        let (decision, errors) = decide(&mut method_authorizer(entity("HIGH")), "anything");
        assert_eq!(decision, Decision::Deny, "{ty}: the forbid must fire");
        assert!(errors.is_empty(), "{ty}: got {errors:?}");
        let (decision, _) = decide(&mut method_authorizer(entity("LOW")), "anything");
        assert_eq!(decision, Decision::Allow, "{ty}");
    }
}

// Each stage's value is checked against its enum before the next method
// runs, not only the last stage's. As the method's input, `CRITICAL` would
// make `isHigh` false, and the `forbid` would silently not fire.

#[test]
fn a_base_value_outside_its_enum_denies_before_a_method_runs() {
    let mut authorizer = method_authorizer(Value::String("CRITICAL".into()));
    let (decision, errors) = decide(&mut authorizer, "anything");
    assert_eq!(decision, Decision::Deny, "a non-member must not fail open");
    assert!(
        errors.iter().any(|e| e.contains(
            "provider `Guard::Filter`.result: `CRITICAL` is not a member of `Guard::Score`"
        )),
        "got: {errors:?}"
    );
}

#[test]
fn a_base_entity_of_another_type_denies_before_a_method_runs() {
    let mut authorizer = method_authorizer(Value::Entity {
        ty: "Other::Level".into(),
        id: "LOW".into(),
    });
    let (decision, errors) = decide(&mut authorizer, "anything");
    assert_eq!(decision, Decision::Deny);
    assert!(
        errors.iter().any(|e| e.contains(
            "provider `Guard::Filter`.result: expected a `Guard::Score`, got a `Other::Level`"
        )),
        "got: {errors:?}"
    );
}

#[test]
fn a_method_output_outside_its_enum_denies_before_the_next_method() {
    let policy = r#"
permit (principal, action == Drupe::Action::"Read", resource);
forbid (principal, action == Drupe::Action::"Read", resource)
when { Guard::Filter(context.input.document).escalated().isHighScore() };
"#;
    let mut authorizer = method_authorizer_with(policy, Value::String("LOW".into()));
    let (decision, errors) = decide(&mut authorizer, "anything");
    assert_eq!(decision, Decision::Deny, "a non-member must not fail open");
    assert!(
        errors.iter().any(|e| e.contains(
            "provider `Guard::Filter`.escalated(): `CRITICAL` is not a member of `Guard::Score`"
        )),
        "got: {errors:?}"
    );
}
