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
