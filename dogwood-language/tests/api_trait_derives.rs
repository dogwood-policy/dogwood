//! The standard testing traits (`Debug`, `PartialEq`, `Eq`) are available on
//! the API's data types, so downstream unit tests can `assert_eq!` on them and
//! print them on failure. This pins the capability the API promises; it also
//! guards against a future field addition that would silently drop a derive
//! (a non-comparable field would fail this to compile).
//!
//! It deliberately does NOT assert equality on the opaque handles
//! (`LoweredPolicySet` / `ParsedPolicySet` / `Authorizer`): those are `Debug`
//! only, by design — see their type docs.

use std::collections::BTreeMap;

use dogwood_language::{
    ActionRef, ActionScope, Arg, Authorizer, Decision, Invocation, LoweredPolicySet,
    ParsedPolicySet, PolicySchema, ProviderDeclarations, ProviderField, Response, ServiceSchema,
    Value,
};

/// Statically require `T: Debug + PartialEq + Eq`. If a future change drops
/// one of these from a listed type, this stops compiling.
fn assert_debug_eq<T: std::fmt::Debug + PartialEq + Eq>() {}

/// Statically require `T: Debug` (for the opaque handles, which have `Debug`
/// but intentionally no equality).
fn assert_debug<T: std::fmt::Debug>() {}

#[test]
fn data_types_are_debug_eq() {
    // Value model + events.
    assert_debug_eq::<Value>();
    // Authorization results.
    assert_debug_eq::<Response>();
    // Hoisted-leaf / mapping types.
    assert_debug_eq::<ActionRef>();
    assert_debug_eq::<ActionScope>();
    assert_debug_eq::<ProviderField>();
    // Provider invocation data + declarations.
    assert_debug_eq::<Invocation>();
    assert_debug_eq::<Arg>();
    assert_debug_eq::<ProviderDeclarations>();
}

#[test]
fn opaque_handles_are_debug_only() {
    // These carry Debug for test output but no equality (opaque by design).
    assert_debug::<LoweredPolicySet>();
    assert_debug::<ParsedPolicySet>();
    assert_debug::<Authorizer>();
    assert_debug::<ServiceSchema>();
    assert_debug::<PolicySchema>();
}

#[test]
fn value_equality_is_structural() {
    // `==` is structural (the derive), so it is exact and predictable in tests.
    assert_eq!(
        Value::String("alice".to_string()),
        Value::String("alice".to_string())
    );
    assert_ne!(Value::Int(1), Value::Int(2));

    let a = Value::Object(BTreeMap::from([(
        "k".to_string(),
        Value::Array(vec![Value::Bool(true)]),
    )]));
    let b = Value::Object(BTreeMap::from([(
        "k".to_string(),
        Value::Array(vec![Value::Bool(true)]),
    )]));
    assert_eq!(a, b, "nested structural equality holds");

    // Structural `==` on decimals compares the text verbatim (unlike the
    // domain-canonical `dom_eq`), so `"1.5"` and `"1.50"` are NOT `==`.
    assert_ne!(
        Value::Decimal("1.5".to_string()),
        Value::Decimal("1.50".to_string()),
        "structural equality is verbatim; dom_eq is the canonical comparison"
    );
}

#[test]
fn response_equality_lets_tests_assert_a_whole_verdict() {
    // The point of the request: compare a full authorization Response.
    let policy = r#"permit ( principal, action == Svc::Action::"Read", resource );"#;
    let service = ServiceSchema::defaults();
    let schema = PolicySchema::from_cedarschema_str(
        r#"namespace Svc { entity Gateway; entity User; action "Read" appliesTo { principal: [User], resource: [Gateway] }; }"#,
    )
    .expect("policy schema");

    let lower = || LoweredPolicySet::from_str(policy, &service, &schema).expect("lower");

    let ev = || {
        dogwood_language::Event::builder("Svc::Action::Read", "request")
            .principal("Svc::User::\"alice\"")
            .resource("Svc::Gateway::\"gw1\"")
            .build()
    };

    let r1 = Authorizer::new(lower()).is_authorized(&ev());
    let r2 = Authorizer::new(lower()).is_authorized(&ev());
    // Two independent runs of the same policy/event produce equal Responses.
    assert_eq!(r1, r2);
    assert_eq!(r1.map(|r| r.decision()), Some(Decision::Allow));
}

#[test]
fn parsed_policy_handle_is_debug_and_copy() {
    // ParsedPolicy is a Copy handle (three references) and prints for tests.
    let src = r#"permit ( principal, action == Svc::Action::"Read", resource );"#;
    let parsed = ParsedPolicySet::parse(src, &ServiceSchema::defaults()).expect("parses");
    let p = parsed.policies().next().unwrap();
    let p_copy = p; // Copy
    let _ = format!("{p:?} {p_copy:?}");
    assert_eq!(p.index(), p_copy.index());
}
