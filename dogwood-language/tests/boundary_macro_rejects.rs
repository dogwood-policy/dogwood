//! Phase 2: Confirm macro expansion rejects invalid macro usage before
//! lowering sees it.
//!
//! Every rejection test passes source with macro issues to
//! `LoweredPolicySet::from_str()` and pattern-matches on `Error::Macro` to
//! ensure the error is caught at the right phase. The `Display` message is
//! checked for expected substrings.
//!
//! Sanity tests verify that valid macros expand to the expected number of
//! Cedar policies and that the lowered output references the expected content.

use dogwood_language::{Error, LoweredPolicySet, PolicySchema, ServiceSchema};

const SCHEMA: &str = r#"
    namespace Drupe {
      entity OAuthUser;
      entity Gateway;
      action "Read" appliesTo {
        principal: [OAuthUser], resource: [Gateway],
        context: { input: { x: String, amount: Long } }
      };
      action "Login" appliesTo {
        principal: [OAuthUser], resource: [Gateway],
        context: { input: { user: String } }
      };
    }
"#;

const MULTI_NS_SCHEMA: &str = r#"
    namespace Drupe {
      entity OAuthUser;
      entity Gateway;
      action "Read" appliesTo {
        principal: [OAuthUser], resource: [Gateway],
        context: { input: { x: String, amount: Long } }
      };
      action "Login" appliesTo {
        principal: [OAuthUser], resource: [Gateway],
        context: { input: { user: String } }
      };
    }
    namespace OtherNS {
      entity Bot;
      entity Service;
      action "Invoke" appliesTo {
        principal: [Bot], resource: [Service],
        context: { input: { payload: String } }
      };
    }
"#;

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

fn try_lower(src: &str) -> Result<LoweredPolicySet, Error> {
    try_lower_with_schema(src, SCHEMA)
}

fn try_lower_with_schema(src: &str, schema_str: &str) -> Result<LoweredPolicySet, Error> {
    let schema = PolicySchema::from_cedarschema_str(schema_str).unwrap();
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .unwrap();
    LoweredPolicySet::from_str(src, &service, &schema)
}

fn assert_macro_error(src: &str, expected_substring: &str) {
    assert_macro_error_with_schema(src, SCHEMA, expected_substring);
}

fn assert_macro_error_with_schema(src: &str, schema_str: &str, expected_substring: &str) {
    let result = try_lower_with_schema(src, schema_str);
    let err = result.expect_err("expected macro error for input");
    assert!(
        matches!(&err, Error::Macro(_)),
        "expected Error::Macro variant, got: {err}"
    );
    let display = err.to_string();
    assert!(
        display.contains(expected_substring),
        "error Display should mention {expected_substring:?}, got: {display}"
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Undefined macro calls
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn undefined_cedar_macro_call() {
    assert_macro_error(
        r#"
            permit(principal, action == Drupe::Action::"Read", resource)
              when { undefined_macro(context.input.x) };
        "#,
        "unknown function or macro",
    );
}

#[test]
fn undefined_temporal_macro_call() {
    assert_macro_error(
        r#"
            permit(principal, action == Drupe::Action::"Read", resource)
              when temporal { nonexistent_macro(context.input.x) };
        "#,
        "unknown macro",
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Wrong argument count
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn cedar_macro_too_few_args() {
    assert_macro_error(
        r#"
            def cedar is_small(?amount) { ?amount < 100 };
            permit(principal, action == Drupe::Action::"Read", resource)
              when { is_small() };
        "#,
        "argument",
    );
}

#[test]
fn cedar_macro_too_many_args() {
    assert_macro_error(
        r#"
            def cedar is_small(?amount) { ?amount < 100 };
            permit(principal, action == Drupe::Action::"Read", resource)
              when { is_small(context.input.amount, context.input.x) };
        "#,
        "argument",
    );
}

#[test]
fn temporal_macro_too_few_args() {
    assert_macro_error(
        r#"
            def temporal was_login(?user) { formerly within 1h Drupe::Action::"Login"::request{ input.user: ?user } };
            permit(principal, action == Drupe::Action::"Read", resource)
              when temporal { was_login() };
        "#,
        "argument",
    );
}

#[test]
fn temporal_macro_too_many_args() {
    assert_macro_error(
        r#"
            def temporal was_login(?user) { formerly within 1h Drupe::Action::"Login"::request{ input.user: ?user } };
            permit(principal, action == Drupe::Action::"Read", resource)
              when temporal { was_login(context.input.x, context.input.amount) };
        "#,
        "argument",
    );
}

#[test]
fn zero_param_cedar_macro_called_with_args() {
    assert_macro_error(
        r#"
            def cedar always_true() { true };
            permit(principal, action == Drupe::Action::"Read", resource)
              when { always_true(context.input.x) };
        "#,
        "argument",
    );
}

#[test]
fn zero_param_temporal_macro_called_with_args() {
    assert_macro_error(
        r#"
            def temporal had_login() { formerly within 1h Drupe::Action::"Login"::request{} };
            permit(principal, action == Drupe::Action::"Read", resource)
              when temporal { had_login(context.input.x) };
        "#,
        "argument",
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Temporal block inside cedar macro (disallowed)
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn temporal_block_inside_cedar_macro() {
    assert_macro_error(
        r#"
            def cedar has_login() { temporal { formerly within 1h Drupe::Action::"Login"::request{} } };
            permit(principal, action == Drupe::Action::"Read", resource)
              when { has_login() };
        "#,
        "not allowed",
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Recursive / mutually-recursive macros
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn self_recursive_cedar_macro() {
    assert_macro_error(
        r#"
            def cedar loop(?x) { loop(?x) };
            permit(principal, action == Drupe::Action::"Read", resource)
              when { loop(context.input.x) };
        "#,
        "macro-in-macro is not supported",
    );
}

#[test]
fn mutually_recursive_cedar_macros() {
    assert_macro_error(
        r#"
            def cedar ping(?x) { pong(?x) };
            def cedar pong(?x) { ping(?x) };
            permit(principal, action == Drupe::Action::"Read", resource)
              when { ping(context.input.x) };
        "#,
        "macro-in-macro is not supported",
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Valid macro usage (sanity — should NOT error, with output assertions)
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn valid_cedar_macro_expands() {
    let lowered = try_lower(
        r#"
        def cedar is_small(?amount) { ?amount < 100 };
        permit(principal, action == Drupe::Action::"Read", resource)
          when { is_small(context.input.amount) };
    "#,
    )
    .expect("valid cedar macro should expand");

    assert_eq!(lowered.as_cedar().policies().count(), 1);
    let cedar_text = lowered.as_cedar().to_string();
    assert!(
        cedar_text.contains("100"),
        "expanded policy should reference literal 100, got: {cedar_text}"
    );
}

#[test]
fn valid_temporal_macro_expands() {
    let lowered = try_lower(r#"
        def temporal was_login(?user) { formerly within 1h Drupe::Action::"Login"::request{ input.user: ?user } };
        permit(principal, action == Drupe::Action::"Read", resource)
          when temporal { was_login(context.input.x) };
    "#)
    .expect("valid temporal macro should expand");

    assert_eq!(lowered.as_cedar().policies().count(), 1);
    // Temporal conditions get hoisted into a context field (e.g. policy_0__temporal_0).
    let cedar_text = lowered.as_cedar().to_string();
    assert!(
        cedar_text.contains("temporal"),
        "expanded temporal policy should reference a hoisted temporal context field, got: {cedar_text}"
    );
    // The augmented schema should carry the Login action's temporal constraint.
    let schema_text = lowered.cedar_schema_str().expect("schema should serialize");
    assert!(
        schema_text.contains("temporal"),
        "augmented schema should contain temporal hoisted field, got: {schema_text}"
    );
}

#[test]
fn valid_macro_with_multiple_params() {
    let lowered = try_lower(
        r#"
        def cedar in_range(?val, ?lo, ?hi) { ?val >= ?lo && ?val < ?hi };
        permit(principal, action == Drupe::Action::"Read", resource)
          when { in_range(context.input.amount, 0, 100) };
    "#,
    )
    .expect("multi-param macro should expand");

    assert_eq!(lowered.as_cedar().policies().count(), 1);
    let cedar_text = lowered.as_cedar().to_string();
    assert!(
        cedar_text.contains("100") && cedar_text.contains("0"),
        "expanded policy should reference both bound values, got: {cedar_text}"
    );
}

#[test]
fn valid_zero_param_cedar_macro() {
    let lowered = try_lower(
        r#"
        def cedar always_true() { true };
        permit(principal, action == Drupe::Action::"Read", resource)
          when { always_true() };
    "#,
    )
    .expect("zero-param cedar macro should expand");

    assert_eq!(lowered.as_cedar().policies().count(), 1);
    let cedar_text = lowered.as_cedar().to_string();
    assert!(
        cedar_text.contains("true"),
        "expanded policy should reference literal true, got: {cedar_text}"
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Cross-namespace macro usage
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn macro_referencing_different_namespace_action() {
    let lowered = try_lower_with_schema(
        r#"
            def temporal bot_invoked(?payload) { formerly within 1h OtherNS::Action::"Invoke"::request{ input.payload: ?payload } };
            permit(principal, action == Drupe::Action::"Read", resource)
              when temporal { bot_invoked(context.input.x) };
        "#,
        MULTI_NS_SCHEMA,
    )
    .expect("macro referencing cross-namespace action should expand");

    assert_eq!(lowered.as_cedar().policies().count(), 1);
    // Temporal conditions are hoisted; the lowered Cedar policy references a
    // context field, not the original action name. Verify the hoisted field
    // exists and the schema was augmented for the cross-namespace reference.
    let cedar_text = lowered.as_cedar().to_string();
    assert!(
        cedar_text.contains("temporal"),
        "expanded policy should reference a hoisted temporal context field, got: {cedar_text}"
    );
    let schema_text = lowered.cedar_schema_str().expect("schema should serialize");
    assert!(
        schema_text.contains("temporal"),
        "augmented schema should contain temporal hoisted field for cross-ns macro, got: {schema_text}"
    );
}
