//! Adversarial and edge-case tests for the cedarify lowering pipeline.
//!
//! These exercise error paths, weird inputs, and boundary conditions through
//! the public API (`LoweredPolicySet::from_str`). The goal is to break things:
//! malformed provider arguments, deeply nested expressions, empty schemas,
//! unicode edge cases, and inputs that are syntactically valid but
//! semantically degenerate.

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema};

const MINIMAL_SCHEMA: &str = r#"
    namespace App {
      entity User;
      entity Doc;
      action "Read" appliesTo {
        principal: [User], resource: [Doc],
        context: { input: { x: String } }
      };
    }
"#;

fn lower(src: &str) -> Result<LoweredPolicySet, dogwood_language::Error> {
    let schema = PolicySchema::from_cedarschema_str(MINIMAL_SCHEMA).unwrap();
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .unwrap();
    LoweredPolicySet::from_str(src, &service, &schema)
}

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

// ═══════════════════════════════════════════════════════════════════════
// Provider argument rejection — weird inputs that must NOT lower
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn provider_arg_arithmetic_is_rejected() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check(1 + 2) == "ok" };
    "#;
    let result = lower(src);
    assert!(result.is_err(), "arithmetic provider arg should fail");
    let err = format!("{:?}", result.unwrap_err());
    assert!(
        err.contains("attribute path") || err.contains("provider argument"),
        "error should mention arg restriction: {err}"
    );
}

#[test]
fn provider_arg_if_expression_is_rejected() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check(if true then "a" else "b") == "ok" };
    "#;
    let result = lower(src);
    assert!(result.is_err(), "if-expr provider arg should fail");
}

#[test]
fn provider_arg_negation_is_rejected() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check(!true) == "ok" };
    "#;
    let result = lower(src);
    assert!(result.is_err(), "negation provider arg should fail");
}

#[test]
fn provider_arg_comparison_is_rejected() {
    // A comparison inside a provider argument should be rejected.
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check(context.input.x == "a") == "ok" };
    "#;
    let result = lower(src);
    assert!(result.is_err(), "comparison provider arg should fail");
}

#[test]
fn provider_arg_method_call_is_rejected() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check(context.input.x.contains("a")) == "ok" };
    "#;
    let result = lower(src);
    assert!(result.is_err(), "method call provider arg should fail");
}

#[test]
fn provider_arg_record_literal_is_rejected() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check({"key": "val"}) == "ok" };
    "#;
    let result = lower(src);
    assert!(result.is_err(), "record literal provider arg should fail");
}

#[test]
fn provider_arg_action_variable_is_rejected() {
    // `action` is not a valid provider argument — providers run pre-Cedar.
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check(action) == "ok" };
    "#;
    let result = lower(src);
    assert!(
        result.is_err(),
        "`action` variable as provider arg should fail"
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Provider argument acceptance — weird but valid inputs
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn provider_arg_nested_sets_accepted() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check([["a", "b"], ["c"]]) == "ok" };
    "#;
    let result = lower(src);
    assert!(result.is_ok(), "nested set arg should lower: {result:?}");
}

#[test]
fn provider_arg_decimal_literal_accepted() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check(decimal("0.5")) == "ok" };
    "#;
    let result = lower(src);
    assert!(
        result.is_ok(),
        "decimal literal arg should lower: {result:?}"
    );
}

#[test]
fn provider_arg_boolean_literal_accepted() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check(true) == "ok" };
    "#;
    let result = lower(src);
    assert!(result.is_ok(), "bool literal arg should lower: {result:?}");
}

#[test]
fn provider_arg_deep_attribute_path_accepted() {
    // context.input.x is about as deep as our schema goes, but the path
    // flattening logic should handle it.
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check(context.input.x) == "ok" };
    "#;
    let result = lower(src);
    assert!(
        result.is_ok(),
        "deep attr path arg should lower: {result:?}"
    );
}

#[test]
fn provider_with_zero_arguments_accepted() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check() == "ok" };
    "#;
    let result = lower(src);
    assert!(result.is_ok(), "zero-arg provider should lower: {result:?}");
}

#[test]
fn provider_with_many_arguments_accepted() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Ns::Check(context.input.x, "literal", 42, true, decimal("1.0"), [1, 2]) == "ok" };
    "#;
    let result = lower(src);
    assert!(result.is_ok(), "many-arg provider should lower: {result:?}");
}

// ═══════════════════════════════════════════════════════════════════════
// Temporal hoisting — edge cases
// ═══════════════════════════════════════════════════════════════════════

const TEMPORAL_SCHEMA: &str = r#"
    namespace Drupe {
      entity User;
      entity Doc;
      action "Read" appliesTo {
        principal: [User], resource: [Doc],
        context: { input: { x: String } }
      };
      action "Login" appliesTo {
        principal: [User], resource: [Doc],
        context: { input: { x: String } }
      };
    }
"#;

fn lower_temporal(src: &str) -> Result<LoweredPolicySet, dogwood_language::Error> {
    let schema = PolicySchema::from_cedarschema_str(TEMPORAL_SCHEMA).unwrap();
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .unwrap();
    LoweredPolicySet::from_str(src, &service, &schema)
}

#[test]
fn temporal_deeply_nested_in_if_then_else() {
    // Mid-expression temporal inside an if/then/else.
    let src = r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when {
            if context.input.x == "a"
            then temporal {
                formerly within 1h Drupe::Action::"Login"::request{}
            }
            else false
          };
    "#;
    let result = lower_temporal(src);
    assert!(
        result.is_ok(),
        "temporal in if-branch should lower: {result:?}"
    );
    assert!(!result.unwrap().is_self_contained_cedar());
}

#[test]
fn temporal_in_or_branch() {
    // Mid-expression temporal inside ||.
    let src = r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when {
            false || temporal {
                formerly within 1h Drupe::Action::"Login"::request{}
            }
          };
    "#;
    let result = lower_temporal(src);
    assert!(
        result.is_ok(),
        "temporal in || branch should lower: {result:?}"
    );
}

#[test]
fn two_temporal_leaves_same_policy_get_distinct_field_names() {
    // Two separate when-temporal clauses on one rule.
    let src = r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when temporal { formerly within 1h Drupe::Action::"Login"::request{} }
          when temporal { formerly within 2h Drupe::Action::"Login"::request{} };
    "#;
    let result = lower_temporal(src);
    assert!(
        result.is_ok(),
        "two temporal leaves should lower: {result:?}"
    );
    let schema_text = result.unwrap().cedar_schema_str().unwrap();
    assert!(schema_text.contains("policy_0__temporal_0"));
    assert!(schema_text.contains("policy_0__temporal_1"));
}

#[test]
fn temporal_across_two_policies_get_distinct_rule_keys() {
    let src = r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when temporal { formerly within 1h Drupe::Action::"Login"::request{} };
        forbid(principal, action == Drupe::Action::"Read", resource)
          when temporal { formerly within 1h Drupe::Action::"Login"::request{} };
    "#;
    let result = lower_temporal(src);
    assert!(
        result.is_ok(),
        "temporal in two policies should lower: {result:?}"
    );
    let schema_text = result.unwrap().cedar_schema_str().unwrap();
    assert!(schema_text.contains("policy_0__temporal_0"));
    assert!(schema_text.contains("policy_1__temporal_0"));
}

// ═══════════════════════════════════════════════════════════════════════
// Degenerate / boundary inputs
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn empty_source_lowers_to_empty_policy_set() {
    let result = lower("");
    assert!(result.is_ok());
    assert_eq!(result.unwrap().as_cedar().policies().count(), 0);
}

#[test]
fn bare_permit_no_conditions_lowers() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource);
    "#;
    let result = lower(src);
    assert!(result.is_ok());
    assert!(result.unwrap().is_self_contained_cedar());
}

#[test]
fn fifty_chained_and_conditions_no_stack_overflow() {
    let clauses: Vec<String> = (0..50)
        .map(|_| "context.input.x == \"a\"".to_string())
        .collect();
    let body = clauses.join(" && ");
    let src =
        format!("permit(principal, action == App::Action::\"Read\", resource) when {{ {body} }};",);
    let result = lower(&src);
    assert!(result.is_ok(), "50 && chain should lower: {result:?}");
}

#[test]
fn fifty_nested_not_operators() {
    // !!!!!...!!true — 50 negations. Tests recursive unary lowering.
    let nots = "!".repeat(50);
    let src = format!(
        "permit(principal, action == App::Action::\"Read\", resource) when {{ {nots}true }};",
    );
    // Cedar limits negation depth to 4 at parse, so this should fail at parse.
    // Either a parse error or a successful lower is fine — the test asserts
    // only that lowering does not panic.
    let _ = lower(&src);
}

#[test]
fn unicode_string_literal_survives_lowering() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { context.input.x == "こんにちは 🌍 \u{1F680}" };
    "#;
    let result = lower(src);
    assert!(result.is_ok(), "unicode should lower: {result:?}");
}

#[test]
fn empty_string_comparison_lowers() {
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { context.input.x == "" };
    "#;
    let result = lower(src);
    assert!(result.is_ok());
}

#[test]
fn multiple_unless_clauses_lower() {
    let src = r#"
        forbid(principal, action == App::Action::"Read", resource)
          unless { context.input.x == "admin" }
          unless { context.input.x == "root" };
    "#;
    let result = lower(src);
    assert!(result.is_ok(), "multiple unless should lower: {result:?}");
}

#[test]
fn schema_with_no_actions_temporal_unconstrained_scope() {
    // Empty schema + temporal leaf with unconstrained action scope.
    // The augmentation has no actions to augment — should not panic.
    let empty_schema = "entity User;";
    let schema = PolicySchema::from_cedarschema_str(empty_schema).unwrap();
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .unwrap();
    let src = r#"
        permit(principal, action, resource)
          when temporal { formerly within 1h Action::"X"::request{} };
    "#;
    let result = LoweredPolicySet::from_str(src, &service, &schema);
    // Must not panic — error or success are both acceptable.
    match &result {
        Ok(_) => {}
        Err(e) => {
            let msg = format!("{e:?}");
            assert!(
                !msg.contains("panic") && !msg.contains("unwrap"),
                "should not panic on empty schema: {msg}"
            );
        }
    }
}

#[test]
fn provider_undeclared_still_lowers_with_string_fallback() {
    // Ns::Fn is structurally a provider. Without declarations it hoists
    // with String type — validation catches the real error later.
    let src = r#"
        permit(principal, action == App::Action::"Read", resource)
          when { Unknown::Check(context.input.x) == "ok" };
    "#;
    let result = lower(src);
    assert!(
        result.is_ok(),
        "undeclared provider should lower: {result:?}"
    );
}

#[test]
fn policy_with_all_annotation_types() {
    let src = r#"
        @id("test-policy")
        @comment("this is a comment with \"quotes\" and unicode: 日本語")
        @empty
        permit(principal, action == App::Action::"Read", resource);
    "#;
    let result = lower(src);
    assert!(result.is_ok(), "annotated policy should lower: {result:?}");
}
