//! Phase 4: Confirm the validator catches errors that earlier stages (parser,
//! macro expansion, lowering) intentionally let through.
//!
//! Every test here:
//! 1. Passes source through `LoweredPolicySet::from_str()` → asserts `Ok`
//! 2. Runs `Validator::validate()` on the result → asserts errors present
//! 3. Checks the error message/code matches the expected finding
//!
//! These are the errors that ONLY the validator can catch — the policy is
//! syntactically valid and lowers successfully, but is semantically wrong
//! against the schema.

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, Validator,
};

const SCHEMA: &str = r#"
    namespace Drupe {
      entity OAuthUser;
      entity Gateway;
      type ReadInput = { user: String, amount: Long, stock: String };
      type WriteInput = { user: String, data: String };
      action "Read" appliesTo {
        principal: [OAuthUser],
        resource: [Gateway],
        context: { input: ReadInput, system: { now: String } }
      };
      action "Write" appliesTo {
        principal: [OAuthUser],
        resource: [Gateway],
        context: { input: WriteInput }
      };
      action "Login" appliesTo {
        principal: [OAuthUser],
        resource: [Gateway],
        context: { input: { user: String } }
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

fn lower(src: &str) -> LoweredPolicySet {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .unwrap();
    LoweredPolicySet::from_str(src, &service, &schema)
        .expect("precondition: source must parse and lower successfully")
}

fn lower_with_providers(src: &str, providers_json: &str) -> LoweredPolicySet {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
    let decls = ProviderDeclarations::from_json(providers_json).unwrap();
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .providers(decls)
        .build()
        .unwrap();
    LoweredPolicySet::from_str(src, &service, &schema)
        .expect("precondition: source must parse and lower successfully")
}

fn validate_errors(lowered: &LoweredPolicySet) -> Vec<String> {
    let result = Validator::new().validate(lowered);
    result.validation_errors().map(|e| format!("{e}")).collect()
}

fn validate_errors_raw(lowered: &LoweredPolicySet) -> Vec<ValidationError> {
    Validator::new()
        .validate(lowered)
        .validation_errors()
        .cloned()
        .collect()
}

use dogwood_language::ValidationError;

fn assert_has_error(errors: &[String], substring: &str) {
    assert!(
        errors.iter().any(|e| e.contains(substring)),
        "expected an error containing {:?}, got:\n{}",
        substring,
        errors.join("\n")
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Cedar schema validation — type mismatches and unknown attributes
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn cedar_type_mismatch_long_vs_string() {
    // context.input.amount is Long, comparing to a String
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when { context.input.amount < "fifty" };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert!(
        !errors.is_empty(),
        "type mismatch should produce a validation error"
    );
}

#[test]
fn cedar_unknown_attribute_on_context() {
    // context.input.nonexistent is not declared on Read's input
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when { context.input.nonexistent == "x" };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert!(
        !errors.is_empty(),
        "unknown attribute should produce a validation error"
    );
    assert_has_error(&errors, "nonexistent");
}

#[test]
fn cedar_unknown_nested_attribute() {
    // context.input.user is a String, not a record — .name is invalid
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when { context.input.user.name == "x" };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert!(!errors.is_empty(), "nested attr on non-record should error");
}

#[test]
fn cedar_wrong_action_in_scope() {
    // Action "Delete" doesn't exist in the schema
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Delete", resource)
          when { true };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert!(!errors.is_empty(), "undeclared action should produce error");
}

#[test]
fn cedar_attribute_from_wrong_action() {
    // Write doesn't have context.input.amount (that's Read's field)
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Write", resource)
          when { context.input.amount > 10 };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert!(
        !errors.is_empty(),
        "Read's field on Write scope should error"
    );
    assert_has_error(&errors, "amount");
}

// ═══════════════════════════════════════════════════════════════════════
// Temporal dialect — entity types
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn temporal_unknown_entity_type() {
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when temporal {
            formerly within 1h Drupe::Action::"Login"::request{ input.user: Drupe::FakeEntity::"x" }
          };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert_has_error(&errors, "unknown entity type");
}

// ═══════════════════════════════════════════════════════════════════════
// Temporal dialect — context field resolution
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn temporal_context_field_not_on_action() {
    // context.input.stock exists on Read but not on Login
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Login", resource)
          when temporal {
            formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.stock }
          };
    "#,
    );
    let errors = validate_errors(&lowered);
    // Should flag context.input.stock as not on Login's context
    assert!(
        !errors.is_empty(),
        "referencing Read's field from Login scope should error"
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Temporal dialect — timepoint dependence
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn temporal_degenerate_condition_no_tp_variation() {
    // A temporal body that doesn't vary with timepoint — it's always the same
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when temporal { context.input.user == "admin" };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert_has_error(&errors, "does not vary");
}

// ═══════════════════════════════════════════════════════════════════════
// Temporal dialect — type checking
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn temporal_numeric_comparison_with_string() {
    // Comparing a string field with a numeric operator
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when temporal {
            formerly within 1h Drupe::Action::"Read"::request{ input.amount: context.input.amount }
            && context.input.user > 42
          };
    "#,
    );
    let errors = validate_errors(&lowered);
    // context.input.user is String, 42 is int — numeric comparison should fail
    assert!(!errors.is_empty(), "String > int should produce type error");
}

// ═══════════════════════════════════════════════════════════════════════
// Provider dialect — undeclared provider
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn provider_undeclared() {
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when { Unknown::Check(context.input.user) == "ok" };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert_has_error(&errors, "not present in");
}

// ═══════════════════════════════════════════════════════════════════════
// Provider dialect — argument count mismatch
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn provider_wrong_arg_count() {
    let providers = r#"{
        "availableProviders": {
            "Risk::Score": {
                "argumentTypes": [
                    { "paramType": "string" }
                ],
                "outputType": { "paramType": "string" }
            }
        }
    }"#;
    let lowered = lower_with_providers(
        r#"
            permit(principal, action == Drupe::Action::"Read", resource)
              when { Risk::Score(context.input.user, context.input.stock) == "ok" };
        "#,
        providers,
    );
    let errors = validate_errors(&lowered);
    assert_has_error(&errors, "expects 1 argument(s) but got 2");
}

// ═══════════════════════════════════════════════════════════════════════
// Provider dialect — argument type mismatch
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn provider_wrong_arg_type() {
    let providers = r#"{
        "availableProviders": {
            "Risk::Score": {
                "argumentTypes": [
                    { "paramType": "string" }
                ],
                "outputType": { "paramType": "string" }
            }
        }
    }"#;
    let lowered = lower_with_providers(
        r#"
            permit(principal, action == Drupe::Action::"Read", resource)
              when { Risk::Score(42) == "ok" };
        "#,
        providers,
    );
    let errors = validate_errors(&lowered);
    assert_has_error(&errors, "does not match");
}

// ═══════════════════════════════════════════════════════════════════════
// Validator produces NO errors for valid policies (sanity check)
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn valid_cedar_policy_passes_validation() {
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when { context.input.amount < 100 };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert!(errors.is_empty(), "valid policy should pass: {errors:?}");
}

#[test]
fn valid_temporal_policy_passes_validation() {
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when temporal {
            formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }
          };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert!(
        errors.is_empty(),
        "valid temporal policy should pass: {errors:?}"
    );
}

#[test]
fn valid_provider_policy_passes_validation() {
    let providers = r#"{
        "availableProviders": {
            "Risk::Score": {
                "argumentTypes": [
                    { "paramType": "string" }
                ],
                "outputType": { "paramType": "string" }
            }
        }
    }"#;
    let lowered = lower_with_providers(
        r#"
            permit(principal, action == Drupe::Action::"Read", resource)
              when { Risk::Score(context.input.user) == "safe" };
        "#,
        providers,
    );
    let errors = validate_errors(&lowered);
    assert!(
        errors.is_empty(),
        "valid provider policy should pass: {errors:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Span accuracy — verify errors point at the right source location
// ═══════════════════════════════════════════════════════════════════════

use miette::SourceSpan;

/// Extract the span from a ValidationError (both variants carry one).
fn error_span(e: &ValidationError) -> SourceSpan {
    match e {
        ValidationError::Cedar { span, .. } => *span,
        ValidationError::Extension { span, .. } => *span,
        _ => SourceSpan::new(0.into(), 1),
    }
}

/// Extract the source text a span underlines.
fn spanned_text(src: &str, span: SourceSpan) -> &str {
    let start = span.offset();
    let end = start + span.len();
    &src[start..end.min(src.len())]
}

#[test]
fn span_points_at_unknown_attribute() {
    let src = r#"permit(principal, action == Drupe::Action::"Read", resource) when { context.input.nonexistent == "x" };"#;
    let lowered = lower(src);
    let errors = validate_errors_raw(&lowered);
    assert!(!errors.is_empty());
    let span = error_span(&errors[0]);
    let text = spanned_text(src, span);
    // The span should underline something containing "nonexistent"
    assert!(
        text.contains("nonexistent"),
        "span should point at the unknown attribute, got: {:?} (offset={}, len={})",
        text,
        span.offset(),
        span.len(),
    );
}

#[test]
fn span_points_at_type_mismatch_expression() {
    let src = r#"permit(principal, action == Drupe::Action::"Read", resource) when { context.input.amount < "fifty" };"#;
    let lowered = lower(src);
    let errors = validate_errors_raw(&lowered);
    assert!(!errors.is_empty());
    let span = error_span(&errors[0]);
    let text = spanned_text(src, span);
    // The span should point at something in the comparison, not byte 0
    assert!(
        span.offset() > 0,
        "span should not be the START_SPAN fallback (offset 0)"
    );
    assert!(
        text.contains("fifty") || text.contains("amount") || text.contains("<"),
        "span should point at the comparison area, got: {:?}",
        text,
    );
}

#[test]
fn temporal_error_span_is_not_at_byte_zero() {
    let src = r#"permit(principal, action == Drupe::Action::"Read", resource) when temporal { context.input.user == "admin" };"#;
    let lowered = lower(src);
    let errors = validate_errors_raw(&lowered);
    assert!(!errors.is_empty(), "degenerate temporal should error");
    let span = error_span(&errors[0]);
    // Temporal errors should point inside the temporal block, not at byte 0
    assert!(
        span.offset() > 50,
        "temporal span should be inside the temporal block (offset={}), not at source start",
        span.offset()
    );
}

#[test]
fn provider_error_span_is_not_at_byte_zero() {
    let src = r#"permit(principal, action == Drupe::Action::"Read", resource) when { Unknown::Check(context.input.x) == "ok" };"#;
    let lowered = lower(src);
    let errors = validate_errors_raw(&lowered);
    assert!(!errors.is_empty());
    let span = error_span(&errors[0]);
    // Provider error should point near the invocation, not byte 0
    assert!(
        span.offset() > 50,
        "provider span should point at invocation (offset={}), not at source start",
        span.offset()
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Provider method chain validation (Item 4)
// ═══════════════════════════════════════════════════════════════════════

const PROVIDER_WITH_METHODS: &str = r#"{
    "availableProviders": {
        "Content::Risk": {
            "argumentTypes": [
                { "paramType": "string" }
            ],
            "outputType": { "paramType": "record", "fields": { "score": { "paramType": "decimal" } }, "required": ["score"] },
            "availableMethods": {
                "classify": {
                    "argumentTypes": [],
                    "outputType": { "paramType": "string" }
                }
            }
        }
    }
}"#;

#[test]
fn provider_unknown_method() {
    let lowered = lower_with_providers(
        r#"
            permit(principal, action == Drupe::Action::"Read", resource)
              when { Content::Risk(context.input.user).nonexistent() == "ok" };
        "#,
        PROVIDER_WITH_METHODS,
    );
    let errors = validate_errors(&lowered);
    assert_has_error(&errors, "nonexistent");
}

#[test]
fn provider_valid_method_passes() {
    let lowered = lower_with_providers(
        r#"
            permit(principal, action == Drupe::Action::"Read", resource)
              when { Content::Risk(context.input.user).classify() == "safe" };
        "#,
        PROVIDER_WITH_METHODS,
    );
    let errors = validate_errors(&lowered);
    assert!(errors.is_empty(), "valid method should pass: {errors:?}");
}

// ═══════════════════════════════════════════════════════════════════════
// Temporal type-checking depth (Item 5)
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn temporal_equality_entity_vs_string() {
    // Comparing an entity literal with a String field
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when temporal {
            formerly within 1h Drupe::Action::"Login"::request{ input.user: Drupe::OAuthUser::"alice" }
          };
    "#,
    );
    let errors = validate_errors(&lowered);
    // input.user is String, but we're passing an entity ref — type mismatch
    assert!(
        !errors.is_empty(),
        "entity vs string should produce type error: {errors:?}"
    );
}

#[test]
fn temporal_equality_long_vs_string() {
    // input.user is String, comparing with a Long literal
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when temporal {
            formerly within 1h Drupe::Action::"Read"::request{ input.user: 42 }
          };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert!(
        !errors.is_empty(),
        "Long vs String should produce type error: {errors:?}"
    );
}

#[test]
fn temporal_comparison_string_with_ordering() {
    // Ordering comparisons (< > <= >=) require numeric operands.
    // context.input.user is String, context.input.amount is Long — comparing them
    // with > should fail.
    let lowered = lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when temporal {
            formerly within 1h Drupe::Action::"Read"::request{ input.amount: context.input.amount }
            && context.input.user > context.input.amount
          };
    "#,
    );
    let errors = validate_errors(&lowered);
    assert!(
        !errors.is_empty(),
        "String > Long should produce type error"
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Cross-stage confusion (Item 8) — parse errors must NOT reach validator
// ═══════════════════════════════════════════════════════════════════════
// If something is a parse error, the pipeline must reject it at parse time.
// The validator must never be reachable for these inputs.

fn try_lower(src: &str) -> Result<LoweredPolicySet, dogwood_language::Error> {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .unwrap();
    LoweredPolicySet::from_str(src, &service, &schema)
}

#[test]
fn parse_error_cannot_reach_validator_missing_semicolon() {
    let result = try_lower("permit(principal, action, resource) when { true }");
    // Must fail at parse — not succeed and then fail at validation
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        dogwood_language::Error::Parse(_)
    ));
}

#[test]
fn parse_error_cannot_reach_validator_bad_expression() {
    let result = try_lower("permit(principal, action, resource) when { == };");
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        dogwood_language::Error::Parse(_)
    ));
}

#[test]
fn macro_error_cannot_reach_validator_undefined_call() {
    let result = try_lower(
        r#"
        permit(principal, action == Drupe::Action::"Read", resource)
          when { bogus_macro() };
    "#,
    );
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        dogwood_language::Error::Macro(_)
    ));
}
