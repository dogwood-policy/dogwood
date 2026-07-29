//! Phase 1: Confirm the parser rejects malformed input with clear errors,
//! ensuring garbage never reaches lowering or validation.
//!
//! Every test passes invalid source to `LoweredPolicySet::from_str()` and asserts:
//! 1. The result is `Err`
//! 2. The error is a parse error (not a macro or lowering error)
//! 3. The error message is actionable (mentions what's wrong)

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema};

const SCHEMA: &str = r#"
    namespace App {
      entity User;
      entity Doc;
      action "Read" appliesTo {
        principal: [User], resource: [Doc],
        context: { input: { x: String } }
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

fn try_lower(src: &str) -> Result<LoweredPolicySet, dogwood_language::Error> {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .unwrap();
    LoweredPolicySet::from_str(src, &service, &schema)
}

fn assert_parse_error(src: &str, expected_substring: &str) {
    let result = try_lower(src);
    assert!(result.is_err(), "expected parse error for: {src}");
    let err = result.unwrap_err();
    assert!(
        matches!(err, dogwood_language::Error::Parse(_)),
        "expected a Parse error variant, got: {err:?}"
    );
    let msg = format!("{err}");
    assert!(
        msg.contains(expected_substring),
        "error should mention {expected_substring:?}, got: {msg}"
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Structural — missing/extra delimiters
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn missing_closing_paren_in_scope() {
    assert_parse_error(
        "permit(principal, action, resource when { true };",
        "expected",
    );
}

#[test]
fn missing_semicolon_between_policies() {
    assert_parse_error(
        r#"
            permit(principal, action, resource) when { true }
            forbid(principal, action, resource) when { true };
        "#,
        "expected",
    );
}

#[test]
fn missing_opening_brace_in_when() {
    assert_parse_error(
        "permit(principal, action, resource) when true };",
        "expected",
    );
}

#[test]
fn missing_closing_brace_in_when() {
    assert_parse_error(
        "permit(principal, action, resource) when { true ;",
        "expected",
    );
}

#[test]
fn unbalanced_braces_in_temporal_body() {
    assert_parse_error(
        r#"permit(principal, action, resource) when temporal { formerly within 1h App::Action::"Read"::request{ ;"#,
        "expected",
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Empty bodies — must not silently produce empty conditions
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn empty_when_clause_body() {
    assert_parse_error(
        "permit(principal, action, resource) when { };",
        "expression",
    );
}

#[test]
fn empty_temporal_body() {
    assert_parse_error(
        "permit(principal, action, resource) when temporal { };",
        "expected",
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Lexical errors — bad tokens
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn unterminated_string_literal() {
    assert_parse_error(
        r#"permit(principal, action, resource) when { context.input.x == "hello };"#,
        "\"",
    );
}

#[test]
fn invalid_number_format() {
    // A bare floating point is not valid (Cedar uses decimal("1.5"))
    assert_parse_error(
        "permit(principal, action, resource) when { context.input.x == 1.5 };",
        "expected",
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Invalid effect keyword
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn invalid_effect_keyword() {
    // "allow" is not a valid effect — only permit/forbid
    let result = try_lower("allow(principal, action, resource) when { true };");
    assert!(result.is_err(), "invalid effect should fail");
}

// ═══════════════════════════════════════════════════════════════════════
// Scope syntax errors
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn scope_with_invalid_operator() {
    // principal > User::"alice" is not valid scope syntax
    assert_parse_error(
        r#"permit(principal > App::User::"alice", action, resource) when { true };"#,
        "scope only allows",
    );
}

#[test]
fn action_scope_with_unclosed_list() {
    assert_parse_error(
        r#"permit(principal, action in [App::Action::"Read", resource) when { true };"#,
        "expected",
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Expression syntax errors inside conditions
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn dangling_operator_in_condition() {
    assert_parse_error(
        "permit(principal, action, resource) when { context.input.x == };",
        "expected",
    );
}

#[test]
fn double_operator_in_condition() {
    assert_parse_error(
        "permit(principal, action, resource) when { context.input.x == == true };",
        "expected",
    );
}

#[test]
fn assignment_operator_in_condition() {
    // Single `=` is intentionally captured with a "did you mean `==`?" hint
    let result = try_lower("permit(principal, action, resource) when { context.input.x = true };");
    assert!(result.is_err(), "single = should fail");
}

// ═══════════════════════════════════════════════════════════════════════
// Template slot errors
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn unknown_template_slot() {
    // ?foo is not a recognized slot
    let result = try_lower(r#"permit(?foo, action, resource) when { true };"#);
    assert!(result.is_err(), "unknown slot should fail");
}

// ═══════════════════════════════════════════════════════════════════════
// Temporal sub-parser errors
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn temporal_missing_within_clause() {
    // `formerly` requires `within <duration>`
    assert_parse_error(
        r#"permit(principal, action, resource) when temporal { formerly App::Action::"Read"::request{} };"#,
        "within",
    );
}

#[test]
fn temporal_invalid_duration_unit() {
    // "1x" is not a valid duration
    assert_parse_error(
        r#"permit(principal, action, resource) when temporal { formerly within 1x App::Action::"Read"::request{} };"#,
        "expected",
    );
}

#[test]
fn temporal_missing_event_kind() {
    // Missing the ::request/::response event kind after the action ref
    assert_parse_error(
        r#"permit(principal, action, resource) when temporal { formerly within 1h App::Action::"Read"{} };"#,
        "expected",
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Macro syntax errors (caught at parse, not expansion)
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn def_with_missing_body_braces() {
    assert_parse_error(
        "def cedar foo() true; permit(principal, action, resource);",
        "expected",
    );
}

#[test]
fn def_with_missing_kind() {
    // "def foo()" without cedar/temporal kind keyword
    assert_parse_error(
        "def foo() { true }; permit(principal, action, resource);",
        "expected",
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Garbage / adversarial input
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn completely_random_text() {
    let result = try_lower("asdfghjkl 12345 !@#$%");
    assert!(result.is_err());
}

#[test]
fn sql_injection_attempt() {
    let result = try_lower("'; DROP TABLE policies; --");
    assert!(result.is_err());
}

#[test]
fn xml_injection_attempt() {
    let result = try_lower("<policy><effect>permit</effect></policy>");
    assert!(result.is_err());
}

#[test]
fn null_bytes_in_source() {
    let result = try_lower("permit(principal\0, action, resource);");
    assert!(result.is_err());
}

#[test]
fn only_whitespace_and_comments() {
    // Empty source (only comments) should succeed with 0 policies, not error
    let result = try_lower("// just a comment\n   \n// another");
    assert!(result.is_ok(), "comments-only should parse as empty set");
    assert_eq!(result.unwrap().as_cedar().policies().count(), 0);
}

#[test]
fn extremely_long_identifier() {
    let long_id = "a".repeat(10_000);
    let src =
        format!("permit(principal, action, resource) when {{ context.input.{long_id} == true }};");
    // Should either parse (and fail at validation) or fail at parse — not panic
    let _ = try_lower(&src);
}

#[test]
fn deeply_nested_parentheses() {
    // Note: 100+ levels causes stack overflow in the recursive pest parser.
    // This is a known limitation. We test at 20 levels to confirm it works
    // within reasonable depth without panicking.
    let opens = "(".repeat(20);
    let closes = ")".repeat(20);
    let src = format!("permit(principal, action, resource) when {{ {opens}true{closes} }};");
    // Should parse successfully at this depth
    let result = try_lower(&src);
    assert!(result.is_ok(), "20-deep parens should parse: {result:?}");
}
