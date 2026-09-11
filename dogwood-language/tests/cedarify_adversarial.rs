//! Adversarial and edge-case tests for the cedarify lowering pipeline.
//!
//! These exercise error paths, weird inputs, and boundary conditions through
//! the public API (`LoweredPolicySet::from_str`). The goal is to break things:
//! malformed provider arguments, deeply nested expressions, empty schemas,
//! unicode edge cases, and inputs that are syntactically valid but
//! semantically degenerate.

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema, Validator};

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

const ESCAPED_ACTION_SCHEMA: &str = r#"
    namespace Escaped {
      entity User;
      entity Doc;
      action "\u{e}" appliesTo {
        principal: [User], resource: [Doc],
        context: { input: { x: String } }
      };
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

fn assert_escaped_action_scope_lowers_and_validates(scope: &str) {
    let schema =
        PolicySchema::from_cedarschema_str(ESCAPED_ACTION_SCHEMA).expect("schema should parse");
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("service schema should build");
    let src = format!(
        r#"permit(principal, {scope}, resource)
             when temporal {{
               formerly within 1h Escaped::Action::"Login"::request{{}}
             }};"#
    );

    let lowered = LoweredPolicySet::from_str(&src, &service, &schema)
        .unwrap_or_else(|error| panic!("escaped action scope should lower: {error:?}"));
    let result = Validator::new().validate(&lowered);
    let errors: Vec<_> = result
        .validation_errors()
        .map(|error| error.to_string())
        .collect();
    assert!(
        errors.is_empty(),
        "escaped action scope should validate cleanly: {errors:#?}"
    );
}

#[test]
fn temporal_namespaced_escaped_action_scope_lowers_and_validates() {
    assert_escaped_action_scope_lowers_and_validates(r#"action == Escaped::Action::"\u{e}""#);
}

#[test]
fn temporal_action_list_with_escaped_id_lowers_and_validates() {
    assert_escaped_action_scope_lowers_and_validates(
        r#"action in [Escaped::Action::"\u{e}", Escaped::Action::"Read"]"#,
    );
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

/// Lower `@doc("<inner>") permit …` and return the decoded `doc` annotation
/// value carried onto the Cedar policy, or the lowering error.
fn annotation_doc_value(inner: &str) -> Result<Option<String>, dogwood_language::Error> {
    let policy =
        format!("@doc(\"{inner}\")\npermit(principal, action == App::Action::\"Read\", resource);");
    let lowered = lower(&policy)?;
    Ok(lowered
        .as_cedar()
        .policies()
        .next()
        .expect("one lowered policy")
        .annotation("doc")
        .map(str::to_string))
}

#[test]
fn annotation_values_decode_escapes_like_cedar() {
    // (annotation source between the quotes, expected decoded value). Every
    // escape family Cedar decodes must decode identically in an annotation
    // value — they all funnel through `decode_string` now, not `trim_matches`.
    let cases: &[(&str, &str)] = &[
        ("a\\\"b", "a\"b"),           // escaped quote
        ("a\\\\b", "a\\b"),           // escaped backslash
        ("a\\nb", "a\nb"),            // newline
        ("a\\tb", "a\tb"),            // tab
        ("a\\rb", "a\rb"),            // carriage return
        ("o\\'brien", "o'brien"),     // escaped apostrophe
        ("\\x41", "A"),               // hex byte escape (<= 0x7F)
        ("\\u{1_2_3_4}", "\u{1234}"), // \u{…} with interior underscore separators
        ("\\u{1F512}", "\u{1F512}"),  // astral codepoint
        ("plain", "plain"),           // control: no escape
        ("", ""),                     // empty value: `@doc("")` decodes to ""
    ];
    for (inner, expected) in cases {
        assert_eq!(
            annotation_doc_value(inner).unwrap_or_else(|e| panic!("`{inner}` should lower: {e:?}")),
            Some(expected.to_string()),
            "annotation `{inner}` must decode to {expected:?}"
        );
    }
}

#[test]
fn annotation_invalid_escapes_are_rejected() {
    // Escapes Cedar's `to_unescaped_string` rejects — an annotation value must
    // reject them at parse too (not silently keep them verbatim), matching
    // `decode_string` and the string-literal `expected_failures` cases.
    for inner in [
        "a\\zb",       // unknown escape
        "\\*",         // `\*` is valid only in a `like` pattern, not a string
        "\\u{_1234}",  // leading underscore in \u{…}
        "\\xFF",       // \x above 0x7F
        "\\u{}",       // empty \u{}
        "\\u{110000}", // codepoint above U+10FFFF
    ] {
        assert!(
            annotation_doc_value(inner).is_err(),
            "annotation `{inner}` must be rejected at parse"
        );
    }
}

/// Cross-reference the annotation decode against Cedar's **own** string decoder
/// (`to_unescaped_string`, the exact function `decode_string` funnels through)
/// rather than hardcoded expectations: for every form, the annotation path must
/// decode to *exactly* what Cedar decodes, and reject *exactly* where Cedar
/// rejects. The expected value is Cedar's, so this can't enshrine a wrong guess
/// about Cedar's behaviour — and it covers forms whose outcome is not obvious.
#[test]
fn annotation_decoding_matches_cedar_reference() {
    use cedar_policy_core::parser::unescape::to_unescaped_string;

    // Bodies (the text between the quotes) spanning valid and Cedar-invalid
    // escapes, including edge forms (leading/trailing `_`, surrogate, out-of-
    // range, `\x` boundary, `\0`).
    let bodies = [
        "",
        "plain",
        "a b",
        "o'brien",
        "café",
        "a\\\"b",
        "a\\\\b",
        "a\\nb",
        "a\\tb",
        "a\\rb",
        "a\\0b",
        "o\\'brien",
        "\\x41",
        "\\x7f",
        "\\u{1_2_3_4}",
        "\\u{1F512}",
        "\\u{12_34_}",
        "\\u{41}",
        // Cedar-invalid forms:
        "a\\zb",
        "\\*",
        "\\u{_1234}",
        "\\xFF",
        "\\u{}",
        "\\u{110000}",
        "\\u{d800}",
    ];
    for body in bodies {
        let cedar = to_unescaped_string(body).ok().map(|s| s.to_string());
        let dogwood = annotation_doc_value(body);
        match (&dogwood, &cedar) {
            (Ok(Some(v)), Some(exp)) => assert_eq!(
                v, exp,
                "annotation `{body}`: Dogwood decoded {v:?} but Cedar decodes {exp:?}"
            ),
            (Err(_), None) => { /* both reject — agree with Cedar */ }
            _ => {
                panic!("annotation `{body}`: Dogwood = {dogwood:?} but Cedar reference = {cedar:?}")
            }
        }
    }
}

#[test]
fn multiple_annotations_on_one_policy_decode_independently() {
    // Two escape-bearing annotations under different keys on the same policy:
    // each value must decode through the same unescaper on its own, with no
    // cross-contamination between keys and no last-writer-wins clobbering.
    let src = r#"
        @id("a\"b")
        @note("c\td")
        permit(principal, action == App::Action::"Read", resource);
    "#;
    let lowered = lower(src).expect("annotated policy should lower");
    let policy = lowered
        .as_cedar()
        .policies()
        .next()
        .expect("one lowered policy");
    assert_eq!(policy.annotation("id"), Some("a\"b"));
    assert_eq!(policy.annotation("note"), Some("c\td"));
}
