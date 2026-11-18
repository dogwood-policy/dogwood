//! Lowering defects that a second implementation of the frontend found, by
//! computing what the crate computes and comparing the results with the
//! formal specification (`dogwood-lean`): a name the event-schema derivation
//! resolved differently from Cedar, a fresh name an authored binder could
//! capture, schema text synthesized for provider outputs that Cedar reads
//! differently or not at all, a schema that `PolicySet.Valid` rejects, error
//! spans in the wrong place, and the reserved names of the lowered context.
//!
//! Each test failed before its fix (the self-referential common type crashed
//! the process with a stack overflow instead).

use dogwood_language::{
    Authorizer, Decision, Error, LoweredPolicySet, PolicySchema, ProviderDeclarations,
    ServiceSchema, ValidationError, ValidationResult, Validator, parse_trace,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type LoginInput = { user: String };
  type ReadInput = { user: String, note?: String };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: LoginInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

fn service(providers: Option<&str>) -> ServiceSchema {
    let mut builder = ServiceSchema::builder();
    if let Some(json) = providers {
        builder = builder.providers(ProviderDeclarations::from_json(json).expect("providers load"));
    }
    builder.build().expect("service schema builds")
}

fn lower_with(policy: &str, schema: &str, providers: Option<&str>) -> Result<LoweredPolicySet, Error> {
    let schema = PolicySchema::from_cedarschema_str(schema).expect("action schema builds");
    LoweredPolicySet::from_str(policy, &service(providers), &schema)
}

fn lower_err(policy: &str, schema: &str, providers: Option<&str>) -> Error {
    match lower_with(policy, schema, providers) {
        Ok(_) => panic!("expected lowering to fail"),
        Err(e) => e,
    }
}

fn validate_with(policy: &str, schema: &str, providers: Option<&str>) -> ValidationResult {
    let policies = lower_with(policy, schema, providers).expect("policy lowers");
    Validator::new().validate(&policies)
}

fn messages(r: &ValidationResult) -> Vec<String> {
    r.validation_errors().map(|e| e.to_string()).collect()
}

#[track_caller]
fn assert_passes(r: &ValidationResult) {
    assert!(r.validation_passed(), "expected no errors, got {:?}", messages(r));
}

#[track_caller]
fn assert_code(r: &ValidationResult, code: &str) {
    assert!(
        r.validation_errors()
            .any(|e| matches!(e, ValidationError::Extension { code: c, .. } if *c == code)),
        "expected a finding with code `{code}`, got {:?}",
        messages(r)
    );
}

/// A login by the current request's user.
const LOGIN: &str = r#"formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }"#;

fn read_rule(leaf: &str) -> String {
    format!(r#"permit (principal, action == Drupe::Action::"Read", resource) when temporal {{ {leaf} }};"#)
}

/// The leaf paths of the event `action`::`kind`.
fn leaf_paths(lowered: &LoweredPolicySet, action: &str, kind: &str) -> Vec<String> {
    let sig = lowered
        .event_signatures()
        .find(|s| s.action() == action && s.kind() == kind)
        .unwrap_or_else(|| panic!("no signature for {action}::{kind}"));
    let mut paths: Vec<String> = sig.fields().map(|f| f.path().join(".")).collect();
    paths.sort();
    paths
}

// ─── Event-schema derivation resolves names as Cedar does ────────────

#[test]
fn a_bare_type_name_in_a_namespace_also_resolves_in_the_root_namespace() {
    // Cedar resolves the bare `In` of `Drupe` to `Drupe::In` if declared, and
    // else to the root namespace's `In`. The derived `input` group used to be
    // empty, so the event had no `input.user` field.
    let schema = r#"
type In = { user: String };
namespace Drupe {
  entity Gateway;
  entity OAuthUser;
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: In }
  };
}
"#;
    let policy = format!(
        r#"permit (principal, action == Drupe::Action::"Login", resource) when temporal {{ {LOGIN} }};"#
    );
    let lowered = lower_with(&policy, schema, None).expect("policy lowers");
    assert!(
        leaf_paths(&lowered, "Login", "request").contains(&"input.user".to_string()),
        "{:?}",
        leaf_paths(&lowered, "Login", "request")
    );
    assert_passes(&Validator::new().validate(&lowered));
    // (A namespace may not declare a type of the same name: Cedar rejects the
    // shadowing.)
}

// ─── A schema the specification's well-formedness rejects ────────────

#[test]
fn an_entity_type_whose_parent_is_an_enumerated_entity_type_is_rejected() {
    // Cedar accepts it; cedar-lean's `Schema.validateWellFormed`, which
    // `PolicySet.Valid` requires, does not.
    let schema = r#"
namespace Drupe {
  entity Application enum ["TinyTodo"];
  entity Team in [Application];
  entity User in [Team];
  entity Gateway;
  action "Read" appliesTo { principal: [User], resource: [Gateway], context: {} };
}
"#;
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource);"#;
    let r = validate_with(policy, schema, None);
    assert_code(&r, "schema");
    let errors = messages(&r);
    assert!(
        errors.iter().any(|m| m.contains("`Drupe::Application`")
            && m.contains("`Drupe::Team`")
            && m.contains("`Drupe::User`")),
        "{errors:?}"
    );
    // Even a policy set without policies is checked.
    let r = validate_with("", schema, None);
    assert_code(&r, "schema");
    // A standard parent is fine.
    let standard = schema.replace(r#"enum ["TinyTodo"]"#, "");
    assert_passes(&validate_with(policy, &standard, None));
}

// ─── Relativization's fresh names ────────────────────────────────────

fn decisions(policy: &str, log: &str) -> Vec<Option<Decision>> {
    let lowered = lower_with(policy, SCHEMA, None).expect("policy lowers");
    assert_passes(&Validator::new().validate(&lowered));
    let mut a = Authorizer::new(lowered);
    parse_trace(log)
        .expect("trace parses")
        .iter()
        .map(|e| a.is_authorized(e).map(|r| r.decision()))
        .collect()
}

fn event(ts: u32, action: &str) -> String {
    format!(
        r#"@{ts} scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: {{ user: "alice" }}) Drupe::Action::"{action}"::request(input: {{ user: "alice" }}, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw1", requestId: "r{ts}")"#
    )
}

#[test]
fn an_authored_binder_named_like_a_relativization_name_is_not_captured() {
    // Relativization (for the default schema's universal `callerPrincipal`
    // pin) rewrites `previous` with binders of its own. They used to be named
    // `__pin_ti0`, … whatever the leaf: here the rewrite's `__pin_ti0` captured
    // the authored one inside the `previous`, and the `Read` was denied.
    let leaf = |x: &str| {
        format!(
            r#"exists ({x}: Timepoint). (
                formerly within 1h (Drupe::Action::"Login"::request{{ input.user: context.input.user }} && tp({x}))
                && previous within 1h (formerly within 1h (Drupe::Action::"Login"::request{{ input.user: context.input.user }} && tp({x}))))"#
        )
    };
    let log = [event(1000, "Login"), event(1010, "Read")].join("\n");
    // The `Login` request is a decision too, which no rule permits.
    let expected = vec![Some(Decision::Deny), Some(Decision::Allow)];
    assert_eq!(decisions(&read_rule(&leaf("x")), &log), expected);
    for name in ["__pin_ti0", "__pin_tj1", "__pin_"] {
        assert_eq!(decisions(&read_rule(&leaf(name)), &log), expected, "binder `{name}`");
    }
}

// ─── Array constants under arithmetic ────────────────────────────────

// EXPERIMENTAL-ARITHMETIC: a compound operand parses only with the feature on.
#[cfg(feature = "experimental-arithmetic")]
#[test]
fn an_array_constant_in_an_aggregate_under_any_arithmetic_operator_fails_lowering() {
    for op in ["+", "-", "*"] {
        let policy = read_rule(&format!(
            r#"(count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{{ input.user: ["a", "b"] }} && tp(t)))) {op} 2 >= 1"#,
        ));
        let err = lower_err(&policy, SCHEMA, None);
        assert!(err.to_string().contains("array constants"), "`{op}`: {err}");
        // Nested one level deeper, on the right.
        let policy = read_rule(&format!(
            r#"1 {op} (2 {op} (count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{{ input.user: ["a"] }} && tp(t))))) >= 1"#,
        ));
        let err = lower_err(&policy, SCHEMA, None);
        assert!(err.to_string().contains("array constants"), "`{op}`: {err}");
    }
}

// ─── Error spans ─────────────────────────────────────────────────────

/// The text a macro error's span covers in its source.
fn macro_error_text(policy: &str) -> String {
    let err = lower_err(policy, SCHEMA, None);
    let Error::Macro(m) = &err else {
        panic!("expected a macro error, got {err}");
    };
    let loc = m.location();
    assert_eq!(loc.source(), policy, "the error renders against the policy");
    let span = loc.span();
    policy[span.offset()..span.offset() + span.len()].to_string()
}

#[test]
fn an_error_inside_a_temporal_block_points_into_the_block() {
    // The span used to be relative to the block's body: `0..12`.
    let policy = r#"def cedar c(?p) { ?p == principal };
permit (principal, action == Drupe::Action::"Read", resource)
when temporal { c(principal) };"#;
    assert_eq!(macro_error_text(policy), "c(principal)");
}

#[test]
fn an_error_inside_a_def_body_points_into_the_body() {
    // The span used to be relative to the body: `0..9`.
    let policy = r#"def cedar inner(?x) { ?x };
def cedar outer(?y) { inner(?y) };
permit (principal, action == Drupe::Action::"Read", resource) when { outer(true) };"#;
    assert_eq!(macro_error_text(policy), "inner(?y)");
    // A value body has no span of its own: the error points at the definition.
    let policy = r#"def temporal v() { (count for ($t: Timepoint). where tp($t)) + ?q };
permit (principal, action == Drupe::Action::"Read", resource);"#;
    assert_eq!(
        macro_error_text(policy),
        "def temporal v() { (count for ($t: Timepoint). where tp($t)) + ?q };"
    );
}

#[test]
fn a_stray_parameter_in_a_comparison_operand_points_at_the_comparison() {
    // The span used to be `0..0`.
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource)
when temporal { formerly within 1h Drupe::Action::"Login"::request{} && ?x > 1 };"#;
    assert_eq!(macro_error_text(policy).trim_end(), "?x > 1");
}

// ─── The message of the binding-equality demand ──────────────────────

#[test]
fn a_binding_equality_with_an_arithmetic_value_side_names_it_so() {
    let policy = read_rule(
        r#"exists (x: Long). exists (y: Long). (x == y + 1
            && formerly within 1h Drupe::Action::"Login"::request{ input.count: y })"#,
    );
    let message = lower_err(&policy, SCHEMA, None).to_string();
    assert!(message.contains("the equality binding `x` reads `y`"), "{message}");
    assert!(!message.contains("aggregate"), "{message}");
}

// ─── Provider outputs in the synthesized schema text ─────────────────

const DECIMAL_PROVIDERS: &str = r#"{ "availableProviders": { "Risk::Score": {
  "outputType": { "paramType": "record",
    "fields": { "score": { "paramType": "decimal" } }, "required": ["score"] },
  "implementation": { "kind": "rhai", "script": "fn evaluate() { #{ score: \"0.75\" } }" }
} } }"#;

#[test]
fn a_namespace_type_named_decimal_does_not_capture_a_provider_decimal() {
    let schema = SCHEMA.replace("entity Gateway;", "type decimal = { foo: Long };\n  entity Gateway;");
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource)
when { Risk::Score().score.greaterThan(decimal("0.5")) };"#;
    assert_passes(&validate_with(policy, &schema, Some(DECIMAL_PROVIDERS)));
}

const FIELD_NAME_PROVIDERS: &str = r#"{ "availableProviders": { "Http::Head": {
  "outputType": { "paramType": "record",
    "fields": { "content-type": { "paramType": "string" }, "in": { "paramType": "long" },
                "say \"hi\"": { "paramType": "bool" } },
    "required": ["content-type", "in"] },
  "implementation": { "kind": "rhai", "script": "fn evaluate() { #{} }" }
} } }"#;

#[test]
fn a_provider_record_field_that_is_not_an_identifier_lowers() {
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource)
when { Http::Head()["content-type"] == "text/plain" && Http::Head()["in"] > 1
       && !(Http::Head() has "say \"hi\"") };"#;
    assert_passes(&validate_with(policy, SCHEMA, Some(FIELD_NAME_PROVIDERS)));
}

// ─── A self-referential common type behind a context reference ───────

#[test]
fn a_self_referential_common_type_behind_a_context_reference_fails_lowering() {
    // Derivation reads only `input`; inlining the context used to recurse
    // through `meta` until the stack overflowed. Cedar rejects the cycle.
    let schema = r#"
namespace Drupe {
  type A = { x: A };
  type Ctx = { input: { user: String }, meta: A };
  entity Gateway;
  entity OAuthUser;
  action "Login" appliesTo { principal: [OAuthUser], resource: [Gateway], context: Ctx };
}
"#;
    let policy = format!(
        r#"permit (principal, action == Drupe::Action::"Login", resource) when temporal {{ {LOGIN} }};"#
    );
    let err = lower_err(&policy, schema, None);
    assert!(err.to_string().contains("cycl"), "{err}");
}

// ─── The names lowering adds to the context ──────────────────────────

#[test]
fn the_context_names_lowering_reserves_are_reserved() {
    // A read of a hoisted name, or of the whole context, by the Cedar part.
    for condition in ["context.policy_0__temporal_0", "context == {}"] {
        let policy = format!(
            r#"permit (principal, action == Drupe::Action::"Read", resource)
               when {{ {condition} }} when temporal {{ {LOGIN} }};"#
        );
        assert_code(&validate_with(&policy, SCHEMA, None), "context");
    }
    // A declared attribute with a hoisted name, whatever its type, on an
    // action the leaf targets (`Read`) or on another (`Login`).
    for (input, ty) in [("ReadInput", "Long"), ("ReadInput", "Bool"), ("LoginInput", "Bool")] {
        let schema = SCHEMA.replace(
            &format!("context: {{ input: {input} }}"),
            &format!("context: {{ input: {input}, policy_0__temporal_0: {ty} }}"),
        );
        let err = lower_err(&read_rule(LOGIN), &schema, None);
        assert!(err.to_string().contains("policy_0__temporal_0"), "{input}, {ty}: {err}");
    }
    // A declared `providers` record, on an action a provider leaf targets.
    let schema = SCHEMA.replace(
        "context: { input: ReadInput }",
        "context: { input: ReadInput, providers: { legacy: String } }",
    );
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource)
when { Risk::Score().score.greaterThan(decimal("0.5")) };"#;
    let err = lower_err(policy, &schema, Some(DECIMAL_PROVIDERS));
    assert!(err.to_string().contains("`providers`"), "{err}");
}
