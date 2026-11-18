//! Temporal conditions do not support Cedar's extension types other than
//! `decimal` (`datetime`, `duration`, `ipaddr`): validation rejects a binder
//! declared with one, and a temporal term whose type is or holds one — a
//! comparison operand, a predicate argument, or a pin's request-side path —
//! as the formal specification's typing does (`dogwood-lean`,
//! `Temporal.Typing`, `CedarType.temporalSupported`).
//!
//! A schema may still declare such attributes and fields: a predicate that
//! does not constrain the field, or matches it with a wildcard, is valid, and
//! the Cedar part reads them as Cedar does. The validator used to type them in
//! temporal leaves, but the interpreter compared their values by their text,
//! so two spellings of one instant (`2026-01-01T00:00:00Z`,
//! `2026-01-01T00:00:00.000Z`) did not match.

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, ValidationResult,
    Validator,
};
const SCHEMA: &str = r#"
namespace Drupe {
  type LoginInput = { user: String, at: datetime, ttl: duration, addr: ipaddr, score: decimal };
  type ReadInput = {
    user: String, since: datetime, ttl: duration, addr: ipaddr, meta: { at: datetime },
    stamps: Set<datetime>
  };
  entity Gateway;
  entity OAuthUser = { joined: datetime };
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

/// An event schema that also declares an event-schema field of type
/// `datetime` on every response, outside the spliced `input`.
const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
}

event <A>::response {
    ...inputs(A),
    callerPrincipal: principalType(A),
    issuedAt: datetime,
}
"#;

fn lower(policy: &str, event_schema: Option<&str>) -> LoweredPolicySet {
    let mut builder = ServiceSchema::builder();
    if let Some(e) = event_schema {
        builder = builder.event_schema_str(e);
    }
    let service = builder.build().expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    LoweredPolicySet::from_str(policy, &service, &schema).expect("policy lowers")
}

fn validate(body: &str) -> ValidationResult {
    validate_with(body, None)
}

fn validate_with(body: &str, event_schema: Option<&str>) -> ValidationResult {
    let policy = format!(
        "permit (principal, action == Drupe::Action::\"Read\", resource)\nwhen temporal {{\n{body}\n}};\n"
    );
    Validator::new().validate(&lower(&policy, event_schema))
}

fn messages(r: &ValidationResult) -> Vec<String> {
    r.validation_errors().map(|e| e.to_string()).collect()
}

#[track_caller]
fn assert_passes(r: &ValidationResult) {
    assert!(
        r.validation_passed(),
        "expected no errors, got {:?}",
        messages(r)
    );
}

#[track_caller]
fn assert_rejects(r: &ValidationResult, needle: &str) {
    let errors = messages(r);
    assert!(
        errors.iter().any(|m| m.contains(needle)),
        "expected an error containing `{needle}`, got {errors:?}"
    );
}

/// The phrase every finding of this rule ends with.
const UNSUPPORTED: &str =
    "temporal conditions do not support Cedar's `datetime`, `duration`, and `ipaddr` types";

// ─── Binders ─────────────────────────────────────────────────────────

#[test]
fn a_binder_of_an_unsupported_extension_type_is_rejected() {
    for (ty, field) in [("datetime", "at"), ("duration", "ttl"), ("ipaddr", "addr")] {
        assert_rejects(
            &validate(&format!(
                r#"exists (t: {ty}). formerly within 1h Drupe::Action::"Login"::response{{ input.{field}: t }}"#
            )),
            &format!("the binder `t` is declared `{ty}`; {UNSUPPORTED}"),
        );
    }
    assert_rejects(
        &validate(
            r#"(count for (t: datetime). where formerly within 1h Drupe::Action::"Login"::response{ input.at: t }) >= 1"#,
        ),
        &format!("the binder `t` is declared `datetime`; {UNSUPPORTED}"),
    );
}

#[test]
fn a_decimal_binder_is_still_supported() {
    assert_passes(&validate(
        r#"exists (d: decimal). formerly within 1h Drupe::Action::"Login"::response{ input.score: d }"#,
    ));
}

// ─── Terms ───────────────────────────────────────────────────────────

#[test]
fn a_comparison_reading_an_unsupported_attribute_is_rejected() {
    for (path, ty) in [
        ("context.input.since", "datetime"),
        ("context.input.ttl", "duration"),
        ("context.input.addr", "ipaddr"),
        ("principal.joined", "datetime"),
    ] {
        assert_rejects(
            &validate(&format!(
                r#"formerly within 1h (Drupe::Action::"Login"::response{{ input.user: context.input.user }} && {path} == {path})"#
            )),
            &format!("`{path}` has the type `{ty}`; {UNSUPPORTED}"),
        );
    }
}

#[test]
fn a_record_holding_an_unsupported_value_is_rejected() {
    assert_rejects(
        &validate(
            r#"formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && context.input.meta == context.input.meta)"#,
        ),
        &format!("`context.input.meta` has the type `{{ at: datetime }}`; {UNSUPPORTED}"),
    );
}

#[test]
fn a_predicate_argument_of_an_unsupported_type_is_rejected() {
    assert_rejects(
        &validate(
            r#"formerly within 1h Drupe::Action::"Login"::response{ input.at: context.input.since }"#,
        ),
        &format!("`context.input.since` has the type `datetime`; {UNSUPPORTED}"),
    );
    assert_rejects(
        &validate_with(
            r#"formerly within 1h Drupe::Action::"Login"::response{ issuedAt: context.input.since }"#,
            Some(EVENT_SCHEMA),
        ),
        &format!("`context.input.since` has the type `datetime`; {UNSUPPORTED}"),
    );
}

#[test]
fn an_unsupported_operand_is_reported_alone() {
    // The comparison is not typed further, so its operand finding is the only one.
    let r = validate(
        r#"formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && context.input.since == context.input.user)"#,
    );
    assert_eq!(
        messages(&r),
        [format!(
            "`context.input.since` has the type `datetime`; {UNSUPPORTED}"
        )]
    );
}

#[test]
fn a_pin_on_an_unsupported_path_is_rejected() {
    let event_schema = r#"
decision event <A>::request {
    ...inputs(A),
}

event <A>::response {
    ...inputs(A),
    pin stamp: datetime = context.input.since,
}
"#;
    // A pin is injected into every predicate of its event as an argument, and validated like
    // an authored one, so the path is reported once as that argument and once as the pin.
    let r = validate_with(
        r#"formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }"#,
        Some(event_schema),
    );
    assert_eq!(
        messages(&r),
        [
            format!("`context.input.since` has the type `datetime`; {UNSUPPORTED}"),
            format!(
                "pin `stamp` of `Drupe::Action::\"Login\"::response` correlates the field with \
                 `context.input.since`, of type `datetime`; {UNSUPPORTED}"
            ),
        ]
    );
}

// ─── What stays valid ────────────────────────────────────────────────

#[test]
fn a_predicate_that_does_not_constrain_an_unsupported_field_is_valid() {
    assert_passes(&validate(
        r#"formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }"#,
    ));
    assert_passes(&validate(
        r#"formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user, input.at: * }"#,
    ));
}

#[test]
fn the_cedar_part_may_read_an_unsupported_attribute() {
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource)
when { context.input.since == context.input.since }
when temporal { formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user } };
"#;
    assert_passes(&Validator::new().validate(&lower(policy, None)));
}

#[test]
fn a_string_literal_does_not_match_a_datetime_field() {
    assert_rejects(
        &validate(
            r#"formerly within 1h Drupe::Action::"Login"::response{ input.at: "2026-01-01T00:00:00Z" }"#,
        ),
        "argument `input.at` of `Login` expects `datetime` but got `string`",
    );
}

// ─── Provider arguments ──────────────────────────────────────────────

/// A provider whose one parameter is a `string`, given the attribute `arg`.
fn validate_provider_argument(arg: &str) -> ValidationResult {
    let providers = ProviderDeclarations::from_json(
        r#"{
        "availableProviders": {
            "Risk::Score": {
                "argumentTypes": [ { "paramType": "string" } ],
                "outputType": { "paramType": "string" }
            }
        }
    }"#,
    )
    .expect("provider declarations parse");
    let service = ServiceSchema::builder()
        .providers(providers)
        .build()
        .expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    let policy = format!(
        "permit (principal, action == Drupe::Action::\"Read\", resource)\nwhen {{ Risk::Score({arg}) == \"ok\" }};\n"
    );
    let lowered = LoweredPolicySet::from_str(&policy, &service, &schema).expect("policy lowers");
    Validator::new().validate(&lowered)
}

#[test]
fn a_string_provider_parameter_takes_a_string_attribute() {
    assert_passes(&validate_provider_argument("context.input.user"));
}

#[test]
fn a_string_provider_parameter_does_not_take_a_datetime_attribute() {
    assert_rejects(
        &validate_provider_argument("context.input.since"),
        "argument `context.input.since` has type `datetime` on action `Drupe::Action::\"Read\"` \
         but the provider declares argument type `string`",
    );
}

#[test]
fn a_string_variable_does_not_bind_a_datetime_field() {
    assert_rejects(
        &validate(
            r#"exists (t: String). formerly within 1h Drupe::Action::"Login"::response{ input.at: t }"#,
        ),
        "argument `input.at` of `Login` expects `datetime` but got `string`",
    );
    assert_rejects(
        &validate_with(
            r#"exists (t: String). formerly within 1h Drupe::Action::"Login"::response{ issuedAt: t }"#,
            Some(EVENT_SCHEMA),
        ),
        "a variable bound by a field must have a type every value of the field has",
    );
}

#[test]
fn duration_and_ipaddr_arguments_are_rejected() {
    for (field, path, ty) in [
        ("ttl", "context.input.ttl", "duration"),
        ("addr", "context.input.addr", "ipaddr"),
    ] {
        assert_rejects(
            &validate(&format!(
                r#"formerly within 1h Drupe::Action::"Login"::response{{ input.{field}: {path} }}"#
            )),
            &format!("`{path}` has the type `{ty}`; {UNSUPPORTED}"),
        );
    }
}

#[test]
fn a_set_of_datetimes_is_rejected() {
    assert_rejects(
        &validate(
            r#"formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && context.input.stamps == context.input.stamps)"#,
        ),
        &format!("`context.input.stamps` has the type `array<datetime>`; {UNSUPPORTED}"),
    );
}

#[test]
fn both_unsupported_operands_are_reported() {
    let r = validate(
        r#"formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && context.input.since == context.input.ttl)"#,
    );
    assert_eq!(
        messages(&r),
        [
            format!("`context.input.since` has the type `datetime`; {UNSUPPORTED}"),
            format!("`context.input.ttl` has the type `duration`; {UNSUPPORTED}"),
        ]
    );
}

#[test]
fn an_unsupported_operand_in_an_aggregate_body_is_rejected() {
    assert_rejects(
        &validate(
            r#"(count for (t: Timepoint). where formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && tp(t) && context.input.since == context.input.since)) >= 1"#,
        ),
        &format!("`context.input.since` has the type `datetime`; {UNSUPPORTED}"),
    );
}

#[test]
fn an_unsupported_operand_from_a_macro_is_rejected() {
    let policy = r#"def temporal same(?x) {
    formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && ?x == ?x)
};
permit (principal, action == Drupe::Action::"Read", resource)
when temporal { same(context.input.since) };
"#;
    assert_rejects(
        &Validator::new().validate(&lower(policy, None)),
        &format!("`context.input.since` has the type `datetime`; {UNSUPPORTED}"),
    );
}

#[cfg(feature = "experimental-arithmetic")]
#[test]
fn an_unsupported_arithmetic_atom_is_rejected() {
    assert_rejects(
        &validate(
            r#"formerly within 1h (Drupe::Action::"Login"::response{ input.user: context.input.user } && context.input.since + 1 == 2)"#,
        ),
        &format!("`context.input.since` has the type `datetime`; {UNSUPPORTED}"),
    );
}

#[test]
fn a_pin_on_an_unsupported_entity_attribute_is_rejected() {
    let event_schema = r#"
decision event <A>::request {
    ...inputs(A),
}

event <A>::response {
    ...inputs(A),
    pin joined: datetime = principal.joined,
}
"#;
    // Reported as the injected argument and as the pin
    // (`a_pin_on_an_unsupported_path_is_rejected`).
    let r = validate_with(
        r#"formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }"#,
        Some(event_schema),
    );
    assert_eq!(
        messages(&r),
        [
            format!("`principal.joined` has the type `datetime`; {UNSUPPORTED}"),
            format!(
                "pin `joined` of `Drupe::Action::\"Login\"::response` correlates the field with \
                 `principal.joined`, of type `datetime`; {UNSUPPORTED}"
            ),
        ]
    );
}
