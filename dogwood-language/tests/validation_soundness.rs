//! Policy sets the formal specification (`dogwood-lean`, `PolicySet.Valid`)
//! rejects, and that `Validator` used to accept.
//!
//! Each test names the rule of the specification the policy set breaks and
//! asserts a finding whose message the conformance harness
//! (`dogwood-lean/Dogwood/Conformance/Harness.lean`, `crateCategory`) files under
//! the specification's category for it, so that the crate and the specification
//! report the same category. The comment on each test gives the category.

use dogwood_language::{
    Error, LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, ValidationError,
    ValidationResult, Validator,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type LoginInput = { user: String };
  type Profile = { name: String };
  type ReadInput = {
    user: String,
    note?: String,
    count: Long,
    owner: User,
    other: Other::User,
    users: Set<User>,
    others: Set<Other::User>,
    profile: Profile,
    card: { number: Long },
    when: datetime,
    grade: Grade,
    otherGrade: Other::Grade
  };
  entity Grade enum ["low", "high"];
  entity Gateway;
  entity Bot;
  entity Group;
  entity User in [Group] = { id: Long, level: Long, dept?: String };
  action "Login" appliesTo {
    principal: [User], resource: [Gateway],
    context: { input: LoginInput }
  };
  action "Read" appliesTo {
    principal: [User], resource: [Gateway],
    context: { input: ReadInput }
  };
  action "Ping" appliesTo {
    principal: [User, Bot], resource: [Gateway],
    context: { input: ReadInput }
  };
}
namespace Other {
  entity User;
  entity Grade enum ["low", "high"];
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

fn validate_with(policy: &str, providers: Option<&str>) -> ValidationResult {
    let policies = lower_with(policy, SCHEMA, providers).expect("policy lowers");
    Validator::new().validate(&policies)
}

fn validate(policy: &str) -> ValidationResult {
    validate_with(policy, None)
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

/// A rule on `Read` whose `when temporal` body is `leaf`.
fn read_rule(leaf: &str) -> String {
    format!(r#"permit (principal, action == Drupe::Action::"Read", resource) when temporal {{ {leaf} }};"#)
}

/// A login by the current request's user, as a conjunct that makes a leaf vary
/// with the timepoint.
const LOGIN: &str = r#"formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }"#;

/// A login by the current request's user at which `condition` holds: the
/// condition is part of an operator body, which varies with the timepoint.
fn login_and(condition: &str) -> String {
    format!(
        r#"formerly within 1h (Drupe::Action::"Login"::request{{ input.user: context.input.user }} && {condition})"#
    )
}

// ─── Compound operands (experimental arithmetic) ─────────────────────

// EXPERIMENTAL-ARITHMETIC: a compound operand parses only with the feature on.
#[cfg(feature = "experimental-arithmetic")]
#[test]
fn an_undeclared_event_in_an_aggregate_inside_a_compound_is_rejected() {
    // Category: event names.
    let r = validate(&read_rule(
        r#"(count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Nope"::request{} && tp(t)))) + 1 > 3"#,
    ));
    assert_rejects(&r, "does not name a declared event");
}

#[cfg(feature = "experimental-arithmetic")]
#[test]
fn a_constant_aggregate_body_inside_a_compound_is_rejected() {
    // Category: time dependence.
    let r = validate(&read_rule(
        r#"(count for (a: Long). where (a == context.input.count)) + 1 > 3"#,
    ));
    assert_rejects(&r, "does not vary with the current timepoint");
}

#[cfg(feature = "experimental-arithmetic")]
#[test]
fn an_array_constant_in_an_aggregate_inside_a_compound_fails_lowering() {
    // The specification has no array term; lowering rejects arrays everywhere.
    let policy = read_rule(
        r#"(count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: ["a", "b"] } && tp(t)))) + 1 > 3"#,
    );
    let err = lower_with(&policy, SCHEMA, None).expect_err("an array constant fails lowering");
    assert!(err.to_string().contains("array constants"), "{err}");
}

// ─── Literals, wildcards, and binders ────────────────────────────────

#[test]
fn a_wildcard_comparison_operand_is_rejected() {
    // Category: placement. `x == *` is always false, `!(x == *)` always true.
    for leaf in [
        login_and("context.input.user == *"),
        login_and("!(context.input.user != _)"),
    ] {
        assert_rejects(&validate(&read_rule(&leaf)), "wildcard");
    }
}

#[test]
fn an_undeclared_action_literal_is_rejected() {
    // Category: paths.
    let r = validate(&read_rule(&login_and(
        r#"Drupe::Action::"Lgoin" == Drupe::Action::"Login""#,
    )));
    assert_rejects(&r, r#"`Drupe::Action::"Lgoin"` is not a declared action"#);
}

#[test]
fn a_decimal_literal_that_does_not_parse_is_rejected() {
    // Category: paths.
    let r = validate(&read_rule(&login_and(
        r#"decimal("1.23456") == decimal("1.0")"#,
    )));
    assert_rejects(&r, "does not parse as a `decimal`");
}

#[test]
fn a_binder_of_an_undeclared_or_unqualified_type_is_rejected() {
    // Category: binders. `User` alone is not `Drupe::User`.
    for ty in ["Nope", "User", "Drupe::Usr"] {
        let r = validate(&read_rule(&format!(
            r#"exists (u: {ty}). formerly within 1h Drupe::Action::"Login"::request{{ callerPrincipal: u }}"#
        )));
        assert_rejects(&r, "names no declared entity type");
    }
    assert_passes(&validate(&read_rule(
        r#"exists (u: Drupe::User). formerly within 1h Drupe::Action::"Login"::request{ callerPrincipal: u }"#,
    )));
}

// ─── Types ───────────────────────────────────────────────────────────

#[test]
fn entity_types_are_compared_by_their_qualified_names() {
    // Category: predicate arguments, then comparison operands.
    let r = validate(&read_rule(
        r#"formerly within 1h Drupe::Action::"Read"::request{ input.owner: Other::User::"alice" }"#,
    ));
    assert_rejects(&r, "expects `Drupe::User` but got `Other::User`");
    let r = validate(&read_rule(
        r#"exists (u: Other::User). formerly within 1h Drupe::Action::"Read"::request{ input.owner: u }"#,
    ));
    assert_rejects(&r, "expects `Drupe::User` but got `Other::User`");
    let r = validate(&read_rule(&login_and(
        "context.input.users == context.input.others",
    )));
    assert_rejects(&r, "equality requires both sides to have the same type");
}

#[test]
fn a_scope_root_is_typed_in_each_request_environment() {
    // Category: predicate arguments. `Ping` admits `User` and `Bot` principals,
    // and `input.owner` holds a `User` only.
    let r = validate(
        r#"permit (principal, action == Drupe::Action::"Ping", resource)
           when temporal { formerly within 1h Drupe::Action::"Ping"::request{ input.owner: principal } };"#,
    );
    assert_rejects(&r, "expects `Drupe::User` but got `Drupe::Bot`");
    // Narrowed to `User`, it is well-typed.
    assert_passes(&validate(
        r#"permit (principal is Drupe::User, action == Drupe::Action::"Ping", resource)
           when temporal { formerly within 1h Drupe::Action::"Ping"::request{ input.owner: principal } };"#,
    ));
}

#[test]
fn an_equality_that_binds_a_variable_needs_equal_types() {
    // Category: comparison operands.
    let r = validate(&read_rule(&format!(
        "exists (x: Drupe::User). ({LOGIN} && x == resource)"
    )));
    assert_rejects(&r, "equality requires both sides to have the same type");
    // An equality that binds nothing may compare two entity types.
    assert_passes(&validate(&read_rule(&login_and("!(principal == resource)"))));
}

#[test]
fn records_are_compared_exactly() {
    // Category: comparison operands.
    let r = validate(&read_rule(&login_and(
        "context.input.profile == context.input.card",
    )));
    assert_rejects(&r, "equality requires both sides to have the same type");
    assert_passes(&validate(&read_rule(&login_and(
        "context.input.profile == context.input.profile",
    ))));
}

#[test]
fn a_datetime_is_not_a_temporal_operand() {
    // Category: extension types. Temporal conditions do not support `datetime`, so the
    // comparison is not typed further (`tests/extension_typed_fields.rs`).
    let r = validate(&read_rule(&login_and(r#"context.input.when == "2026-01-01""#)));
    assert_rejects(
        &r,
        "`context.input.when` has the type `datetime`; temporal conditions do not support Cedar's",
    );
}

#[test]
fn a_non_variable_argument_of_a_field_the_event_schema_names_is_typed() {
    // Category: predicate arguments.
    for arg in [
        "requestId: 5",
        "callerPrincipal: resource",
        r#"callerResource: Drupe::User::"alice""#,
    ] {
        let r = validate(&read_rule(&format!(
            r#"formerly within 1h Drupe::Action::"Login"::request{{ {arg} }}"#
        )));
        assert_rejects(&r, "expects");
    }
    assert_passes(&validate(&read_rule(
        r#"formerly within 1h Drupe::Action::"Login"::request{ requestId: "r1", callerPrincipal: principal }"#,
    )));
}

#[test]
fn a_field_whose_declared_type_names_no_type_holds_no_value() {
    // Category: predicate arguments. The event schema types `meta` by a name the
    // schema does not declare, so no argument has its type.
    let event_schema = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    meta: Strng,
}
"#;
    let service = ServiceSchema::builder()
        .event_schema_str(event_schema)
        .build()
        .expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    let policies = LoweredPolicySet::from_str(
        &read_rule(r#"formerly within 1h Drupe::Action::"Login"::request{ meta: "x" }"#),
        &service,
        &schema,
    )
    .expect("policy lowers");
    assert_rejects(&Validator::new().validate(&policies), "argument `meta`");
}

#[test]
fn principal_id_has_the_type_the_entity_type_declares() {
    // Category: comparison operands. `principal.id` is an attribute like any other, as in
    // Cedar: here the entity type declares it `Long`.
    let r = validate(&read_rule(&login_and(r#"principal.id == "alice""#)));
    assert_rejects(&r, "equality requires both sides to have the same type");
    assert_passes(&validate(&read_rule(&login_and("principal.id == 5"))));
}

#[test]
fn principal_in_a_group_is_checked_in_the_environments_of_its_members() {
    // Accepted by both: `Bot` cannot be a member of a `Group`, so the rule never
    // decides a `Bot`, which declares no `level`. (The specification narrows the
    // environments of `principal in E` as Cedar's typechecker does.)
    assert_passes(&validate(&format!(
        r#"permit (principal in Drupe::Group::"staff", action == Drupe::Action::"Ping", resource)
           when temporal {{ {} }};"#,
        login_and("principal.level > 3")
    )));
}

// ─── Information providers ───────────────────────────────────────────

const PROVIDERS: &str = r#"{
    "availableProviders": {
        "Risk::Score": {
            "argumentTypes": [ { "paramType": "string" } ],
            "outputType": { "paramType": "long" }
        },
        "Risk::Owner": {
            "argumentTypes": [ { "paramType": "entity", "entityType": "Drupe::Grade" } ],
            "outputType": { "paramType": "bool" }
        },
        "Risk::Names": {
            "argumentTypes": [ { "paramType": "set", "items": { "paramType": "string" } } ],
            "outputType": { "paramType": "bool" }
        },
        "Risk::Profile": {
            "argumentTypes": [ { "paramType": "record", "fields": { "name": { "paramType": "string" } }, "required": ["name"] } ],
            "outputType": { "paramType": "bool" }
        },
        "Risk::Chain": {
            "argumentTypes": [],
            "outputType": { "paramType": "set", "items": { "paramType": "string" } },
            "availableMethods": {
                "first": {
                    "inputType": { "paramType": "set", "items": { "paramType": "long" } },
                    "outputType": { "paramType": "long" }
                }
            }
        }
    }
}"#;

fn provider_rule(condition: &str) -> String {
    format!(r#"permit (principal, action == Drupe::Action::"Read", resource) when {{ {condition} }};"#)
}

#[test]
fn a_provider_argument_may_read_an_optional_attribute_unguarded() {
    // The provider contract tolerates an absent argument: an unguarded optional
    // attribute resolves to an absent value. The specification accepts it too.
    assert_passes(&validate_with(
        &provider_rule("Risk::Score(context.input.note) > 3"),
        Some(PROVIDERS),
    ));
    assert_passes(&validate_with(
        &provider_rule("Risk::Score(principal.dept) > 3"),
        Some(PROVIDERS),
    ));
}

#[test]
fn a_provider_argument_has_its_declared_type_exactly() {
    // Category: providers.
    for call in [
        // A bare scope root is an entity, not a string.
        "Risk::Score(principal) > 3",
        // The whole context is not an argument.
        "Risk::Score(context) > 3",
        // An entity of another type.
        "Risk::Owner(context.input.otherGrade)",
        "Risk::Owner(resource)",
        // A set's literal elements are typed.
        "Risk::Names([1, 2])",
        "Risk::Names([context.input.count])",
        // A record of another shape.
        "Risk::Profile(context.input.card)",
        // An extension type is not a string.
        "Risk::Score(context.input.when) > 3",
        // `principal.id` is the declared `Long` attribute, not a string.
        "Risk::Score(principal.id) > 3",
    ] {
        let r = validate_with(&provider_rule(call), Some(PROVIDERS));
        assert!(
            r.validation_errors()
                .any(|e| matches!(e, ValidationError::Extension { code: "provider", .. })),
            "expected a provider finding for `{call}`, got {:?}",
            messages(&r)
        );
    }
    for call in [
        "Risk::Owner(context.input.grade)",
        r#"Risk::Names(["a", context.input.user])"#,
        "Risk::Profile(context.input.profile)",
    ] {
        assert_passes(&validate_with(&provider_rule(call), Some(PROVIDERS)));
    }
}

#[test]
fn a_provider_method_takes_the_cedar_type_of_the_stage_before_it() {
    // Category: providers. A `Set<String>` is not a `Set<Long>`.
    let r = validate_with(&provider_rule("Risk::Chain().first() > 3"), Some(PROVIDERS));
    assert_rejects(&r, "expects an input of type");
}

// ─── The Cedar part ──────────────────────────────────────────────────

#[test]
fn an_impossible_policy_is_an_error() {
    // Category: cedar. `Read` admits no `Bot` principal.
    let r = validate(
        r#"permit (principal is Drupe::Bot, action == Drupe::Action::"Read", resource);"#,
    );
    assert!(!r.validation_passed(), "an impossible policy is an error");
    assert_rejects(&r, "policy is impossible");
}

#[test]
fn the_cedar_part_reads_the_context_only_through_other_attributes() {
    // Category: context reads.
    for condition in [
        "context == context",
        r#"{ c: context }.c has input"#,
        "context.policy_0__temporal_0",
        "context has providers",
    ] {
        let r = validate(&format!(
            r#"permit (principal, action == Drupe::Action::"Read", resource)
               when {{ {condition} }}
               when temporal {{ {LOGIN} }};"#
        ));
        assert_rejects(&r, "reads the request context");
    }
}

#[test]
fn a_temporal_leaf_does_not_read_a_hoisted_attribute() {
    // Category: paths. The hoisted attributes are not part of the request.
    let r = validate(&read_rule(&login_and("context.policy_0__temporal_0 == true")));
    assert_rejects(&r, "has no context field");
}

#[test]
fn a_declared_context_attribute_with_a_hoisted_name_is_not_overwritten() {
    // The augmented schema would replace the declared `Long` with the leaf's
    // `Bool`; lowering refuses instead.
    let schema = SCHEMA.replace(
        "context: { input: ReadInput }",
        "context: { input: ReadInput, policy_0__temporal_0: Long }",
    );
    let err = lower_with(&read_rule(LOGIN), &schema, None)
        .expect_err("a declared attribute with a hoisted name fails lowering");
    assert!(err.to_string().contains("policy_0__temporal_0"), "{err}");
}
