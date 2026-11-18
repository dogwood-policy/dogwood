//! The validity rules of the formal specification (`dogwood-lean`,
//! `Formula.WellTyped`) that `Validator` enforces on temporal leaves:
//!
//! * a temporal term reads an optional attribute only where a `has` test of
//!   the Cedar part guards it, at the leaf's position;
//! * a pin correlates its field with a request-side path that is declared and
//!   required in every request the rule decides, of a type the field can hold;
//! * the `for` variables of one aggregation have distinct names;
//! * a variable bound by a predicate field has a type every value of the field
//!   has;
//! * a binder scopes over its own body only, so a name an aggregation's `for`
//!   list rebinds has its enclosing type again outside the aggregation;
//! * an `==` or `!=` with a bare variable on one side and a term that is not a
//!   variable and holds no wildcard on the other compares two values of the
//!   same type (`EqCompatible`).

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema, ValidationResult,
    Validator, Value,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type LoginInput = { user: String };
  type ReadInput = { user: String, note?: String, level?: Long };
  entity Gateway;
  entity Bot;
  entity OAuthUser = { id: String, dept?: String };
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: LoginInput, session: { id: String }, tenant?: String }
  };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: ReadInput, session: { id: String }, tenant?: String }
  };
  action "Ping" appliesTo {
    principal: [OAuthUser, Bot], resource: [Gateway],
    context: { input: LoginInput, session: { id: String }, tenant?: String }
  };
}
"#;

fn validate_with(policy: &str, event_schema: Option<&str>) -> ValidationResult {
    let mut builder = ServiceSchema::builder();
    if let Some(e) = event_schema {
        builder = builder.event_schema_str(e);
    }
    let service = builder.build().expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    let policies = LoweredPolicySet::from_str(policy, &service, &schema).expect("policy lowers");
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

// ─── Optional attributes ─────────────────────────────────────────────

const OPTIONAL_NOTE: &str = "reads the optional attribute `input.note`";

#[test]
fn an_unguarded_read_of_an_optional_context_attribute_is_rejected() {
    let r = validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.note } };"#,
    );
    assert_rejects(&r, OPTIONAL_NOTE);
    assert_rejects(
        &r,
        "test it first, as in `context.input has note && temporal { … }`",
    );
}

#[test]
fn a_has_test_of_the_cedar_part_guards_the_read() {
    assert_passes(&validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when { context.input has note && temporal { formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.note } } };"#,
    ));
    // Cedar's `has` path tests every prefix.
    assert_passes(&validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when { context has input.note }
           when temporal { formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.note } };"#,
    ));
}

#[test]
fn a_test_that_does_not_reach_the_leaf_does_not_guard_it() {
    // An `unless` clause negates; a `||` does not establish its operands.
    for condition in [
        "unless { !(context.input has note) } when temporal { LEAF }",
        "when { context.input has note || temporal { LEAF } }",
        "when { temporal { LEAF } && context.input has note }",
    ] {
        let leaf = r#"formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.note }"#;
        let policy = format!(
            r#"permit (principal, action == Drupe::Action::"Read", resource) {};"#,
            condition.replace("LEAF", leaf)
        );
        assert_rejects(&validate(&policy), OPTIONAL_NOTE);
    }
}

#[test]
fn an_optional_attribute_in_an_aggregation_body_needs_a_guard() {
    let r = validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { (count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.note } && tp(t)))) >= 1 };"#,
    );
    assert_rejects(&r, OPTIONAL_NOTE);
}

// EXPERIMENTAL-ARITHMETIC: a compound operand parses only with the feature on.
#[cfg(feature = "experimental-arithmetic")]
#[test]
fn an_optional_attribute_in_a_compound_operand_needs_a_guard() {
    let r = validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { (count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && tp(t)))) + context.input.level <= 3 };"#,
    );
    assert_rejects(&r, "reads the optional attribute `input.level`");
}

#[test]
fn an_unguarded_read_of_an_optional_entity_attribute_is_rejected() {
    let leaf =
        r#"formerly within 1h Drupe::Action::"Login"::request{ input.user: principal.dept }"#;
    let r = validate(&format!(
        r#"permit (principal, action == Drupe::Action::"Read", resource) when temporal {{ {leaf} }};"#
    ));
    assert_rejects(
        &r,
        "`principal.dept` reads the optional attribute `dept` of `Drupe::OAuthUser`",
    );
    assert_passes(&validate(&format!(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when {{ principal has dept && temporal {{ {leaf} }} }};"#
    )));
}

#[test]
fn principal_id_reads_the_declared_required_attribute_and_needs_no_guard() {
    // `OAuthUser` declares a required `id: String`; `principal.id` is that attribute.
    assert_passes(&validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { formerly within 1h Drupe::Action::"Login"::request{ input.user: principal.id } };"#,
    ));
}

// ─── Pins ────────────────────────────────────────────────────────────

fn pinned_schema(reference: &str) -> String {
    format!(
        r#"
decision event <A>::request {{
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    pin key: String = {reference},
}}
"#
    )
}

const READ_AFTER_LOGIN: &str = r#"permit (principal, action == Drupe::Action::"Read", resource)
    when temporal { formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user } };"#;

#[test]
fn a_pin_on_a_required_context_path_is_valid() {
    assert_passes(&validate_with(
        READ_AFTER_LOGIN,
        Some(&pinned_schema("context.session.id")),
    ));
}

#[test]
fn a_pin_on_an_optional_or_undeclared_context_path_is_rejected() {
    for reference in ["context.tenant", "context.missing"] {
        let r = validate_with(READ_AFTER_LOGIN, Some(&pinned_schema(reference)));
        assert_rejects(
            &r,
            &format!(
                "pin `key` of `Drupe::Action::\"Login\"::request` correlates the field with \
                 `{reference}`, which is not a declared, required attribute"
            ),
        );
    }
    // A `has` test guards a read, not a pin: a pin is injected into every
    // predicate of its event, wherever the rule decides.
    let guarded = r#"permit (principal, action == Drupe::Action::"Read", resource)
        when { context has tenant && temporal { formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user } } };"#;
    assert_rejects(
        &validate_with(guarded, Some(&pinned_schema("context.tenant"))),
        "pin `key`",
    );
}

#[test]
fn a_pin_on_a_declared_required_principal_id_is_valid() {
    assert_passes(&validate_with(
        READ_AFTER_LOGIN,
        Some(&pinned_schema("principal.id")),
    ));
}

#[test]
fn a_pin_on_an_undeclared_id_or_an_optional_attribute_is_rejected() {
    // `Gateway` declares no `id`, and `OAuthUser`'s `dept` is optional.
    for reference in [
        "resource.id",
        "resource.type",
        "principal.type",
        "principal.dept",
    ] {
        let r = validate_with(READ_AFTER_LOGIN, Some(&pinned_schema(reference)));
        assert_rejects(
            &r,
            &format!(
                "pin `key` of `Drupe::Action::\"Login\"::request` correlates the field with \
                 `{reference}`, which is not a declared, required attribute"
            ),
        );
    }
}

#[test]
fn a_pin_of_the_wrong_type_is_rejected() {
    let r = validate_with(READ_AFTER_LOGIN, Some(&pinned_schema("principal")));
    assert_rejects(
        &r,
        "pin `key` of `Drupe::Action::\"Login\"::request` correlates the field, of type \
         `String`, with `principal`, which is a `Drupe::OAuthUser`",
    );
}

#[test]
fn a_scope_pin_needs_every_principal_type_the_rule_decides() {
    // `Ping` admits `Bot` principals, whose requests a `Login`'s
    // `callerPrincipal` (an `OAuthUser`) can never equal.
    let ping = r#"permit (principal, action == Drupe::Action::"Ping", resource)
        when temporal { formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user } };"#;
    let r = validate(ping);
    assert_rejects(
        &r,
        "pin `callerPrincipal` of `Drupe::Action::\"Login\"::request` correlates the field, of \
         type `Drupe::OAuthUser`, with `principal`, which is a `Drupe::Bot`",
    );
    // Narrowing the rule's scope to `OAuthUser` principals makes it valid.
    assert_passes(&validate(
        r#"permit (principal is Drupe::OAuthUser, action == Drupe::Action::"Ping", resource)
           when temporal { formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user } };"#,
    ));
}

// ─── Binders ─────────────────────────────────────────────────────────

#[test]
fn the_for_variables_of_an_aggregation_are_distinct() {
    let r = validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { (count for (t: Timepoint), (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && tp(t)))) >= 1 };"#,
    );
    assert_rejects(
        &r,
        "the `for` list of this aggregation binds `t` more than once",
    );
    assert_passes(&validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { (count for (t: Timepoint), (u: String). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: u } && tp(t)))) >= 1 };"#,
    ));
}

#[test]
fn a_variable_bound_by_a_field_has_every_type_the_field_holds() {
    // `Ping`'s `callerPrincipal` holds an `OAuthUser` or a `Bot`.
    let bind = |action: &str| {
        format!(
            r#"permit (principal is Drupe::OAuthUser, action == Drupe::Action::"Login", resource)
               when temporal {{ exists (pr: Drupe::OAuthUser). formerly within 1h Drupe::Action::"{action}"::request{{ callerPrincipal: pr }} }};"#
        )
    };
    let unpinned =
        "decision event <A>::request { ...inputs(A), callerPrincipal: principalType(A), }";
    assert_rejects(
        &validate_with(&bind("Ping"), Some(unpinned)),
        "argument `callerPrincipal` of `Ping` expects `Drupe::OAuthUser | Drupe::Bot`, but binds \
         the variable `pr`, declared `Drupe::OAuthUser`",
    );
    // `Login`'s holds an `OAuthUser` only.
    assert_passes(&validate_with(&bind("Login"), Some(unpinned)));
}

#[test]
fn a_binder_scopes_over_its_own_body_only() {
    // The aggregation's `for` list rebinds `t`; outside the aggregation, `t` is
    // the `Long` of the enclosing `exists` again.
    assert_passes(&validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { exists (t: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && tp(t)))) == t && t == 1) };"#,
    ));
    // Inside it, `t` is a timepoint, so comparing it with a `Long` is an error.
    let r = validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { exists (n: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && tp(t)) && t == 1)) == n && n == 1) };"#,
    );
    assert!(!r.validation_passed(), "{:?}", messages(&r));
}

// ─── Equalities that can bind a variable ─────────────────────────────
//
// See also `validation_soundness.rs`, `an_equality_that_binds_a_variable_needs_equal_types`.

/// A leaf over `Read`: a login correlated by `input.user`, beside which the existential `g: ty`
/// is bound only by `cmp`.
fn exists_compared(ty: &str, cmp: &str) -> String {
    format!(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal {{ exists (g: {ty}). (formerly within 1h Drupe::Action::"Login"::request{{ input.user: context.input.user }} && {cmp}) }};"#
    )
}

#[test]
fn an_equality_that_binds_a_variable_to_an_entity_of_another_type_is_rejected() {
    // Evaluation is untyped: `g == Drupe::OAuthUser::"alice"` binds `g` to alice, so the leaf
    // would hold though no `Gateway` equals an `OAuthUser`. Validation rejects it, as the
    // specification does (`EqCompatible`).
    for cmp in [
        r#"g == Drupe::OAuthUser::"alice""#,
        r#"Drupe::OAuthUser::"alice" == g"#,
        "g == principal",
    ] {
        assert_rejects(
            &validate(&exists_compared("Drupe::Gateway", cmp)),
            "equality requires both sides to have the same type",
        );
    }
}

#[test]
fn an_aggregation_variable_bound_to_an_entity_of_another_type_is_rejected() {
    assert_rejects(
        &validate(
            r#"permit (principal, action == Drupe::Action::"Read", resource)
               when temporal { (count for (g: Drupe::Gateway). where (formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user } && g == Drupe::OAuthUser::"alice")) >= 1 };"#,
        ),
        "equality requires both sides to have the same type",
    );
}

#[test]
fn an_equality_that_binds_a_variable_to_an_entity_of_its_own_type_is_valid() {
    for cmp in [r#"g == Drupe::Gateway::"gw1""#, "g == resource"] {
        assert_passes(&validate(&exists_compared("Drupe::Gateway", cmp)));
    }
}

#[test]
fn an_equality_of_entities_of_different_types_that_binds_nothing_is_valid() {
    // As in Cedar, which types it `False`: neither side is a variable it could bind.
    assert_passes(&validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && principal == resource) };"#,
    ));
}

/// A leaf over `Read` whose `g: Drupe::Gateway` is bound by a login's `callerResource`, then
/// compared by `cmp`.
fn bound_then_compared(cmp: &str) -> String {
    format!(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal {{ exists (g: Drupe::Gateway). (formerly within 1h Drupe::Action::"Login"::request{{ callerResource: g }} && {cmp}) }};"#
    )
}

#[test]
fn the_rule_is_syntactic_so_it_applies_where_the_equality_cannot_bind() {
    // `!=`, a negated `==`, and an `==` whose variable is already bound cannot bind `g` at run
    // time: each is false or true as Cedar would make it. The rule looks at the comparison's
    // shape only, as the specification's does (`eqRestricted?`), so it rejects them too.
    for cmp in ["g != principal", "!(g == principal)", "g == principal"] {
        assert_rejects(
            &validate(&bound_then_compared(cmp)),
            "equality requires both sides to have the same type",
        );
    }
    // The same shapes between values of one type are valid.
    for cmp in ["g != resource", "!(g == resource)", "g == resource"] {
        assert_passes(&validate(&bound_then_compared(cmp)));
    }
}

#[test]
fn the_rule_holds_in_every_request_environment_of_the_rule() {
    // `Ping` admits `OAuthUser` and `Bot` principals, so `g == principal` compares a
    // `Drupe::OAuthUser` with a `Drupe::Bot` in one of them. With no pins, nothing else is wrong.
    let unpinned = "decision event <A>::request {\n    ...inputs(A),\n}\n";
    let rule = |scope: &str| {
        format!(
            r#"permit ({scope}, action == Drupe::Action::"Ping", resource)
               when temporal {{ exists (g: Drupe::OAuthUser). (formerly within 1h Drupe::Action::"Login"::request{{ input.user: context.input.user }} && g == principal) }};"#
        )
    };
    assert_rejects(
        &validate_with(&rule("principal"), Some(unpinned)),
        "equality requires both sides to have the same type, got `Drupe::OAuthUser` and \
         `Drupe::Bot`",
    );
    assert_passes(&validate_with(
        &rule("principal is Drupe::OAuthUser"),
        Some(unpinned),
    ));
}

#[test]
fn the_rule_applies_to_the_expansion_of_a_macro() {
    let rule = |arg: &str| {
        format!(
            r#"def temporal logged_in_at(?gw) {{
                 exists ($g: Drupe::Gateway). (formerly within 1h Drupe::Action::"Login"::request{{ input.user: context.input.user }} && $g == ?gw)
               }};
               permit (principal, action == Drupe::Action::"Read", resource)
               when temporal {{ logged_in_at({arg}) }};"#
        )
    };
    assert_rejects(
        &validate(&rule(r#"Drupe::OAuthUser::"alice""#)),
        "equality requires both sides to have the same type",
    );
    assert_passes(&validate(&rule(r#"Drupe::Gateway::"gw1""#)));
}

#[test]
fn unvalidated_the_binding_equality_holds_across_types() {
    // Why the rule exists: evaluation does not consult `g`'s declared type, so an authorizer
    // given the rejected leaf without validation binds `g` to alice and allows.
    let policy = exists_compared("Drupe::Gateway", r#"g == Drupe::OAuthUser::"alice""#);
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    let lowered = LoweredPolicySet::from_str(&policy, &ServiceSchema::defaults(), &schema)
        .expect("policy lowers");
    assert_rejects(
        &Validator::new().validate(&lowered),
        "equality requires both sides to have the same type",
    );
    let event = |action: &str, ts| {
        Event::builder(&format!("Drupe::Action::{action}"), "request")
            .timestamp(ts)
            .principal("Drupe::OAuthUser::\"alice\"")
            .resource("Drupe::Gateway::\"gw1\"")
            .field("input", "user", Value::String("alice".to_string()))
            .request_context("input", "user", Value::String("alice".to_string()))
            .request_context("session", "id", Value::String("s1".to_string()))
            .entity(
                "Drupe::OAuthUser::\"alice\"",
                [("id", Value::String("alice".to_string()))],
            )
            .build()
    };
    let read = |authorizer: &mut Authorizer, ts| {
        authorizer
            .is_authorized(&event("Read", ts))
            .expect("decision point")
            .decision()
    };
    // The leaf is evaluated: with no login yet, it fails.
    let mut authorizer = Authorizer::new(lowered);
    assert_eq!(read(&mut authorizer, 0), Decision::Deny);
    authorizer
        .is_authorized(&event("Login", 5))
        .expect("decision point");
    assert_eq!(read(&mut authorizer, 10), Decision::Allow);
}

#[test]
fn two_variables_of_different_entity_types_may_be_compared() {
    // An equality of two variables binds neither, so the two types need not be equal; the
    // comparison is false, as in Cedar.
    assert_passes(&validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { exists (g: Drupe::Gateway). exists (u: Drupe::OAuthUser). (formerly within 1h Drupe::Action::"Login"::request{ callerResource: g, callerPrincipal: u } && g == u) };"#,
    ));
}

// ─── A wildcard is not a comparison operand ──────────────────────────
//
// A wildcard outside a predicate argument resolves to no value, so a comparison with it
// would be false whatever the trace, and its negation true. The specification rejects it
// (`Formula.WellTyped`: a wildcard is not a comparison operand); so does the crate. See also
// `validation_soundness.rs`, `a_wildcard_comparison_operand_is_rejected`.

const WILDCARD_OPERAND: &str = "a wildcard (`*` / `_`) cannot be a comparison operand";

#[test]
fn a_wildcard_on_either_side_of_any_comparison_is_rejected() {
    for cmp in [
        r#""foo" == *"#,
        "* == context.input.user",
        "context.input.user != _",
        "!(context.input.user == *)",
        "context.input.level < *",
    ] {
        let rule = format!(
            r#"permit (principal, action == Drupe::Action::"Read", resource)
               when {{ context.input has level }}
               when temporal {{ formerly within 1h (Drupe::Action::"Login"::request{{ input.user: context.input.user }} && {cmp}) }};"#
        );
        let errors = messages(&validate(&rule));
        assert_eq!(
            errors.len(),
            1,
            "{cmp}: expected only the wildcard finding, got {errors:?}"
        );
        assert!(errors[0].starts_with(WILDCARD_OPERAND), "{cmp}: {errors:?}");
    }
}

#[test]
fn a_wildcard_against_or_inside_an_aggregate_is_rejected() {
    for leaf in [
        r#"(count for (t: Timepoint). where formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && tp(t))) == *"#,
        r#"(count for (t: Timepoint). where formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && tp(t) && context.input.user == *)) >= 1"#,
    ] {
        let errors = messages(&validate(&format!(
            r#"permit (principal, action == Drupe::Action::"Read", resource)
               when temporal {{ {leaf} }};"#
        )));
        assert_eq!(errors.len(), 1, "{leaf}: {errors:?}");
        assert!(
            errors[0].starts_with(WILDCARD_OPERAND),
            "{leaf}: {errors:?}"
        );
    }
}

#[test]
fn a_wildcard_in_a_since_operand_is_rejected() {
    // The left of `since` is checked at every step; the leaf also fails the time-dependence
    // check, which is the other finding.
    assert_rejects(
        &validate(
            r#"permit (principal, action == Drupe::Action::"Read", resource)
               when temporal { (context.input.user == *) since within 1h Drupe::Action::"Login"::request{ input.user: context.input.user } };"#,
        ),
        WILDCARD_OPERAND,
    );
}

#[cfg(feature = "experimental-arithmetic")]
#[test]
fn a_wildcard_inside_an_arithmetic_operand_is_rejected() {
    assert_rejects(
        &validate(
            r#"permit (principal, action == Drupe::Action::"Read", resource)
               when { context.input has level }
               when temporal { formerly within 1h (Drupe::Action::"Login"::request{ input.user: context.input.user } && context.input.level + * > 3) };"#,
        ),
        "a wildcard (`*` / `_`) cannot appear inside an arithmetic expression",
    );
}

#[test]
fn a_wildcard_argument_of_a_macro_that_compares_it_is_rejected() {
    // A macro meant to mean "any user" when given `*` does not: after expansion the equality
    // compares with a wildcard, which validation rejects. A rule that means "some user" leaves
    // the equality out.
    let rule = |arg: &str| {
        format!(
            r#"def temporal repeat_sender(?user) {{
                 exists ($u: String).
                   (formerly within 1h Drupe::Action::"Login"::request{{ input.user: $u }})
                   && $u == ?user
               }};
               permit (principal, action == Drupe::Action::"Read", resource)
               when temporal {{ repeat_sender({arg}) }};"#
        )
    };
    assert_rejects(&validate(&rule("*")), WILDCARD_OPERAND);
    assert_passes(&validate(&rule(r#""alice""#)));
}

#[test]
fn a_wildcard_predicate_argument_is_still_valid() {
    assert_passes(&validate(
        r#"permit (principal, action == Drupe::Action::"Read", resource)
           when temporal { formerly within 1h Drupe::Action::"Login"::request{ input.user: * } };"#,
    ));
}
