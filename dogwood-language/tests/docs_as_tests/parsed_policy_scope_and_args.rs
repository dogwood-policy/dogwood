//! Reading a policy's **scope** and its **provider-invocation arguments**
//! straight off a [`ParsedPolicy`] — *before* lowering, with only a
//! [`ServiceSchema`] (no action schema).
//!
//! These two accessors let a consumer that previously had to lower a policy
//! (or hand-crawl an opaque handle) answer "what does this rule scope, and what
//! does it pass to its providers?" up front:
//!
//!   * [`ParsedPolicy::scope`] returns a Dogwood-owned [`PolicyScope`] view.
//!     Its entity leaves are the public [`cedar_policy::EntityUid`] /
//!     `EntityTypeName`, and a `?principal` / `?resource` slot reads as `None`
//!     — so no `cedar-policy-core` or internal AST type is exposed.
//!   * [`ParsedPolicy::provider_invocations_with_args`] returns the structured
//!     [`Invocation`]s, each carrying its `Ns::Fn` key **and** its resolved
//!     [`Arg`] list, extracted through the exact conversion lowering uses.
//!
//! Provider invocations are recognized structurally (`Ns::Fn(...)`), so neither
//! accessor needs the providers to be *declared* — a bare `ServiceSchema` (no
//! provider declarations, default event schema) suffices to read both.

use dogwood_language::{
    ActionConstraint, Arg, ParsedPolicySet, PrincipalConstraint, ResourceConstraint, ServiceSchema,
};

/// The corpus `0012` policy: a concrete action scope
/// (`action == Drupe::Action::"Read"`, principal/resource unconstrained)
/// and a provider invocation whose base argument is a `context` field path and
/// whose `.above(…)` method takes a `decimal("0.5")` literal.
const SCORE_ABOVE: &str = r#"
permit (
    principal,
    action == Drupe::Action::"Read",
    resource
)
unless guardrails {
    Risk::Score(context.input.document).above(decimal("0.5")) == true
};
"#;

/// A parse against a bare `ServiceSchema` (no providers, default event schema).
/// Phase 1 needs no action schema, which is the whole point of reading these
/// facts up front.
fn parse(src: &str) -> ParsedPolicySet {
    let service = ServiceSchema::builder().build().expect("service schema");
    ParsedPolicySet::parse(src, &service).expect("parses")
}

#[test]
fn scope_view_reports_the_concrete_action_and_unconstrained_principal_resource() {
    let parsed = parse(SCORE_ABOVE);
    let policy = parsed.policies().next().expect("one policy");
    let scope = policy.scope();

    // `principal` and `resource` are bare — unconstrained.
    assert_eq!(scope.principal(), &PrincipalConstraint::Any);
    assert_eq!(scope.resource(), &ResourceConstraint::Any);

    // `action == Drupe::Action::"Read"` — a single concrete action.
    match scope.action() {
        ActionConstraint::Eq(uid) => {
            assert_eq!(uid.type_name().to_string(), "Drupe::Action");
            assert_eq!(uid.id().unescaped(), "Read");
        }
        other => panic!("expected a concrete action `==` constraint, got {other:?}"),
    }
}

#[test]
fn provider_invocation_args_are_readable_before_lowering() {
    let parsed = parse(SCORE_ABOVE);
    let policy = parsed.policies().next().expect("one policy");

    let invocations = policy
        .provider_invocations_with_args()
        .expect("well-formed provider arguments");

    // Exactly one invocation site: `Risk::Score(...)`. The trailing `.above(…)`
    // method is *not* a second invocation — it hangs off this base call.
    assert_eq!(invocations.len(), 1, "one provider invocation site");
    let inv = &invocations[0];
    assert_eq!(inv.key(), "Risk::Score");

    // Its single argument is the attribute path `context.input.document`.
    assert_eq!(inv.args.len(), 1);
    match &inv.args[0] {
        Arg::Field(path) => assert_eq!(
            path,
            &[
                "context".to_string(),
                "input".to_string(),
                "document".to_string()
            ]
        ),
        other => panic!("expected a `context.input.document` field path, got {other:?}"),
    }
}

#[test]
fn scope_view_reports_template_slots_and_is_constraints() {
    // Exercises the shapes `0012` doesn't: a `?principal` slot on `==`, and a
    // `resource is Type` constraint. A slot reads as `None`; an `is` carries
    // the entity type name.
    let src = r#"
permit (
    principal == ?principal,
    action,
    resource is Drupe::Gateway
);
"#;
    let parsed = parse(src);
    let policy = parsed.policies().next().expect("one policy");
    let scope = policy.scope();

    // `principal == ?principal` — an `Eq` whose target is a slot (`None`).
    assert_eq!(scope.principal(), &PrincipalConstraint::Eq(None));

    // Bare `action` — unconstrained.
    assert_eq!(scope.action(), &ActionConstraint::Any);

    // `resource is Drupe::Gateway`.
    match scope.resource() {
        ResourceConstraint::Is(ty) => assert_eq!(ty.to_string(), "Drupe::Gateway"),
        other => panic!("expected a `resource is …` constraint, got {other:?}"),
    }
}

#[test]
fn malformed_provider_argument_is_rejected_with_a_located_error() {
    // A provider argument outside the grammar (arithmetic) is reported by the
    // pre-lowering accessor as the same self-rendering error lowering would
    // raise — not silently dropped.
    let src = r#"
permit ( principal, action, resource )
when guardrails {
    Risk::Score(1 + 2).above(decimal("0.5")) == true
};
"#;
    let parsed = parse(src);
    let policy = parsed.policies().next().expect("one policy");

    let err = policy
        .provider_invocations_with_args()
        .expect_err("arithmetic is not a valid provider argument");
    let rendered = err.to_string();
    assert!(
        rendered.contains("provider argument"),
        "error should explain the provider-argument rule, got: {rendered}"
    );
}
