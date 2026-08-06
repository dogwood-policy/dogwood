//! Slice 1 capability test: a temporal marker *nested inside* a Cedar
//! expression.
//!
//! This is the composition the old representation could not express. The
//! surface body used to be opaque text (or a whole-clause tagged marker),
//! so `context.input.shares < 100 && temporal { … }` had no
//! representation: the marker had to be the entire clause. With the
//! structured `Expr` AST the marker is an `Expr::Extension` admitted as a
//! `primary`, so it can sit anywhere in the expression. cedarify hoists
//! the temporal leaf to a `context.__temporal_0` reference and leaves the
//! `&&` and the comparison as native Cedar.
//!
//! We assert the policy parses, hoists a temporal leaf (so it is no longer
//! self-contained Cedar), and validates against the case schema — all
//! through the public Cedar-parity API: build a [`ServiceSchema`] and a
//! [`PolicySchema`], parse + lower with [`LoweredPolicySet::from_str`], then
//! validate with a [`Validator`].

use std::path::Path;

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema, Validator};

/// Reuse a temporal case's schema (it types `SellShares` and the
/// `context.input` record the marker and comparison both reference).
fn schema_src() -> String {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/docs_as_tests/temporal_cases/documentation_0300_formerly_within_short_window");
    std::fs::read_to_string(dir.join("schema.cedarschema")).expect("read schema")
}

/// The request/response event schema convention these temporal markers
/// validate against.
fn event_schema() -> String {
    std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .expect("read event schema")
}

/// Build the case schema halves from the action schema + request/response
/// event schema, with no provider declarations.
fn build_schema() -> (ServiceSchema, PolicySchema) {
    let service = ServiceSchema::builder()
        .event_schema_str(&event_schema())
        .build()
        .expect("service schema builds");
    let policy_schema =
        PolicySchema::from_cedarschema_str(&schema_src()).expect("policy schema builds");
    (service, policy_schema)
}

#[test]
fn temporal_marker_conjoined_with_cedar_comparison() {
    let (service, policy_schema) = build_schema();

    // The marker is the right operand of `&&`; the left is plain Cedar.
    let policy = r#"
        permit (
            principal,
            action == Drupe::Action::"SellShares",
            resource
        )
        when {
            context.input.shares < 100
            && temporal {
                formerly within 1h Drupe::Action::"ApproveSale"::request{input.stock: context.input.stock}
            }
        };
    "#;

    let policies = LoweredPolicySet::from_str(policy, &service, &policy_schema)
        .unwrap_or_else(|e| panic!("parse/lower failed:\n{e:#?}"));

    // A temporal leaf hoisted out of the mid-expression marker, so the policy
    // set is not self-contained Cedar. The whole point of this test was
    // "exactly one temporal leaf", but the public API exposes only the
    // *presence* of hoisted temporal/provider leaves, not their count — so the
    // old `bundle.temporal.len() == 1` is weakened to this presence check.
    assert!(
        !policies.is_self_contained_cedar(),
        "a temporal leaf should hoist out of the mid-expression marker",
    );

    let result = Validator::new().validate(&policies);
    assert!(
        result.validation_passed(),
        "validation errors: {:?}",
        result
            .validation_errors()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );
}

#[test]
fn temporal_marker_inside_if_then_else() {
    let (service, policy_schema) = build_schema();

    // A marker buried in the `then` branch of an `if`/`then`/`else`.
    let policy = r#"
        permit (
            principal,
            action == Drupe::Action::"SellShares",
            resource
        )
        when {
            if context.input.shares < 100
            then temporal {
                formerly within 1h Drupe::Action::"ApproveSale"::request{input.stock: context.input.stock}
            }
            else false
        };
    "#;

    let policies = LoweredPolicySet::from_str(policy, &service, &policy_schema)
        .unwrap_or_else(|e| panic!("parse/lower failed:\n{e:#?}"));

    // As above: the public API exposes presence, not count, of hoisted leaves,
    // so the old `bundle.temporal.len() == 1` becomes a presence check.
    assert!(
        !policies.is_self_contained_cedar(),
        "a temporal leaf should hoist out of the if/then/else marker",
    );

    let result = Validator::new().validate(&policies);
    assert!(
        result.validation_passed(),
        "validation errors: {:?}",
        result
            .validation_errors()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );
}
