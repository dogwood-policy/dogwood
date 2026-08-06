//! Names-only validation of temporal predicates against a derived event
//! schema.
//!
//! This is the first static check temporal predicates get: every
//! predicate must name a derived event (by namespace + action + kind),
//! and every field it *mentions* must be declared on that event. A
//! predicate that omits a declared field is fine — omission means
//! "wildcard", not "missing". Only a mentioned name that the event does
//! not declare (a typo, a stale field) is an error.
//!
//! It is deliberately separate from `extension::temporal::check`, which
//! runs at parse time and is schema-blind by construction; this pass runs
//! later, once the action schema (and thus the derived event schema) is
//! available, on the post-expansion condition tree.

use super::derive::DerivedEventSchema;
use crate::extension::temporal::ast::{AggExprKind, Condition, ConditionKind, Term};

/// Check every predicate in `cond` against the derived event schema.
pub fn validate_condition(cond: &Condition, schema: &DerivedEventSchema) -> Result<(), String> {
    match &cond.kind {
        ConditionKind::And { left, right }
        | ConditionKind::Or { left, right }
        | ConditionKind::Since { left, right, .. } => {
            validate_condition(left, schema)?;
            validate_condition(right, schema)
        }
        ConditionKind::Not { inner }
        | ConditionKind::Formerly { body: inner, .. }
        | ConditionKind::Previous { body: inner, .. }
        | ConditionKind::Exists { body: inner, .. } => validate_condition(inner, schema),
        ConditionKind::Predicate(p) => validate_predicate(p, schema),
        // A field-injection refinement is folded into its base predicate
        // by the macro expansion pass, so validation should never see one.
        // Defensive: recurse into the base so the base predicate (and thus
        // its own fields) still get checked if ordering ever changes.
        ConditionKind::Refine { base, .. } => validate_condition(base, schema),
        // A comparison operand may be an aggregate term whose `where` body
        // holds predicates; check those. Any other term has no predicate.
        ConditionKind::Comparison { left, right, .. } => {
            validate_term(left, schema)?;
            validate_term(right, schema)
        }
        // Leaves with no predicate to check.
        ConditionKind::Tp { .. } | ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => {
            Ok(())
        }
    }
}

/// Check the predicates inside a term: an aggregate term descends into its
/// `where` body; any other term is a leaf.
fn validate_term(term: &Term, schema: &DerivedEventSchema) -> Result<(), String> {
    match term {
        Term::Agg(agg) => match &agg.kind {
            AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => {
                validate_condition(body, schema)
            }
            // A macro call should not survive to validation, but it carries
            // no predicate of its own to check.
            AggExprKind::Call(_) => Ok(()),
        },
        _ => Ok(()),
    }
}

fn validate_predicate(
    p: &crate::extension::temporal::ast::Predicate,
    schema: &DerivedEventSchema,
) -> Result<(), String> {
    use super::derive::PathLookup;

    let Some(event) = schema.get(&p.namespace, &p.action, &p.kind) else {
        let head = qualified_head(&p.namespace, &p.action, &p.kind);
        return Err(format!(
            "predicate `{head}` does not name a declared event \
             (no event kind `{}` derived for action `{}`)",
            p.kind, p.action
        ));
    };
    for arg in &p.args {
        // A field name is a dotted path (`input.user`); a bare name is a
        // single-segment path. It must resolve to a declared *leaf* — not a
        // field group (`input` alone) and not a missing path.
        let path = arg.field_path();
        match event.lookup_path(&path) {
            PathLookup::Leaf => {}
            PathLookup::Group => {
                let head = qualified_head(&p.namespace, &p.action, &p.kind);
                return Err(format!(
                    "predicate `{head}` mentions `{}`, which is a field group, not a field; \
                     address a field inside it (e.g. `{}.<field>`)",
                    arg.field_name(),
                    arg.field_name()
                ));
            }
            PathLookup::Absent => {
                let head = qualified_head(&p.namespace, &p.action, &p.kind);
                return Err(format!(
                    "predicate `{head}` mentions field `{}`, which is not declared on that event \
                     (declared fields: {})",
                    arg.field_name(),
                    event.declared_paths().join(", ")
                ));
            }
        }
    }
    Ok(())
}

/// Render a predicate head for error messages, e.g.
/// `Drupe::Action::"Login"::request`.
fn qualified_head(namespace: &[String], action: &str, kind: &str) -> String {
    if namespace.is_empty() {
        format!("\"{action}\"::{kind}")
    } else {
        format!("{}::\"{action}\"::{kind}", namespace.join("::"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event_schema::derive::derive;
    use crate::event_schema::parse::parse_event_schema;
    use crate::extension::temporal::parse::parse_condition;

    const RR_SCHEMA: &str = r#"
        decision event <A>::request {
            ...inputs(A),
            callerPrincipal: principalType(A),
            callerResource:  resourceType(A),
            requestId:       String,
        }
        event <A>::response {
            ...inputs(A),
            ...outputs(A),
            callerPrincipal: principalType(A),
            callerResource:  resourceType(A),
            requestId:       String,
        }
    "#;

    const ACTION_SCHEMA: &str = r#"
        namespace Drupe {
            entity OAuthUser = { id: String };
            entity Gateway;
            type LoginInput = { server: String, user: String };
            type LoginOutput = { result: Bool };
            action "Login" appliesTo {
                principal: [OAuthUser],
                resource: [Gateway],
                context: { input: LoginInput, output?: LoginOutput }
            };
        }
    "#;

    fn derived() -> DerivedEventSchema {
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        derive(&dsl, ACTION_SCHEMA).unwrap()
    }

    fn check(body: &str) -> Result<(), String> {
        let cond = parse_condition(body).expect("parses");
        validate_condition(&cond, &derived())
    }

    #[test]
    fn valid_predicate_with_declared_field_passes() {
        // Input fields are addressed under the `input` group.
        check(r#"Drupe::Action::"Login"::request{ input.user: u }"#).expect("valid");
    }

    #[test]
    fn omitted_field_is_legal() {
        // `input.server` and the reserved fields are omitted — omission is a
        // wildcard, not an error.
        check(r#"Drupe::Action::"Login"::request{ input.user: u }"#).expect("omission ok");
        // A predicate may even mention no fields at all.
        check(r#"Drupe::Action::"Login"::request{}"#).expect("empty ok");
    }

    #[test]
    fn reserved_injected_field_is_mentionable() {
        // `callerPrincipal` is injected as a top-level (flat) field, so a
        // policy may bind it by bare name.
        check(r#"Drupe::Action::"Login"::request{ callerPrincipal: p }"#)
            .expect("reserved field declared");
    }

    #[test]
    fn response_output_field_passes() {
        // Output fields are addressed under the `output` group.
        check(r#"Drupe::Action::"Login"::response{ output.result: r }"#).expect("output field");
    }

    #[test]
    fn old_unqualified_field_name_is_rejected() {
        // A bare `user` (the pre-nesting spelling) is no longer declared —
        // it must be written `input.user`. This proves the surface genuinely
        // moved and the migration is enforced, not optional.
        let e = check(r#"Drupe::Action::"Login"::request{ user: u }"#)
            .expect_err("bare input field name is rejected");
        assert!(e.contains("field `user`"), "{e}");
        assert!(e.contains("not declared"), "{e}");
        // The error lists the qualified path so the fix is discoverable.
        assert!(
            e.contains("input.user"),
            "declared paths should show input.user: {e}"
        );
    }

    #[test]
    fn addressing_a_field_group_without_a_leaf_is_an_error() {
        // `input` alone names a group, not a field.
        let e = check(r#"Drupe::Action::"Login"::request{ input: x }"#)
            .expect_err("group is not a field");
        assert!(e.contains("field group"), "{e}");
        assert!(e.contains("input"), "{e}");
    }

    #[test]
    fn output_field_on_request_is_error() {
        // `output.result` is an output field — present on the response, not
        // request (request has no `output` group at all).
        let e = check(r#"Drupe::Action::"Login"::request{ output.result: r }"#)
            .expect_err("request has no output group");
        assert!(e.contains("output.result"), "{e}");
        assert!(e.contains("not declared"), "{e}");
    }

    #[test]
    fn unknown_field_is_error() {
        let e =
            check(r#"Drupe::Action::"Login"::request{ input.usre: u }"#).expect_err("typo'd field");
        assert!(e.contains("input.usre"), "{e}");
    }

    #[test]
    fn unknown_action_is_error() {
        let e = check(r#"Drupe::Action::"Lgoin"::request{}"#).expect_err("bad action");
        assert!(e.contains("does not name a declared event"), "{e}");
    }

    #[test]
    fn unknown_kind_is_error() {
        let e = check(r#"Drupe::Action::"Login"::reqeust{}"#).expect_err("bad kind");
        assert!(e.contains("does not name a declared event"), "{e}");
        assert!(e.contains("reqeust"), "{e}");
    }

    #[test]
    fn predicate_under_temporal_op_and_aggregation_is_checked() {
        // The walk must reach predicates nested under formerly and inside
        // an aggregate operand of an `exists` comparison.
        let e = check(r#"formerly within 1h Drupe::Action::"Login"::request{ input.bad: x }"#)
            .expect_err("nested predicate checked");
        assert!(e.contains("input.bad"), "{e}");

        let e2 = check(
            r#"exists (n: Long). ((count for (t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{ input.bad: x } && tp(t)))) == n && n > 0)"#,
        )
        .expect_err("predicate inside aggregation checked");
        assert!(e2.contains("input.bad"), "{e2}");
    }

    #[test]
    fn negation_predicate_is_checked() {
        let e = check(r#"!Drupe::Action::"Login"::request{ input.bad: x }"#)
            .expect_err("predicate under ! checked");
        assert!(e.contains("input.bad"), "{e}");
    }

    // ─── Deep-path validation (facet 3) ─────────────────────────────

    /// A custom event schema with a deeply nested injected field
    /// (`meta.session.id`) alongside the stock request fields, validated
    /// against `ACTION_SCHEMA`.
    const NESTED_SCHEMA: &str = r#"
        decision event <A>::request {
            ...inputs(A),
            meta: { session: { id: String } },
            requestId: String,
        }
    "#;

    fn check_nested(body: &str) -> Result<(), String> {
        let dsl = parse_event_schema(NESTED_SCHEMA).unwrap();
        let derived = derive(&dsl, ACTION_SCHEMA).unwrap();
        let cond = parse_condition(body).expect("parses");
        validate_condition(&cond, &derived)
    }

    #[test]
    fn deep_leaf_path_passes() {
        check_nested(r#"Drupe::Action::"Login"::request{ meta.session.id: s }"#)
            .expect("depth-3 leaf is valid");
    }

    #[test]
    fn addressing_a_deep_intermediate_group_is_an_error() {
        // `meta.session` is a group (its leaf is `id`), not a field.
        let e = check_nested(r#"Drupe::Action::"Login"::request{ meta.session: x }"#)
            .expect_err("intermediate group rejected");
        assert!(e.contains("field group"), "{e}");
        assert!(e.contains("meta.session"), "{e}");
    }

    #[test]
    fn addressing_a_top_level_group_of_a_deep_field_is_an_error() {
        let e = check_nested(r#"Drupe::Action::"Login"::request{ meta: x }"#)
            .expect_err("top group rejected");
        assert!(e.contains("field group"), "{e}");
    }

    #[test]
    fn undeclared_deep_path_lists_declared_leaves() {
        // A typo in the deepest segment; the error should surface the real
        // declared leaf paths (including the deep one).
        let e = check_nested(r#"Drupe::Action::"Login"::request{ meta.session.zzz: x }"#)
            .expect_err("undeclared deep leaf");
        assert!(e.contains("meta.session.zzz"), "{e}");
        assert!(e.contains("meta.session.id"), "declared paths shown: {e}");
    }

    #[test]
    fn descending_through_a_leaf_is_an_error() {
        // `meta.session.id` is a leaf; `meta.session.id.more` descends into
        // a scalar — no such path, rejected (not a panic).
        let e = check_nested(r#"Drupe::Action::"Login"::request{ meta.session.id.more: x }"#)
            .expect_err("descend-through-leaf rejected");
        assert!(e.contains("meta.session.id.more"), "{e}");
        assert!(e.contains("not declared"), "{e}");
    }

    #[test]
    fn partial_deep_path_prefix_is_undeclared() {
        // A path that exists as a prefix but stops short at a non-group is
        // handled by the group/absent logic, not a crash. `input.user.x`
        // where `input.user` is a leaf → absent.
        let e = check_nested(r#"Drupe::Action::"Login"::request{ input.user.x: v }"#)
            .expect_err("descend into input.user leaf rejected");
        assert!(e.contains("input.user.x"), "{e}");
    }

    // ─── Deep predicate-arg fields from a nested ACTION-schema input ──
    //
    // The complement of the DSL-nesting tests above: here the nesting comes
    // from the *action schema's* input type (`ReadInput = { meta: Meta }`),
    // spliced by `...inputs(A)`. Before the derive fix, a record-typed input
    // member flattened to a single `input.meta` leaf, so a deep predicate arg
    // (`input.meta.region:`) failed the names check even though the deep
    // `context.input.meta.region` comparison path validated — the validator
    // asymmetry. These pin that a deep predicate arg now resolves.

    /// An action schema with a record-typed input member (`meta: Meta`) and a
    /// nested int leaf, validated against the stock request/response DSL.
    const NESTED_INPUT_ACTION: &str = r#"
        namespace Drupe {
            entity OAuthUser = { id: String };
            entity Gateway;
            type Meta = { region: String, level: Long };
            type ReadInput = { user: String, meta: Meta };
            action "Read" appliesTo {
                principal: [OAuthUser],
                resource: [Gateway],
                context: { input: ReadInput }
            };
        }
    "#;

    fn check_nested_input(body: &str) -> Result<(), String> {
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let derived = derive(&dsl, NESTED_INPUT_ACTION).unwrap();
        let cond = parse_condition(body).expect("parses");
        validate_condition(&cond, &derived)
    }

    #[test]
    fn deep_predicate_arg_from_nested_input_passes() {
        // `input.meta.region:` is now a declared leaf — the fix's headline.
        check_nested_input(r#"Drupe::Action::"Read"::request{ input.meta.region: r }"#)
            .expect("deep predicate arg from a nested input record is valid");
        // The nested int leaf too.
        check_nested_input(r#"Drupe::Action::"Read"::request{ input.meta.level: l }"#)
            .expect("deep int leaf valid");
    }

    #[test]
    fn record_typed_input_member_is_a_group_not_a_leaf() {
        // Addressing the record-typed member itself (`input.meta`) is now a
        // group error (it has leaves inside), not a silently-accepted leaf.
        let e = check_nested_input(r#"Drupe::Action::"Read"::request{ input.meta: x }"#)
            .expect_err("record member is a group");
        assert!(e.contains("field group"), "{e}");
        assert!(e.contains("input.meta"), "{e}");
    }

    #[test]
    fn undeclared_deep_input_leaf_is_rejected() {
        // A typo inside the nested record: the declared deep leaves are shown.
        let e = check_nested_input(r#"Drupe::Action::"Read"::request{ input.meta.zzz: x }"#)
            .expect_err("undeclared deep input leaf");
        assert!(e.contains("input.meta.zzz"), "{e}");
        assert!(e.contains("input.meta.region"), "declared paths shown: {e}");
    }
}
