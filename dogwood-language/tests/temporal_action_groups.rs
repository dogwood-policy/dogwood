//! An `action in [Group]` scope reaches the group's MEMBER actions, transitively.
//!
//! Cedar treats an action group as a shorthand for its members: a policy scoped
//! `action in [Group]` is validated against every request environment the members admit,
//! and the group action itself contributes none (a group typically declares no `appliesTo`,
//! so it has no principal, resource or context of its own). Two obligations follow for the
//! temporal dialect:
//!
//! 1. **Resolve against members, not the group.** `context.<path>` and `principal.<attr>`
//!    in a group-scoped condition must resolve against each member's declared types. A
//!    condition wrong for any member is rejected; one right for all members is accepted.
//! 2. **The hoisted field must live where the policy is evaluated.** A temporal leaf becomes
//!    a `context.<id>` boolean in the augmented schema. Cedar checks the policy against the
//!    MEMBERS, so the field has to be declared on the members — declaring it on the group
//!    makes Cedar report it missing on every member, and a perfectly correct policy fails.
//!
//! Both obligations are currently unmet, and the second is fail-CLOSED rather than
//! fail-open: a correct group-scoped temporal policy cannot be written at all. It is
//! nonetheless a real defect, and it is measurably inconsistent — the same policy EVALUATES
//! correctly (see `a_group_scoped_cap_fires_for_member_actions`), so validation and
//! evaluation disagree about the same source.
//!
//! # How to read this file
//!
//! Same discipline as `temporal_request_envs.rs`: every case is a PAIR, `cedar_witness_*`
//! first, asserting what **Cedar** does, then `temporal_*` asserting the temporal dialect
//! agrees. Witnesses go through Dogwood's own pipeline rather than calling
//! `cedar_policy_core`, so they exercise schema and policy as a user's would — and if a
//! future Cedar changes how it expands groups, the witness goes red beside the temporal
//! test it justifies.

use dogwood_language::{
    Authorizer, LoweredPolicySet, PolicySchema, ServiceSchema, Validator, parse_trace,
};

/// A two-level action hierarchy, members that disagree about types, and two degenerate
/// groups.
///
/// - `All` contains `Reads` (itself a group) and `Write`, so `in [All]` must expand TWO
///   levels to reach `Read` and `Peek`.
/// - `amount` is `Long` on `Read`/`Write` and `String` on `Peek`, so a comparison can be
///   right for some members and wrong for another.
/// - `tag` is `String` on every member, so a comparison against it is right everywhere —
///   this is the case that must be ACCEPTED, and is what the hoisting defect breaks.
/// - `Peek` admits `Partner`, which declares no `tier`, so the principal axis has a subset
///   shape reachable only through group expansion.
/// - `Empty` is a group no action declares membership in.
/// - `Solo` is an ordinary action outside the hierarchy, for mixed lists.
/// - `readonly` is declared on `Read` ONLY, so a group-scoped read of it fails on the
///   PATH rather than on the type — a distinct failure mode from a type mismatch.
/// - The members also declare a `system` context group: `system.seq` is `Long` on `Read`
///   and `String` on `Peek`, `system.now` is `String` on both. Group expansion must reach
///   non-`input` context groups identically.
/// - `Hub` is BOTH appliable and a group (it declares `appliesTo` and `Spoke` is its
///   member), so `in [Hub]` admits `Hub` itself alongside `Spoke`.
const SCHEMA: &str = r#"namespace W {
  type LongIn = { amount: Long, tag: String };
  type StrIn  = { amount: String, tag: String };
  type ReadIn = { amount: Long, tag: String, readonly: Long };

  entity Gateway;
  entity Staff   = { id: String, tier: Long };
  entity Partner = { id: String };

  action "All";
  action "Reads" in [All];
  action "Empty";

  action "Read" in [Reads] appliesTo {
    principal: [Staff], resource: [Gateway],
    context: { input: ReadIn, system: { now: String, seq: Long } } };
  action "Peek" in [Reads] appliesTo {
    principal: [Staff, Partner], resource: [Gateway],
    context: { input: StrIn, system: { now: String, seq: String } } };
  action "Write" in [All] appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: LongIn } };
  action "Solo" appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: LongIn } };

  action "Hub" in [All] appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: LongIn } };
  action "Spoke" in [Hub] appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: StrIn } };
}"#;

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

/// Distinctive fragments of the diagnostics these cases expect. Centralised so a reworded
/// message is a one-line edit; kept short so a rephrasing that means the same thing does not
/// churn the suite.
mod says {
    /// Cedar, comparing operands of incompatible types.
    pub const CEDAR_TYPE_MISMATCH: &str = "not compatible";
    /// Cedar, reading an attribute an entity type does not declare.
    pub const CEDAR_NO_ATTRIBUTE: &str = "not found";
    /// Cedar, on a scope no request environment can satisfy.
    pub const CEDAR_NO_APPLICABLE_ACTION: &str = "unable to find an applicable action";
    /// Temporal dialect, comparing operands of different types.
    pub const TEMPORAL_TYPE_MISMATCH: &str = "same type";
    /// Cedar, on an ORDERING comparison whose operand is not the expected type. Cedar words
    /// this differently from an equality mismatch — measured, not assumed.
    pub const CEDAR_EXPECTED_LONG: &str = "expected Long but saw String";
}

fn errors(src: &str) -> Vec<String> {
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    match LoweredPolicySet::from_str(src, &service, &schema) {
        Err(e) => vec![format!("LOWERING FAILED: {e:?}")],
        Ok(lowered) => Validator::new()
            .validate(&lowered)
            .validation_errors()
            .map(|e| format!("{e}"))
            .collect(),
    }
}

#[track_caller]
fn assert_rejects(what: &str, needle: &str, src: &str) {
    let errs = errors(src);
    assert!(
        !errs.is_empty(),
        "{what}: expected rejection, but it validated clean\n--- policy ---\n{src}"
    );
    assert!(
        !errs[0].starts_with("LOWERING FAILED"),
        "{what}: must be REJECTED BY VALIDATION, not unlowerable — the fixture is wrong\n{}",
        errs[0]
    );
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "{what}: rejected, but for the wrong reason — no diagnostic contains {needle:?}.\n\
         Got:\n  {}\n--- policy ---\n{src}",
        errs.join("\n  ")
    );
}

#[track_caller]
fn assert_accepts(what: &str, src: &str) {
    let errs = errors(src);
    assert!(
        errs.is_empty(),
        "{what}: expected clean validation, got:\n  {}\n--- policy ---\n{src}",
        errs.join("\n  ")
    );
}

fn cedar(scope: &str, body: &str) -> String {
    format!("permit ({scope})\nwhen {{ {body} }};")
}

/// `body` sits inside the `formerly` scope so time-point dependence is satisfied by the
/// predicate. The predicate names a concrete event type, which is independent of the rule's
/// scope — `context.…` and `principal.…` refer to the CURRENT REQUEST, which the scope
/// constrains.
fn temporal(scope: &str, body: &str) -> String {
    format!(
        "permit ({scope})\nwhen temporal {{ formerly within 1h \
         (W::Action::\"Read\"::request{{}} && {body}) }};"
    )
}

// ═══════════════════════════════════════════════════════════════════════════
// 1. A group-scoped condition right for EVERY member is accepted
// ═══════════════════════════════════════════════════════════════════════════
// `tag` is String on Read and Peek, so this is correct in every environment the
// group admits. This is the case the hoisting defect breaks: the field is declared
// on `Reads`, and Cedar looks for it on `Read` and `Peek`.

#[test]
fn cedar_witness_group_scope_correct_for_all_members() {
    assert_accepts(
        "cedar: action in [Reads], tag is String on both members",
        &cedar(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn temporal_group_scope_correct_for_all_members() {
    assert_accepts(
        "temporal: action in [Reads], tag is String on both members",
        &temporal(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 2. A group-scoped condition wrong for ONE member is rejected
// ═══════════════════════════════════════════════════════════════════════════
// `amount` is Long on Read and String on Peek, so `== 5` is right for Read and
// wrong for Peek. An implementation that expanded to only the first member, or
// that resolved against the group action, would accept this.

#[test]
fn cedar_witness_group_scope_wrong_for_one_member() {
    assert_rejects(
        "cedar: action in [Reads], amount is Long on Read and String on Peek",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

#[test]
fn temporal_group_scope_wrong_for_one_member() {
    assert_rejects(
        "temporal: action in [Reads], amount is Long on Read and String on Peek",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 3. Expansion is TRANSITIVE through nested groups
// ═══════════════════════════════════════════════════════════════════════════
// `All` contains `Reads`, which contains `Read` and `Peek`. Reaching `Peek` needs
// two levels, so a one-level expansion would accept case 4 and pass case 3 for the
// wrong reason.

#[test]
fn cedar_witness_nested_group_correct_for_all() {
    assert_accepts(
        "cedar: action in [All], tag is String on every leaf member",
        &cedar(
            r#"principal, action in [W::Action::"All"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn temporal_nested_group_correct_for_all() {
    assert_accepts(
        "temporal: action in [All], tag is String on every leaf member",
        &temporal(
            r#"principal, action in [W::Action::"All"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

// ── 4. The discriminating negative for transitivity ───────────────────────
// `Peek` is reachable from `All` only through `Reads`. `amount == 5` is right for
// `Write` (a direct member) and for `Read`, and wrong ONLY for `Peek`. So this
// rejects if and only if expansion descended two levels.

#[test]
fn cedar_witness_nested_group_wrong_only_at_depth_two() {
    assert_rejects(
        "cedar: action in [All], amount wrong only for Peek, two levels down",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"All"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

#[test]
fn temporal_nested_group_wrong_only_at_depth_two() {
    assert_rejects(
        "temporal: action in [All], amount wrong only for Peek, two levels down",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action in [W::Action::"All"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 5. Group expansion also widens the PRINCIPAL axis
// ═══════════════════════════════════════════════════════════════════════════
// `Peek` admits `Partner`, which declares no `tier`. That principal type is
// reachable only by expanding the group, so this catches an implementation that
// expands actions but takes principals from the group action (which has none) or
// from the first member alone.

#[test]
fn cedar_witness_group_scope_widens_principal_types() {
    assert_rejects(
        "cedar: action in [Reads] admits Partner via Peek, tier absent there",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_group_scope_widens_principal_types() {
    assert_rejects(
        "temporal: action in [Reads] admits Partner via Peek, tier absent there",
        "attribute `tier`",
        &temporal(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "principal.tier > 0",
        ),
    );
}

// ── 6. Narrowing the principal back makes it legitimate again ─────────────

#[test]
fn cedar_witness_group_scope_with_narrowed_principal() {
    assert_accepts(
        "cedar: action in [Reads] with principal is Staff",
        &cedar(
            r#"principal is W::Staff, action in [W::Action::"Reads"], resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_group_scope_with_narrowed_principal() {
    assert_accepts(
        "temporal: action in [Reads] with principal is Staff",
        &temporal(
            r#"principal is W::Staff, action in [W::Action::"Reads"], resource"#,
            "principal.tier > 0",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 7. A list mixing a group with a concrete action
// ═══════════════════════════════════════════════════════════════════════════
// The environment set is the union of the group's members and the concrete action.
// `Solo` types `amount` as Long, so a comparison wrong for `Peek` must still reject.

#[test]
fn cedar_witness_mixed_group_and_concrete_list() {
    assert_rejects(
        "cedar: action in [Reads, Solo], amount wrong for Peek",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"Reads", W::Action::"Solo"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

#[test]
fn temporal_mixed_group_and_concrete_list() {
    assert_rejects(
        "temporal: action in [Reads, Solo], amount wrong for Peek",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action in [W::Action::"Reads", W::Action::"Solo"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

// ── 8. And the accept side of the mixed list ──────────────────────────────

#[test]
fn cedar_witness_mixed_group_and_concrete_list_correct() {
    assert_accepts(
        "cedar: action in [Reads, Solo], tag is String everywhere",
        &cedar(
            r#"principal, action in [W::Action::"Reads", W::Action::"Solo"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn temporal_mixed_group_and_concrete_list_correct() {
    assert_accepts(
        "temporal: action in [Reads, Solo], tag is String everywhere",
        &temporal(
            r#"principal, action in [W::Action::"Reads", W::Action::"Solo"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 9. Degenerate groups
// ═══════════════════════════════════════════════════════════════════════════
// `Empty` is a group no action belongs to, so it admits no environment at all.
// Whatever Cedar reports, the temporal dialect must not contradict it: per the
// design, when no environment remains the temporal validator stays silent and lets
// Cedar own the diagnostic.

#[test]
fn cedar_witness_group_with_no_members() {
    assert_rejects(
        "cedar: action in [Empty], a group no action belongs to",
        says::CEDAR_NO_APPLICABLE_ACTION,
        &cedar(
            r#"principal, action in [W::Action::"Empty"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn temporal_group_with_no_members() {
    assert_rejects(
        "temporal: action in [Empty], a group no action belongs to",
        says::CEDAR_NO_APPLICABLE_ACTION,
        &temporal(
            r#"principal, action in [W::Action::"Empty"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

// ── 10. `action ==` a GROUP, rather than `action in` ──────────────────────
// Equality names the group action itself, which declares no `appliesTo`, so it
// admits no environment. This distinguishes `Eq` from `In` on a group uid — an
// implementation that treated them alike would expand the members here too.

#[test]
fn cedar_witness_action_eq_a_group() {
    assert_rejects(
        "cedar: action == Reads, the group itself is not appliable",
        says::CEDAR_NO_APPLICABLE_ACTION,
        &cedar(
            r#"principal, action == W::Action::"Reads", resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn temporal_action_eq_a_group() {
    assert_rejects(
        "temporal: action == Reads, the group itself is not appliable",
        says::CEDAR_NO_APPLICABLE_ACTION,
        &temporal(
            r#"principal, action == W::Action::"Reads", resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 11. Validation and EVALUATION must agree about the same source
// ═══════════════════════════════════════════════════════════════════════════
// The hoisting defect makes validation reject a group-scoped temporal policy while
// evaluation handles it correctly. That inconsistency is itself the bug: whichever
// way it is resolved, these two must not disagree.
//
// This test pins the evaluation half — a cap scoped to the GROUP fires for events of
// a MEMBER action — so a fix that "resolves" the disagreement by breaking evaluation
// would be caught here rather than silently shipped.

#[test]
fn a_group_scoped_cap_fires_for_member_actions() {
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let src = r#"permit (principal, action in [W::Action::"Reads"], resource);

forbid (principal, action in [W::Action::"Reads"], resource)
when temporal { (count for (t: Timepoint). where formerly within 1h
  (W::Action::"Read"::request{} && tp(t))) > 1 };"#;
    let lowered = LoweredPolicySet::from_str(src, &service, &schema).expect("policy lowers");
    let mut authorizer = Authorizer::new(lowered);

    let event = |ts: i64, n: usize| {
        format!(
            "@{ts} scope(principal: W::Staff::\"s\", resource: W::Gateway::\"gw\") \
             entities(W::Staff::\"s\": {{ id: \"s\", tier: 1 }}) \
             request_context(input: {{ amount: 10, tag: \"t\" }}) \
             W::Action::\"Read\"::request(input: {{ amount: 10, tag: \"t\" }}, \
             callerPrincipal: W::Staff::\"s\", callerResource: W::Gateway::\"gw\", \
             requestId: \"r{n}\")"
        )
    };
    let trace = format!("{}\n{}\n{}", event(0, 0), event(5, 1), event(10, 2));
    let events = parse_trace(&trace).expect("trace parses");

    let mut verdicts = Vec::new();
    for e in &events {
        if let Some(r) = authorizer.is_authorized(e) {
            verdicts.push(format!("{:?}", r.decision()));
        }
    }
    assert_eq!(
        verdicts,
        vec!["Allow", "Deny", "Deny"],
        "a cap scoped to the group must fire for events of its member action: the first \
         request is under the cap, the next two are over it"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 12. A field declared on only SOME members fails on the PATH, not the type
// ═══════════════════════════════════════════════════════════════════════════
// `readonly` exists on `Read` and not on `Peek`. Both are members of `Reads`, so a
// group-scoped read of it must be rejected — and for a different reason than case 2:
// there the field existed everywhere with the wrong type, here it does not exist at
// all in one environment. An implementation that resolved types but skipped path
// existence, or that stopped at the first member that resolved, would accept this.

#[test]
fn cedar_witness_group_field_on_only_some_members() {
    assert_rejects(
        "cedar: action in [Reads], readonly declared on Read but not Peek",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "context.input.readonly == 5",
        ),
    );
}

#[test]
fn temporal_group_field_on_only_some_members() {
    assert_rejects(
        "temporal: action in [Reads], readonly declared on Read but not Peek",
        "readonly",
        &temporal(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "context.input.readonly == 5",
        ),
    );
}

// ── 13. Narrowing to the declaring member makes the same read legitimate ───
// The accept twin of case 12, and the guard against over-rejecting: pinned to
// `Read` alone, `readonly` resolves.

#[test]
fn cedar_witness_member_scoped_field_resolves() {
    assert_accepts(
        "cedar: action == Read, readonly declared there",
        &cedar(
            r#"principal, action == W::Action::"Read", resource"#,
            "context.input.readonly == 5",
        ),
    );
}

#[test]
fn temporal_member_scoped_field_resolves() {
    assert_accepts(
        "temporal: action == Read, readonly declared there",
        &temporal(
            r#"principal, action == W::Action::"Read", resource"#,
            "context.input.readonly == 5",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 14. An action that is BOTH appliable and a group
// ═══════════════════════════════════════════════════════════════════════════
// `Hub` declares `appliesTo` AND has `Spoke` as a member, so `in [Hub]` admits Hub's
// own environment alongside Spoke's. `amount` is Long on Hub and String on Spoke, so
// `== 5` is right for the group action itself and wrong for its member.
//
// This is the case that separates "expand to members" from "expand to members AND
// keep the group when it is appliable". An implementation that replaced the group
// with its members would MISS Hub; one that ignored members would MISS Spoke. Only
// the union rejects here and accepts case 15.

#[test]
fn cedar_witness_appliable_group_includes_itself_and_members() {
    assert_rejects(
        "cedar: action in [Hub], amount is Long on Hub and String on Spoke",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"Hub"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

#[test]
fn temporal_appliable_group_includes_itself_and_members() {
    assert_rejects(
        "temporal: action in [Hub], amount is Long on Hub and String on Spoke",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action in [W::Action::"Hub"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

// ── 15. And its accept twin ───────────────────────────────────────────────

#[test]
fn cedar_witness_appliable_group_correct_for_itself_and_members() {
    assert_accepts(
        "cedar: action in [Hub], tag is String on Hub and Spoke",
        &cedar(
            r#"principal, action in [W::Action::"Hub"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn temporal_appliable_group_correct_for_itself_and_members() {
    assert_accepts(
        "temporal: action in [Hub], tag is String on Hub and Spoke",
        &temporal(
            r#"principal, action in [W::Action::"Hub"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

// ── 16. `action ==` an APPLIABLE group names only that action ─────────────
// Contrast with case 10, where `==` a non-appliable group admits nothing. `Hub` IS
// appliable, so `== Hub` admits exactly Hub's environment and NOT Spoke's — meaning
// `amount == 5`, wrong for Spoke, is correct here. An implementation that expanded
// members on `Eq` as well as `In` would wrongly reject this.

#[test]
fn cedar_witness_action_eq_appliable_group_excludes_members() {
    assert_accepts(
        "cedar: action == Hub, amount is Long on Hub; Spoke is not admitted",
        &cedar(
            r#"principal, action == W::Action::"Hub", resource"#,
            "context.input.amount == 5",
        ),
    );
}

#[test]
fn temporal_action_eq_appliable_group_excludes_members() {
    assert_accepts(
        "temporal: action == Hub, amount is Long on Hub; Spoke is not admitted",
        &temporal(
            r#"principal, action == W::Action::"Hub", resource"#,
            "context.input.amount == 5",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 17. An ordering comparison under a group scope
// ═══════════════════════════════════════════════════════════════════════════
// Every case above uses `==`. Ordering takes a different arm of the comparison
// check, so a group-scoped `>` against a field that is String in one member must
// also reject.

#[test]
fn cedar_witness_group_scope_ordering_comparison() {
    assert_rejects(
        "cedar: action in [Reads], ordering on amount which is String on Peek",
        says::CEDAR_EXPECTED_LONG,
        &cedar(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "context.input.amount > 3",
        ),
    );
}

#[test]
fn temporal_group_scope_ordering_comparison() {
    assert_rejects(
        "temporal: action in [Reads], ordering on amount which is String on Peek",
        "numeric",
        &temporal(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "context.input.amount > 3",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 18. The aggregation range-restrictor under a group scope
// ═══════════════════════════════════════════════════════════════════════════
// The fail-open shape the whole effort exists to close, reached through group
// expansion: a `Long` summand range-restricted against a field that is `String` in
// one member. At evaluation the summand binds a string, `sum` silently drops the
// row, the total is 0 whatever the window holds, and a `forbid` cap never fires.

#[test]
fn cedar_witness_group_scope_summand_restrictor() {
    assert_rejects(
        "cedar: action in [Reads], Long compared against amount which is String on Peek",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "5 == context.input.amount",
        ),
    );
}

#[test]
fn temporal_group_scope_summand_restrictor() {
    assert_rejects(
        "temporal: action in [Reads], Long summand restricted by a String field on Peek",
        says::TEMPORAL_TYPE_MISMATCH,
        &format!(
            r#"permit (principal, action in [W::Action::"Reads"], resource)
when temporal {{
  (sum a for (a: Long), (t: Timepoint). where formerly within 1h
    (W::Action::"Read"::request{{}} && tp(t) && a == context.input.amount)) > 0
}};"#
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 19. Group expansion reaches context groups OTHER than `input`
// ═══════════════════════════════════════════════════════════════════════════
// The context is an ordinary record and `input` is just one field of it. Expanding a
// group must resolve a non-`input` group against the members exactly the same way.

#[test]
fn cedar_witness_group_scope_non_input_context_mistyped() {
    assert_rejects(
        "cedar: action in [Reads], system.seq is Long on Read and String on Peek",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "context.system.seq == 5",
        ),
    );
}

#[test]
fn temporal_group_scope_non_input_context_mistyped() {
    assert_rejects(
        "temporal: action in [Reads], system.seq is Long on Read and String on Peek",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            "context.system.seq == 5",
        ),
    );
}

#[test]
fn cedar_witness_group_scope_non_input_context_correct() {
    assert_accepts(
        "cedar: action in [Reads], system.now is String on both members",
        &cedar(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            r#"context.system.now == "t""#,
        ),
    );
}

#[test]
fn temporal_group_scope_non_input_context_correct() {
    assert_accepts(
        "temporal: action in [Reads], system.now is String on both members",
        &temporal(
            r#"principal, action in [W::Action::"Reads"], resource"#,
            r#"context.system.now == "t""#,
        ),
    );
}
