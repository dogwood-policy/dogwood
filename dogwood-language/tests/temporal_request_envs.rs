//! Temporal validation agrees with Cedar about which request environments a rule reaches.
//!
//! A policy is validated against every **request environment** its scope admits — each a
//! (principal type, action, resource type) triple. A body that is wrong in any one of them
//! is rejected, because the rule can be evaluated in that environment. This holds whether
//! the scope pins one action or spans many, and whether it pins one principal type or
//! spans every type the action permits.
//!
//! Two consequences the cases below pin down:
//!
//! - **Widening the scope widens the obligation.** `action in [A, B]` must satisfy both A
//!   and B; a bare `action` must satisfy every action. Same for the principal axis.
//! - **Narrowing the scope narrows it back, and narrowing is checkable.** `principal is T`,
//!   `principal == T::"x"` and `principal in Group` each restrict which entity types can
//!   arrive, so an attribute only some types declare becomes legitimate — and, once
//!   narrowed, is type-checked against the type that remains.
//!
//! This matters because the failure is fail-OPEN. A comparison that is wrong for an
//! admissible environment is permanently false there, so the condition never holds, and a
//! permanently false `forbid` is a cap that silently never fires.
//!
//! # How to read this file
//!
//! Every case is a PAIR, witness first:
//!
//! 1. `cedar_witness_*` — the same schema shape as an ordinary Cedar `when` clause,
//!    asserting what **Cedar** does. An auditor can confirm "yes, Cedar treats it that way
//!    too" before reading our expectation of the temporal dialect.
//! 2. `temporal_*` — the same shape inside `when temporal { … }`, asserting the temporal
//!    dialect reaches the same verdict.
//!
//! Witnesses run Cedar through Dogwood's own pipeline (`LoweredPolicySet::from_str` then
//! `Validator::validate`) rather than calling `cedar_policy_core` directly, so they exercise
//! schema and policy exactly as a user's would.
//!
//! The pairing does double duty: it documents the semantics against a reference
//! implementation, and it makes a change in Cedar's own treatment a **test failure** rather
//! than a silent divergence — if a future Cedar stops rejecting one of these, its witness
//! goes red beside the temporal test it justifies.
//!
//! When a pair disagrees, the temporal side is the one to fix — unless the witness shows
//! Cedar ACCEPTS, in which case rejecting in the temporal dialect would be over-rejection.
//!
//! # Why the narrowing cases come in twos
//!
//! An accept-case alone cannot show WHY a policy was accepted: "the scope narrowed to a
//! type that declares the attribute" and "nothing was checked at all" both look clean. So
//! every narrowing case is followed by a DISCRIMINATING NEGATIVE — the same narrowing
//! scope, with a comparison that is wrong for the type the scope narrows to. That can only
//! be rejected if the narrowing genuinely resolved a type, so the pair together pins the
//! mechanism rather than the outcome.

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema, Validator};

/// Actions differ in their principal sets and in how they type `input.amount`, so a rule
/// spanning several of them spans genuinely different request environments.
///
/// - `amount` is `Long` on `Meter` and `String` on `Peek` — a comparison can be right for
///   one action and wrong for another.
/// - `tag` is `String` on both, so a comparison against it cannot be rescued by a path
///   check; only a TYPE check can reject it.
/// - `tier` is on `Staff` and `Bot` but NOT `Partner`, so `Peek`'s principal set has it on
///   only a subset.
/// - `Staff` and `Bot` are members of `Team`; `Partner` is not, so `in Team` narrows.
/// - `capacity` is on `Gateway` but NOT `Kiosk`, and `Wide` permits both, so the RESOURCE
///   axis has the same subset shape the principal axis has on `Peek`.
/// - `Gateway in [Zone]` and `Zone in [Region]` give a two-level membership chain, so
///   `in Region::"r1"` tests whether narrowing follows membership transitively.
/// - `Orphan` is a group type no entity declares membership in, so a scope `in Orphan::"o1"`
///   narrows to nothing at all.
/// - `Hue` is an enum entity type, which declares no attributes.
/// - The context has groups OTHER than `input`: `system.seq` is `Long` on `Meter` and
///   `String` on `Peek`, `system.now` is `String` on both, and `meta` exists only on
///   `Meter`. Nothing in the type path may treat `input` specially.
const SCHEMA: &str = r#"namespace W {
  type MeterIn = { amount: Long, tag: String, owner: W::Manager };
  type PeekIn  = { amount: String, tag: String };
  type PingIn  = { tag: Long };

  entity Team;
  entity Manager = { id: String };
  entity Region;
  entity Zone    in [Region];
  entity Orphan;
  entity Hue enum ["red", "green"];

  entity Staff   in [Team] = { id: String, tier: Long, dept: String };
  entity Bot     in [Team] = { id: String, tier: Long, dept: String };
  entity Partner           = { id: String, dept: String };

  entity Gateway in [Zone] = { id: String, region: String, capacity: Long };
  entity Kiosk             = { id: String, region: String };

  action "Meter" appliesTo {
    principal: [Staff], resource: [Gateway],
    context: { input: MeterIn, system: { now: String, seq: Long }, meta: { tag: String } }
  };
  action "Peek" appliesTo {
    principal: [Staff, Partner], resource: [Gateway],
    context: { input: PeekIn, system: { now: String, seq: String } }
  };
  action "Team" appliesTo {
    principal: [Staff, Bot], resource: [Gateway], context: { input: MeterIn }
  };
  action "Wide" appliesTo {
    principal: [Staff], resource: [Gateway, Kiosk], context: { input: MeterIn }
  };
  action "Enum" appliesTo {
    principal: [Hue], resource: [Gateway], context: { input: MeterIn }
  };
  action "Ping" appliesTo {
    principal: [Partner], resource: [Kiosk], context: { input: PingIn }
  };
}"#;

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

/// Validation errors for a policy source, or the lowering error if it does not get that far.
fn errors(src: &str) -> Vec<String> {
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    match LoweredPolicySet::from_str(src, &service, &schema) {
        // A lowering failure is not the rejection these tests are about; surface it
        // distinctly so a malformed test fixture cannot masquerade as a pass.
        Err(e) => vec![format!("LOWERING FAILED: {e:?}")],
        Ok(lowered) => Validator::new()
            .validate(&lowered)
            .validation_errors()
            .map(|e| format!("{e}"))
            .collect(),
    }
}

/// Distinctive fragments of the diagnostics these cases must produce.
///
/// Centralised on purpose. Asserting only that *something* objected lets a case pass on an
/// unrelated complaint — a window bound, a tp-dependence error, a fixture mistake — so each
/// case names the diagnostic it expects. Keeping the fragments here means a reworded message
/// is a one-line edit rather than an edit in every case.
///
/// Fragments are deliberately SHORT and avoid wording likely to be rephrased, so a message
/// that still says the same thing does not churn the suite. Where a missing attribute is
/// expected, the fragment includes the ATTRIBUTE NAME, which survives rewording of the
/// sentence around it.
mod says {
    /// Cedar, comparing two operands of incompatible types.
    pub const CEDAR_TYPE_MISMATCH: &str = "not compatible";
    /// Cedar, reading an attribute an entity type does not declare.
    pub const CEDAR_NO_ATTRIBUTE: &str = "not found";
    /// Temporal dialect, comparing two operands of different types.
    pub const TEMPORAL_TYPE_MISMATCH: &str = "same type";
    /// Cedar, on a scope no request environment can satisfy. Cedar treats this as a hard
    /// ERROR, not a warning — measured, having first assumed otherwise.
    pub const CEDAR_NO_APPLICABLE_ACTION: &str = "unable to find an applicable action";
}

/// Assert the policy is rejected, by a diagnostic containing `needle`.
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
        "{what}: expected clean validation, got:\n{}\n--- policy ---\n{src}",
        errs.join("\n")
    );
}

/// A Cedar `when` clause carrying `body`, under scope `scope`.
fn cedar(scope: &str, body: &str) -> String {
    format!("permit ({scope})\nwhen {{ {body} }};")
}

/// A temporal condition carrying `body` as a conjunct, under scope `scope`.
///
/// `body` is conjoined inside the `formerly` scope so the time-point dependence check is
/// satisfied by the predicate — the corpus 0735 idiom. The predicate names an event type,
/// which is independent of the rule's scope: `context.…` and `principal.…` in the body
/// refer to the CURRENT REQUEST, which is what the rule scope constrains.
/// A temporal policy whose predicate names `action` and carries `pattern`.
fn temporal_pattern_on(action: &str, pattern: &str) -> String {
    format!(
        "permit (principal, action == W::Action::\"{action}\", resource)\n\
         when temporal {{ formerly within 1h \
         (W::Action::\"{action}\"::request{{ {pattern} }}) }};"
    )
}

fn temporal(scope: &str, body: &str) -> String {
    format!(
        "permit ({scope})\nwhen temporal {{ formerly within 1h \
         (W::Action::\"Meter\"::request{{}} && {body}) }};"
    )
}

// ═══════════════════════════════════════════════════════════════════════════
// Action axis
// ═══════════════════════════════════════════════════════════════════════════

// ── 1. A concrete action typing the comparison wrongly ────────────────────
// The baseline: with one action pinned there is a single environment, and both
// dialects already resolve against it.

#[test]
fn cedar_witness_concrete_action_mistyped() {
    assert_rejects(
        "cedar: action == Meter, amount is Long, compared to a string",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action == W::Action::"Meter", resource"#,
            r#"context.input.amount == "x""#,
        ),
    );
}

#[test]
fn temporal_concrete_action_mistyped() {
    assert_rejects(
        "temporal: action == Meter, amount is Long, compared to a string",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action == W::Action::"Meter", resource"#,
            r#"context.input.amount == "x""#,
        ),
    );
}

// ── 2. A list action scope, wrong in EVERY listed action ──────────────────
// `tag` is String on both actions, so no path check can fire: only a type check
// can reject this.

#[test]
fn cedar_witness_action_list_mistyped_in_all() {
    assert_rejects(
        "cedar: action in [Meter, Peek], tag is String on both, compared to an int",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            "context.input.tag == 7",
        ),
    );
}

#[test]
fn temporal_action_list_mistyped_in_all() {
    assert_rejects(
        "temporal: action in [Meter, Peek], tag is String on both, compared to an int",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            "context.input.tag == 7",
        ),
    );
}

// ── 3. A list action scope, wrong in ONLY ONE listed action ───────────────
// `amount` is Long on Meter and String on Peek, so `== 5` is right for Meter and
// wrong for Peek. Cedar rejects because it fails in SOME environment.

#[test]
fn cedar_witness_action_list_mistyped_in_one() {
    assert_rejects(
        "cedar: action in [Meter, Peek], amount typed differently per action",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

#[test]
fn temporal_action_list_mistyped_in_one() {
    assert_rejects(
        "temporal: action in [Meter, Peek], amount typed differently per action",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

// ── 4. A bare action scope ────────────────────────────────────────────────
// Bare `action` means every action, so the same mistake must be caught.

#[test]
fn cedar_witness_bare_action_mistyped() {
    assert_rejects(
        "cedar: bare action, amount typed differently across actions",
        says::CEDAR_TYPE_MISMATCH,
        &cedar("principal, action, resource", "context.input.amount == 5"),
    );
}

#[test]
fn temporal_bare_action_mistyped() {
    assert_rejects(
        "temporal: bare action, amount typed differently across actions",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal("principal, action, resource", "context.input.amount == 5"),
    );
}

// ── 5. A list action scope that is CORRECT everywhere ─────────────────────
// The over-rejection guard for the action axis: `tag` is String on both actions,
// so comparing it to a string is right in every environment. Case 2 is this
// case's discriminating negative — same scope, same field, wrong literal type —
// so the pair shows the list scope is checked rather than waved through.

#[test]
fn cedar_witness_action_list_correct() {
    assert_accepts(
        "cedar: action in [Meter, Peek], tag compared to a string",
        &cedar(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn temporal_action_list_correct() {
    assert_accepts(
        "temporal: action in [Meter, Peek], tag compared to a string",
        &temporal(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Principal axis
// ═══════════════════════════════════════════════════════════════════════════

// ── 6. A bare principal where the attribute is on only SOME types ─────────
// `Peek` admits Staff and Partner; only Staff declares `tier`. Cedar names the
// entity type that lacks it.

#[test]
fn cedar_witness_bare_principal_attribute_on_subset() {
    assert_rejects(
        "cedar: bare principal on Peek, tier only on Staff",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal, action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_bare_principal_attribute_on_subset() {
    assert_rejects(
        "temporal: bare principal on Peek, tier only on Staff",
        "attribute `tier`",
        &temporal(
            r#"principal, action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

// ── 7. `principal is T` narrowing to a type that HAS the attribute ────────
// The sanctioned way to narrow. This must be ACCEPTED — rejecting it would remove
// the only spelling that makes case 6 fixable.

#[test]
fn cedar_witness_principal_is_narrows_to_declaring_type() {
    assert_accepts(
        "cedar: principal is Staff on Peek, tier declared on Staff",
        &cedar(
            r#"principal is W::Staff, action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_principal_is_narrows_to_declaring_type() {
    assert_accepts(
        "temporal: principal is Staff on Peek, tier declared on Staff",
        &temporal(
            r#"principal is W::Staff, action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

// ── 8. `principal is T` narrowing to a type that LACKS the attribute ──────

#[test]
fn cedar_witness_principal_is_narrows_to_lacking_type() {
    assert_rejects(
        "cedar: principal is Partner on Peek, tier NOT on Partner",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal is W::Partner, action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_principal_is_narrows_to_lacking_type() {
    assert_rejects(
        "temporal: principal is Partner on Peek, tier NOT on Partner",
        "attribute `tier`",
        &temporal(
            r#"principal is W::Partner, action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

// ── 9. `principal == uid` narrowing via the uid's entity type ─────────────

#[test]
fn cedar_witness_principal_eq_uid_narrows() {
    assert_accepts(
        "cedar: principal == Staff::\"s1\" on Peek",
        &cedar(
            r#"principal == W::Staff::"s1", action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_principal_eq_uid_narrows() {
    assert_accepts(
        "temporal: principal == Staff::\"s1\" on Peek",
        &temporal(
            r#"principal == W::Staff::"s1", action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

// ── 10. `principal in Group` narrowing via declared membership ────────────
// Membership is dynamic, but the TYPES reachable through it are static: only
// `Staff` and `Bot` are declared `in [Team]`, and `Partner` is not. So on `Peek`
// (Staff, Partner) this narrows to Staff, which declares `tier`.
//
// This is the case a hand-written narrowing table gets wrong — it is tempting to
// assume a group cannot be narrowed statically at all.

#[test]
fn cedar_witness_principal_in_group_narrows() {
    assert_accepts(
        "cedar: principal in Team::\"t1\" on Peek narrows away Partner",
        &cedar(
            r#"principal in W::Team::"t1", action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_principal_in_group_narrows() {
    assert_accepts(
        "temporal: principal in Team::\"t1\" on Peek narrows away Partner",
        &temporal(
            r#"principal in W::Team::"t1", action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

// ── 10b. DISCRIMINATING NEGATIVES for the three narrowing forms ───────────
// Each reuses the narrowing scope from cases 7, 9 and 10, but compares the narrowed
// type's attribute against the WRONG type: `tier` is `Long`, compared to a string.
// Accepting any of these would mean the narrowing did not actually resolve a type —
// which is exactly how an unchecked implementation passes cases 7, 9 and 10.

#[test]
fn cedar_witness_principal_is_narrowed_then_type_checked() {
    assert_rejects(
        "cedar: principal is Staff, tier is Long, compared to a string",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal is W::Staff, action == W::Action::"Peek", resource"#,
            r#"principal.tier == "x""#,
        ),
    );
}

#[test]
fn temporal_principal_is_narrowed_then_type_checked() {
    assert_rejects(
        "temporal: principal is Staff, tier is Long, compared to a string",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal is W::Staff, action == W::Action::"Peek", resource"#,
            r#"principal.tier == "x""#,
        ),
    );
}

#[test]
fn cedar_witness_principal_eq_uid_narrowed_then_type_checked() {
    assert_rejects(
        "cedar: principal == Staff::\"s1\", tier is Long, compared to a string",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal == W::Staff::"s1", action == W::Action::"Peek", resource"#,
            r#"principal.tier == "x""#,
        ),
    );
}

#[test]
fn temporal_principal_eq_uid_narrowed_then_type_checked() {
    assert_rejects(
        "temporal: principal == Staff::\"s1\", tier is Long, compared to a string",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal == W::Staff::"s1", action == W::Action::"Peek", resource"#,
            r#"principal.tier == "x""#,
        ),
    );
}

#[test]
fn cedar_witness_principal_in_group_narrowed_then_type_checked() {
    assert_rejects(
        "cedar: principal in Team::\"t1\" narrows to Staff, tier compared to a string",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal in W::Team::"t1", action == W::Action::"Peek", resource"#,
            r#"principal.tier == "x""#,
        ),
    );
}

#[test]
fn temporal_principal_in_group_narrowed_then_type_checked() {
    assert_rejects(
        "temporal: principal in Team::\"t1\" narrows to Staff, tier compared to a string",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal in W::Team::"t1", action == W::Action::"Peek", resource"#,
            r#"principal.tier == "x""#,
        ),
    );
}

// ── 11. `principal in Group` where a reachable type LACKS the attribute ───
// On `Team` (Staff, Bot) both are group members and both declare `tier`, so the
// group narrows nothing away. Using `dept`, declared on all three, is accepted;
// using an attribute absent from Bot must reject. `Bot` declares no `absent`.

#[test]
fn cedar_witness_principal_in_group_still_checks_members() {
    assert_rejects(
        "cedar: principal in Team::\"t1\" on Team action, attribute on no member",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal in W::Team::"t1", action == W::Action::"Team", resource"#,
            "principal.absent > 0",
        ),
    );
}

#[test]
fn temporal_principal_in_group_still_checks_members() {
    assert_rejects(
        "temporal: principal in Team::\"t1\" on Team action, attribute on no member",
        "attribute `absent`",
        &temporal(
            r#"principal in W::Team::"t1", action == W::Action::"Team", resource"#,
            "principal.absent > 0",
        ),
    );
}

// ── 12. An attribute declared on EVERY permitted type ─────────────────────
// Over-rejection guard for the principal axis: `dept` is on Staff, Bot and
// Partner, so a bare principal is fine in every environment.

#[test]
fn cedar_witness_bare_principal_attribute_on_all() {
    assert_accepts(
        "cedar: bare principal on Peek, dept on both types",
        &cedar(
            r#"principal, action == W::Action::"Peek", resource"#,
            r#"principal.dept == "eng""#,
        ),
    );
}

#[test]
fn temporal_bare_principal_attribute_on_all() {
    assert_accepts(
        "temporal: bare principal on Peek, dept on both types",
        &temporal(
            r#"principal, action == W::Action::"Peek", resource"#,
            r#"principal.dept == "eng""#,
        ),
    );
}

// ── 13. An attribute declared on NO permitted type ────────────────────────

#[test]
fn cedar_witness_attribute_on_no_type() {
    assert_rejects(
        "cedar: principal.nope on Peek",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal, action == W::Action::"Peek", resource"#,
            r#"principal.nope == "x""#,
        ),
    );
}

#[test]
fn temporal_attribute_on_no_type() {
    assert_rejects(
        "temporal: principal.nope on Peek",
        "attribute `nope`",
        &temporal(
            r#"principal, action == W::Action::"Peek", resource"#,
            r#"principal.nope == "x""#,
        ),
    );
}

// ── 14. The entity-reference projections are strings ──────────────────────

#[test]
fn cedar_witness_id_projection_is_a_string() {
    assert_rejects(
        "cedar: principal.id compared to an int",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action == W::Action::"Peek", resource"#,
            "principal.id == 7",
        ),
    );
}

#[test]
fn temporal_id_projection_is_a_string() {
    assert_rejects(
        "temporal: principal.id compared to an int",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action == W::Action::"Peek", resource"#,
            "principal.id == 7",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Both axes at once
// ═══════════════════════════════════════════════════════════════════════════

// ── 15. A wide scope on both axes, wrong in some environment ──────────────
// Bare principal AND bare action: every environment in the schema. `tier` is
// absent from Partner, so some environment fails.

#[test]
fn cedar_witness_both_axes_wide() {
    assert_rejects(
        "cedar: bare principal and bare action, tier absent from Partner",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar("principal, action, resource", "principal.tier > 0"),
    );
}

#[test]
fn temporal_both_axes_wide() {
    assert_rejects(
        "temporal: bare principal and bare action, tier absent from Partner",
        "attribute `tier`",
        &temporal("principal, action, resource", "principal.tier > 0"),
    );
}

// ── 16. Narrowed on both axes, correct there ──────────────────────────────
// The combination that must keep working: narrow the principal to the declaring
// type and pin the action, and everything resolves.

#[test]
fn cedar_witness_both_axes_narrowed() {
    assert_accepts(
        "cedar: principal is Staff, action == Meter, amount is Long",
        &cedar(
            r#"principal is W::Staff, action == W::Action::"Meter", resource"#,
            "context.input.amount == 5 && principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_both_axes_narrowed() {
    assert_accepts(
        "temporal: principal is Staff, action == Meter, amount is Long",
        &temporal(
            r#"principal is W::Staff, action == W::Action::"Meter", resource"#,
            "context.input.amount == 5 && principal.tier > 0",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 17. `principal is T in G` — the fifth principal shape
// ═══════════════════════════════════════════════════════════════════════════
// Only the `is` half narrows on the TYPE axis; the `in` half constrains which
// instances arrive, not which types. So this must behave like `is` alone. It is the
// shape a converter written with a catch-all would silently degrade to `Any`.

#[test]
fn cedar_witness_principal_is_in_narrows_by_the_is_half() {
    assert_accepts(
        "cedar: principal is Staff in Team::\"t1\" on Peek, tier on Staff",
        &cedar(
            r#"principal is W::Staff in W::Team::"t1", action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_principal_is_in_narrows_by_the_is_half() {
    assert_accepts(
        "temporal: principal is Staff in Team::\"t1\" on Peek, tier on Staff",
        &temporal(
            r#"principal is W::Staff in W::Team::"t1", action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

// Its discriminating negative: narrowed to Staff, so `tier` must be type-checked.
#[test]
fn cedar_witness_principal_is_in_narrowed_then_type_checked() {
    assert_rejects(
        "cedar: principal is Staff in Team, tier is Long, compared to a string",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal is W::Staff in W::Team::"t1", action == W::Action::"Peek", resource"#,
            r#"principal.tier == "x""#,
        ),
    );
}

#[test]
fn temporal_principal_is_in_narrowed_then_type_checked() {
    assert_rejects(
        "temporal: principal is Staff in Team, tier is Long, compared to a string",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal is W::Staff in W::Team::"t1", action == W::Action::"Peek", resource"#,
            r#"principal.tier == "x""#,
        ),
    );
}

// `is Partner in Team` is UNSATISFIABLE: `Partner` is not declared a member of `Team`, so
// no request environment matches the scope at all. Cedar reports that as a hard ERROR
// ("unable to find an applicable action given the policy scope constraints") rather than a
// warning — measured, having first expected an attribute error, then a clean pass.
//
// This is the case the design leans on: when no environment remains, the temporal validator
// stays SILENT and lets Cedar own the diagnostic. The policy is still rejected, so silence
// costs nothing and cannot contradict Cedar.
#[test]
fn cedar_witness_principal_is_in_unsatisfiable_scope() {
    assert_rejects(
        "cedar: principal is Partner in Team is unsatisfiable",
        says::CEDAR_NO_APPLICABLE_ACTION,
        &cedar(
            r#"principal is W::Partner in W::Team::"t1", action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_principal_is_in_unsatisfiable_scope() {
    assert_rejects(
        "temporal: principal is Partner in Team is unsatisfiable (Cedar rejects it)",
        says::CEDAR_NO_APPLICABLE_ACTION,
        &temporal(
            r#"principal is W::Partner in W::Team::"t1", action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 18. The RESOURCE axis — same shapes, other variable
// ═══════════════════════════════════════════════════════════════════════════
// `Wide` permits Gateway and Kiosk; `capacity` is on Gateway only. An
// implementation that resolved the resource axis against principals, or inverted
// the two, would pass every test above and fail these.

#[test]
fn cedar_witness_bare_resource_attribute_on_subset() {
    assert_rejects(
        "cedar: bare resource on Wide, capacity only on Gateway",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal, action == W::Action::"Wide", resource"#,
            "resource.capacity > 0",
        ),
    );
}

#[test]
fn temporal_bare_resource_attribute_on_subset() {
    assert_rejects(
        "temporal: bare resource on Wide, capacity only on Gateway",
        "attribute `capacity`",
        &temporal(
            r#"principal, action == W::Action::"Wide", resource"#,
            "resource.capacity > 0",
        ),
    );
}

#[test]
fn cedar_witness_resource_is_narrows() {
    assert_accepts(
        "cedar: resource is Gateway on Wide, capacity on Gateway",
        &cedar(
            r#"principal, action == W::Action::"Wide", resource is W::Gateway"#,
            "resource.capacity > 0",
        ),
    );
}

#[test]
fn temporal_resource_is_narrows() {
    assert_accepts(
        "temporal: resource is Gateway on Wide, capacity on Gateway",
        &temporal(
            r#"principal, action == W::Action::"Wide", resource is W::Gateway"#,
            "resource.capacity > 0",
        ),
    );
}

// Discriminating negative for the resource narrowing.
#[test]
fn cedar_witness_resource_is_narrowed_then_type_checked() {
    assert_rejects(
        "cedar: resource is Gateway, capacity is Long, compared to a string",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action == W::Action::"Wide", resource is W::Gateway"#,
            r#"resource.capacity == "x""#,
        ),
    );
}

#[test]
fn temporal_resource_is_narrowed_then_type_checked() {
    assert_rejects(
        "temporal: resource is Gateway, capacity is Long, compared to a string",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action == W::Action::"Wide", resource is W::Gateway"#,
            r#"resource.capacity == "x""#,
        ),
    );
}

#[test]
fn cedar_witness_resource_eq_uid_narrows() {
    assert_accepts(
        "cedar: resource == Gateway::\"g1\" on Wide",
        &cedar(
            r#"principal, action == W::Action::"Wide", resource == W::Gateway::"g1""#,
            "resource.capacity > 0",
        ),
    );
}

#[test]
fn temporal_resource_eq_uid_narrows() {
    assert_accepts(
        "temporal: resource == Gateway::\"g1\" on Wide",
        &temporal(
            r#"principal, action == W::Action::"Wide", resource == W::Gateway::"g1""#,
            "resource.capacity > 0",
        ),
    );
}

// An attribute on EVERY permitted resource type: the resource-axis over-rejection guard.
#[test]
fn cedar_witness_bare_resource_attribute_on_all() {
    assert_accepts(
        "cedar: bare resource on Wide, region on both types",
        &cedar(
            r#"principal, action == W::Action::"Wide", resource"#,
            r#"resource.region == "eu""#,
        ),
    );
}

#[test]
fn temporal_bare_resource_attribute_on_all() {
    assert_accepts(
        "temporal: bare resource on Wide, region on both types",
        &temporal(
            r#"principal, action == W::Action::"Wide", resource"#,
            r#"resource.region == "eu""#,
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 19. A single-element action list
// ═══════════════════════════════════════════════════════════════════════════
// `action in [X]` is a distinct constraint shape from `action == X`, and pins the
// same single environment set. It must behave identically.

#[test]
fn cedar_witness_single_element_action_list() {
    assert_rejects(
        "cedar: action in [Meter], amount is Long, compared to a string",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"Meter"], resource"#,
            r#"context.input.amount == "x""#,
        ),
    );
}

#[test]
fn temporal_single_element_action_list() {
    assert_rejects(
        "temporal: action in [Meter], amount is Long, compared to a string",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action in [W::Action::"Meter"], resource"#,
            r#"context.input.amount == "x""#,
        ),
    );
}

// And its accept side: `amount` compared to an int is right for Meter alone.
#[test]
fn cedar_witness_single_element_action_list_correct() {
    assert_accepts(
        "cedar: action in [Meter], amount compared to an int",
        &cedar(
            r#"principal, action in [W::Action::"Meter"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

#[test]
fn temporal_single_element_action_list_correct() {
    assert_accepts(
        "temporal: action in [Meter], amount compared to an int",
        &temporal(
            r#"principal, action in [W::Action::"Meter"], resource"#,
            "context.input.amount == 5",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 20. Environments are a UNION across a list, not a per-axis intersection
// ═══════════════════════════════════════════════════════════════════════════
// `Meter` permits [Staff]; `Peek` permits [Staff, Partner]. So `action in [Meter,
// Peek]` admits Partner via Peek, and `principal.tier` — absent from Partner —
// must reject. An implementation that intersected the principal sets across the
// list would see only Staff and wrongly accept.

#[test]
fn cedar_witness_action_list_unions_principal_types() {
    assert_rejects(
        "cedar: action in [Meter, Peek] admits Partner via Peek, tier absent there",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_action_list_unions_principal_types() {
    assert_rejects(
        "temporal: action in [Meter, Peek] admits Partner via Peek, tier absent there",
        "attribute `tier`",
        &temporal(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            "principal.tier > 0",
        ),
    );
}

// The mirror: `action in [Meter, Team]` admits Staff and Bot, both declaring `tier`.
#[test]
fn cedar_witness_action_list_union_all_declare() {
    assert_accepts(
        "cedar: action in [Meter, Team], tier on Staff and Bot",
        &cedar(
            r#"principal, action in [W::Action::"Meter", W::Action::"Team"], resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_action_list_union_all_declare() {
    assert_accepts(
        "temporal: action in [Meter, Team], tier on Staff and Bot",
        &temporal(
            r#"principal, action in [W::Action::"Meter", W::Action::"Team"], resource"#,
            "principal.tier > 0",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 21. Mixed narrowing across the two axes
// ═══════════════════════════════════════════════════════════════════════════
// The diagonals: one axis wide, the other narrow. Neither axis may leak into the
// other's obligation.

#[test]
fn cedar_witness_bare_action_narrowed_principal() {
    assert_accepts(
        "cedar: bare action, principal is Staff, tier on Staff",
        &cedar(
            "principal is W::Staff, action, resource",
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_bare_action_narrowed_principal() {
    assert_accepts(
        "temporal: bare action, principal is Staff, tier on Staff",
        &temporal(
            "principal is W::Staff, action, resource",
            "principal.tier > 0",
        ),
    );
}

#[test]
fn cedar_witness_narrowed_action_bare_principal() {
    assert_rejects(
        "cedar: action == Peek, bare principal, tier absent from Partner",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal, action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_narrowed_action_bare_principal() {
    assert_rejects(
        "temporal: action == Peek, bare principal, tier absent from Partner",
        "attribute `tier`",
        &temporal(
            r#"principal, action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 22. Membership depth, empty narrowing, and enum entity types
// ═══════════════════════════════════════════════════════════════════════════
// `Gateway in [Zone]` and `Zone in [Region]`: does narrowing follow membership
// TRANSITIVELY? The witness decides; whatever Cedar does, the temporal dialect
// must match.

#[test]
fn cedar_witness_transitive_group_membership() {
    assert_accepts(
        "cedar: resource in Region::\"r1\" on Wide, Gateway -> Zone -> Region",
        &cedar(
            r#"principal, action == W::Action::"Wide", resource in W::Region::"r1""#,
            "resource.capacity > 0",
        ),
    );
}

#[test]
fn temporal_transitive_group_membership() {
    assert_accepts(
        "temporal: resource in Region::\"r1\" on Wide, Gateway -> Zone -> Region",
        &temporal(
            r#"principal, action == W::Action::"Wide", resource in W::Region::"r1""#,
            "resource.capacity > 0",
        ),
    );
}

// A group type no entity declares membership in narrows to NOTHING, so no environment
// remains — and Cedar rejects for the same reason as the case above. Confirms the design
// decision from the other direction: the temporal validator says nothing here, and the
// policy is rejected anyway.
#[test]
fn cedar_witness_group_with_no_members() {
    assert_rejects(
        "cedar: principal in Orphan::\"o1\", a group nothing belongs to",
        says::CEDAR_NO_APPLICABLE_ACTION,
        &cedar(
            r#"principal in W::Orphan::"o1", action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_group_with_no_members() {
    assert_rejects(
        "temporal: principal in Orphan::\"o1\", a group nothing belongs to",
        says::CEDAR_NO_APPLICABLE_ACTION,
        &temporal(
            r#"principal in W::Orphan::"o1", action == W::Action::"Peek", resource"#,
            "principal.tier > 0",
        ),
    );
}

// An enum entity type declares no attributes at all, so reading one must reject
// rather than resolve to nothing.
#[test]
fn cedar_witness_enum_entity_has_no_attributes() {
    assert_rejects(
        "cedar: principal.tier on an enum entity type",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal, action == W::Action::"Enum", resource"#,
            "principal.tier > 0",
        ),
    );
}

#[test]
fn temporal_enum_entity_has_no_attributes() {
    assert_rejects(
        "temporal: principal.tier on an enum entity type",
        "attribute `tier`",
        &temporal(
            r#"principal, action == W::Action::"Enum", resource"#,
            "principal.tier > 0",
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 23. Context groups OTHER than `input`
// ═══════════════════════════════════════════════════════════════════════════
// Every case above reads `context.input.*`. The context is an ordinary record and
// `input` is just one of its fields, so a non-`input` group must be resolved and
// type-checked identically. An implementation that reached the context through an
// `input`-specific helper would pass everything above and fail these.

#[test]
fn cedar_witness_non_input_context_group_mistyped() {
    assert_rejects(
        "cedar: action in [Meter, Peek], system.seq is Long on Meter and String on Peek",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            "context.system.seq == 5",
        ),
    );
}

#[test]
fn temporal_non_input_context_group_mistyped() {
    assert_rejects(
        "temporal: action in [Meter, Peek], system.seq is Long on Meter and String on Peek",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            "context.system.seq == 5",
        ),
    );
}

// Its accept twin: `system.now` is String on both actions.
#[test]
fn cedar_witness_non_input_context_group_correct() {
    assert_accepts(
        "cedar: action in [Meter, Peek], system.now is String on both",
        &cedar(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            r#"context.system.now == "t""#,
        ),
    );
}

#[test]
fn temporal_non_input_context_group_correct() {
    assert_accepts(
        "temporal: action in [Meter, Peek], system.now is String on both",
        &temporal(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            r#"context.system.now == "t""#,
        ),
    );
}

// A non-`input` group declared on only ONE listed action fails on the PATH.
#[test]
fn cedar_witness_non_input_context_group_on_one_action() {
    assert_rejects(
        "cedar: action in [Meter, Peek], meta declared only on Meter",
        says::CEDAR_NO_ATTRIBUTE,
        &cedar(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            r#"context.meta.tag == "t""#,
        ),
    );
}

#[test]
fn temporal_non_input_context_group_on_one_action() {
    assert_rejects(
        "temporal: action in [Meter, Peek], meta declared only on Meter",
        "context field `meta`",
        &temporal(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            r#"context.meta.tag == "t""#,
        ),
    );
}

// And a non-`input` group as an aggregation summand's restrictor — the fail-open
// shape, reached through a context group other than `input`.
#[test]
fn cedar_witness_non_input_group_summand_restrictor() {
    assert_rejects(
        "cedar: Long compared against system.seq which is String on Peek",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action in [W::Action::"Meter", W::Action::"Peek"], resource"#,
            "5 == context.system.seq",
        ),
    );
}

#[test]
fn temporal_non_input_group_summand_restrictor() {
    assert_rejects(
        "temporal: Long summand restricted by system.seq which is String on Peek",
        says::TEMPORAL_TYPE_MISMATCH,
        r#"permit (principal, action in [W::Action::"Meter", W::Action::"Peek"], resource)
when temporal {
  (sum a for (a: Long), (t: Timepoint). where formerly within 1h
    (W::Action::"Meter"::request{} && tp(t) && a == context.system.seq)) > 0
};"#,
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 24. The two axes must INTERACT: narrowing one removes whole ACTIONS
// ═══════════════════════════════════════════════════════════════════════════
// Cedar filters whole (principal, action, resource) triples by the policy scope and
// never typechecks an action for which no triple survives. So narrowing the
// PRINCIPAL must remove an action whose principals exclude it — otherwise that
// action's resource types and context record are held against a condition the rule
// can never be evaluated on.
//
// `Ping` permits only `Partner` / `Kiosk`. A rule narrowed to `principal is Staff`
// can never fire on it, so `Ping`'s input record must not be consulted. Fixing each
// axis separately does NOT produce this: it needs the two to interact.

#[test]
fn cedar_witness_narrowed_principal_removes_whole_actions() {
    assert_accepts(
        "cedar: principal is Staff + bare action; Ping excludes Staff",
        &cedar(
            "principal is W::Staff, action, resource",
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn temporal_narrowed_principal_removes_whole_actions() {
    assert_accepts(
        "temporal: principal is Staff + bare action; Ping excludes Staff",
        &temporal(
            "principal is W::Staff, action, resource",
            r#"context.input.tag == "x""#,
        ),
    );
}

// The mirror on the resource axis, and via a uid rather than `is`.
#[test]
fn cedar_witness_narrowed_resource_removes_whole_actions() {
    assert_accepts(
        "cedar: resource is Gateway + bare action; Ping's resource is Kiosk",
        &cedar(
            "principal, action, resource is W::Gateway",
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn temporal_narrowed_resource_removes_whole_actions() {
    assert_accepts(
        "temporal: resource is Gateway + bare action; Ping's resource is Kiosk",
        &temporal(
            "principal, action, resource is W::Gateway",
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn cedar_witness_narrowed_principal_uid_removes_whole_actions() {
    assert_accepts(
        "cedar: principal == Staff::\"s1\" + bare action",
        &cedar(
            r#"principal == W::Staff::"s1", action, resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

#[test]
fn temporal_narrowed_principal_uid_removes_whole_actions() {
    assert_accepts(
        "temporal: principal == Staff::\"s1\" + bare action",
        &temporal(
            r#"principal == W::Staff::"s1", action, resource"#,
            r#"context.input.tag == "x""#,
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 25. A bare scope root types even when several entity types are permitted
// ═══════════════════════════════════════════════════════════════════════════
// `principal` used to type only when the action permitted EXACTLY ONE entity type. With
// several it typed as nothing — and every comparison check is guarded on both operands
// having a type, so an entity compared against a STRING or an INT went unreported. That
// is a genuine type error which Cedar rejects, so it was fail-open, and it was reachable
// simply by adding a second principal type to an action.
//
// A bare root now types as the UNTAGGED `entity` when several are permitted: whichever
// arrives, it IS an entity. Narrowing the rule's scope back to one type yields the
// tagged form.

#[test]
fn cedar_witness_entity_root_against_a_string_is_rejected() {
    assert_rejects(
        "cedar: bare principal on Peek (two types) compared to a string",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action == W::Action::"Peek", resource"#,
            r#"principal == "alice""#,
        ),
    );
}

#[test]
fn temporal_entity_root_against_a_string_is_rejected() {
    assert_rejects(
        "temporal: bare principal on Peek (two types) compared to a string",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action == W::Action::"Peek", resource"#,
            r#"principal == "alice""#,
        ),
    );
}

#[test]
fn cedar_witness_entity_root_against_an_int_is_rejected() {
    assert_rejects(
        "cedar: bare principal on Peek compared to an int",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal, action == W::Action::"Peek", resource"#,
            "principal == 5",
        ),
    );
}

#[test]
fn temporal_entity_root_against_an_int_is_rejected() {
    assert_rejects(
        "temporal: bare principal on Peek compared to an int",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal, action == W::Action::"Peek", resource"#,
            "principal == 5",
        ),
    );
}

// Narrowing must not lose the check either — this was accepted before, because the
// bare-root arm ignored the rule's scope entirely.
#[test]
fn cedar_witness_narrowed_entity_root_against_a_string_is_rejected() {
    assert_rejects(
        "cedar: principal is Staff on Peek, compared to a string",
        says::CEDAR_TYPE_MISMATCH,
        &cedar(
            r#"principal is W::Staff, action == W::Action::"Peek", resource"#,
            r#"principal == "alice""#,
        ),
    );
}

#[test]
fn temporal_narrowed_entity_root_against_a_string_is_rejected() {
    assert_rejects(
        "temporal: principal is Staff on Peek, compared to a string",
        says::TEMPORAL_TYPE_MISMATCH,
        &temporal(
            r#"principal is W::Staff, action == W::Action::"Peek", resource"#,
            r#"principal == "alice""#,
        ),
    );
}

// The control: entity against entity stays accepted whatever the arity, per the
// decision that a cross-type entity comparison is well-typed.
#[test]
fn cedar_witness_entity_root_against_an_entity_is_accepted() {
    assert_accepts(
        "cedar: bare principal on Peek compared to a Gateway",
        &cedar(
            r#"principal, action == W::Action::"Peek", resource"#,
            r#"principal == W::Gateway::"gw""#,
        ),
    );
}

#[test]
fn temporal_entity_root_against_an_entity_is_accepted() {
    assert_accepts(
        "temporal: bare principal on Peek compared to a Gateway",
        &temporal(
            r#"principal, action == W::Action::"Peek", resource"#,
            r#"principal == W::Gateway::"gw""#,
        ),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 26. A scope root as a field-pattern ARGUMENT — where the tag still decides
// ═══════════════════════════════════════════════════════════════════════════
// This is the one shape where whether a bare root types TAGGED (`entity:Staff`) or
// UNTAGGED (`entity`) changes the verdict. Equality no longer distinguishes entity types
// at all, so the tag is inert there; but a field pattern compares the argument against a
// DECLARED field type, and `param_accepts` accepts an untagged side unconditionally.
//
// `input.owner` is declared `W::Manager` and the argument is `principal`, a `Staff` or
// `Partner`. The pattern can never match, so the condition is permanently false — and
// Cedar reports its analogue as an impossible policy at EVERY arity, measured:
//
//     cedar, one permitted principal type    err=0 warn=1
//     cedar, two permitted principal types   err=0 warn=1
//     cedar, narrowed to one                 err=0 warn=1
//
// The temporal dialect rejects it when the root types tagged. That happens with one
// permitted type, and — because the rule's scope narrowing is consulted — also when
// `principal is` narrows a multi-type action back to one. Without that consultation the
// narrowed case would silently pass, which is what these tests pin: a mutation that
// ignores the narrowing survives the rest of the suite.
//
// KNOWN GAP, deliberately not asserted here: with SEVERAL types permitted and no
// narrowing, the root types untagged and `param_accepts` lets it through, so the dead
// pattern is accepted. Cedar still warns there. Closing it means consulting the candidate
// set instead of accepting any untagged operand.

#[test]
fn cedar_witness_manager_field_against_principal_is_flagged() {
    // Cedar's nearest analogue to the pattern: compare the field to the principal.
    let src = cedar(
        r#"principal, action == W::Action::"Meter", resource"#,
        "context.input.owner == principal",
    );
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let lowered = LoweredPolicySet::from_str(&src, &service, &schema).expect("lowers");
    let result = Validator::new().validate(&lowered);
    assert_eq!(
        result.validation_errors().count(),
        0,
        "Cedar treats an entity-to-entity comparison as well-typed"
    );
    assert!(
        result.validation_warnings().count() > 0,
        "but Cedar DOES flag it as an impossible policy — a Manager is never a Staff"
    );
}

#[test]
fn temporal_scope_root_as_pattern_argument_is_rejected_when_typed() {
    // One permitted principal type: the root types `entity:Staff`, which cannot satisfy
    // a field declared `W::Manager`.
    assert_rejects(
        "temporal: input.owner: principal under a single-principal-type action",
        "expects `Manager`",
        &temporal_pattern_on("Meter", "input.owner: principal"),
    );
}

#[test]
fn temporal_scope_root_as_pattern_argument_honours_narrowing() {
    // Two permitted types, narrowed back to one by the RULE scope. The root types tagged
    // only if the narrowing is consulted — this is the case that pins it.
    assert_rejects(
        "temporal: input.owner: principal under `principal is W::Staff` on a two-type action",
        // Needle names the TYPE mismatch, not merely the field: `Team` declares `owner`,
        // so a path error cannot satisfy this.
        "expects `Manager`",
        &format!(
            "permit (principal is W::Staff, action == W::Action::\"Team\", resource)\n\
             when temporal {{ formerly within 1h \
             (W::Action::\"Team\"::request{{ input.owner: principal }}) }};"
        ),
    );
}
