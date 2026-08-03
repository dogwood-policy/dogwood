//! Entity equality decides the same way in a temporal condition as in a Cedar clause.
//!
//! Cedar's entity equality is STRUCTURAL over a typed pair: `EntityUID` is
//! `{ ty: EntityType, eid: Eid }` with equality derived over both fields, and `Eid` wraps a
//! string. So `W::Staff::"g1"` is not equal to `W::Gateway::"g1"` — the ids match and the
//! types do not. A cross-type comparison is not an error in Cedar; it is simply always
//! false.
//!
//! A temporal condition must decide the same way. The temporal engine, however, flattens that
//! typed pair into ONE rendered string and compares text
//! (`format!("'{ty}::\"{}\"'", id.replace('\'', "''"))`), which reproduces a two-field
//! structural equality through a single text field. That agrees with Cedar only if the
//! rendering is injective and identical on both sides — and Cedar itself declines to
//! canonicalise an id to text: `Eid` deliberately implements no `Display`, because upstream
//! could not settle whether it should escape (cedar-policy issue #884).
//!
//! # Why these tests compare VERDICTS, not validation
//!
//! The sibling suites (`temporal_request_envs.rs`, `temporal_action_groups.rs`) pair Cedar
//! against the temporal dialect on VALIDATION. That answers "does this policy typecheck".
//! It cannot answer "what does this policy decide", which is the question here — and the
//! right validation behaviour DEPENDS on the answer. Validation exists to reject what an
//! engine cannot faithfully evaluate, so deciding what to reject before knowing what the
//! engines do is backwards.
//!
//! These tests therefore lock the evaluation semantics FIRST. Validation behaviour for
//! these shapes is deliberately not asserted here; it currently disagrees with Cedar in one
//! direction and is inconsistent with itself in another, and settling it is the follow-up
//! this suite exists to inform.
//!
//! Consequently these tests build an `Authorizer` WITHOUT requiring validation to pass.
//! That is not an oversight: validation and evaluation are separate steps, and the point is
//! to observe what the engine decides for a policy validation may or may not accept.
//!
//! # How to read this file
//!
//! Every case is a PAIR over the same schema and the same trace:
//!
//! 1. `cedar_verdict_*` — the comparison as an ordinary Cedar `when { … }` clause, which
//!    establishes the reference answer.
//! 2. `temporal_verdict_*` — the same comparison inside `when temporal { … }`, asserted to
//!    reach the same decision.
//!
//! Each asserts the VERDICT VALUE, never merely that the two agree: two engines agreeing on
//! a wrong answer satisfies an agreement-only check, which this campaign has already been
//! caught by once.
//!
//! The temporal form wraps the comparison as `formerly within 1h (<event> && <comparison>)`.
//! The comparison reads the CURRENT request's scope, so it is time-point independent and
//! factors out of the window: with a prior matching event present, the temporal condition
//! reduces to the comparison itself, which is what makes the pair comparable.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ServiceSchema, parse_trace,
};

/// Two entity types whose ids can be made to collide, plus an entity-valued attribute.
///
/// `Staff` and `Gateway` both declare `id`, so a uid of either type can carry the same eid —
/// which is what makes a cross-type comparison with matching ids expressible.
const SCHEMA: &str = r#"namespace W {
  type ReadInput = { amount: Long, owner: W::Manager };

  entity Manager = { id: String };
  entity Gateway = { id: String };
  entity Team;
  entity Partner = { id: String };
  entity Staff in [Team] = { id: String, manager: W::Manager };

  // `Read` permits ONE principal type; `Duo` permits TWO. Only validation is
  // sensitive to that difference (a bare `principal` types only when exactly one type
  // is permitted); evaluation must not be, since the request carries one concrete
  // entity either way. Cases 8 and 9 pin that.
  action "Read" appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: ReadInput }
  };
  action "Duo" appliesTo {
    principal: [Staff, Partner], resource: [Gateway], context: { input: ReadInput }
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

/// One trace event. `principal_eid` sets the request principal's id; `manager_eid` the
/// entity-valued attribute. Both events in a trace share these, so the comparison under
/// test is the only thing that varies between cases.
fn event(ts: i64, n: usize, principal_eid: &str, manager_eid: &str) -> String {
    format!(
        "@{ts} scope(principal: W::Staff::\"{principal_eid}\", resource: W::Gateway::\"gw\") \
         entities(W::Staff::\"{principal_eid}\": {{ id: \"{principal_eid}\", \
         manager: W::Manager::\"{manager_eid}\" }}) \
         request_context(input: {{ amount: 1, owner: W::Manager::\"m1\" }}) \
         W::Action::\"Read\"::request(input: {{ amount: 1, owner: W::Manager::\"m1\" }}, \
         callerPrincipal: W::Staff::\"{principal_eid}\", callerResource: W::Gateway::\"gw\", \
         requestId: \"r{n}\")"
    )
}

/// Like [`event`] but declaring the principal a member of `W::Team::"t1"` via the
/// trailing `in [ … ]` parents clause.
fn event_in_team(ts: i64, n: usize, principal_eid: &str) -> String {
    format!(
        "@{ts} scope(principal: W::Staff::\"{principal_eid}\", resource: W::Gateway::\"gw\") \
         entities(W::Staff::\"{principal_eid}\": {{ id: \"{principal_eid}\", \
         manager: W::Manager::\"m1\" }} in [W::Team::\"t1\"]) \
         request_context(input: {{ amount: 1, owner: W::Manager::\"m1\" }}) \
         W::Action::\"Read\"::request(input: {{ amount: 1, owner: W::Manager::\"m1\" }}, \
         callerPrincipal: W::Staff::\"{principal_eid}\", callerResource: W::Gateway::\"gw\", \
         requestId: \"r{n}\")"
    )
}

/// [`verdict`] with the principal declared a member of `W::Team::"t1"`.
fn verdict_in_team(policy: &str, principal_eid: &str) -> Option<Decision> {
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let lowered = LoweredPolicySet::from_str(policy, &service, &schema).expect("policy lowers");
    let mut authorizer = Authorizer::new(lowered);
    let trace = format!(
        "{}\n{}",
        event_in_team(0, 0, principal_eid),
        event_in_team(5, 1, principal_eid)
    );
    let mut last = None;
    for e in &parse_trace(&trace).expect("trace parses") {
        if let Some(r) = authorizer.is_authorized(e) {
            last = Some(r.decision());
        }
    }
    last
}

/// Like [`event`] but for a named action, so a rule scoped to that action applies.
fn event_for(action: &str, ts: i64, n: usize, principal_eid: &str) -> String {
    format!(
        "@{ts} scope(principal: W::Staff::\"{principal_eid}\", resource: W::Gateway::\"gw\") \
         entities(W::Staff::\"{principal_eid}\": {{ id: \"{principal_eid}\", \
         manager: W::Manager::\"m1\" }}) \
         request_context(input: {{ amount: 1, owner: W::Manager::\"m1\" }}) \
         W::Action::\"{action}\"::request(input: {{ amount: 1, owner: W::Manager::\"m1\" }}, \
         callerPrincipal: W::Staff::\"{principal_eid}\", callerResource: W::Gateway::\"gw\", \
         requestId: \"r{n}\")"
    )
}

/// [`verdict`] with a trace of `action` events, so a rule scoped to `action` applies.
fn verdict_on(policy: &str, action: &str, principal_eid: &str) -> Option<Decision> {
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let lowered = LoweredPolicySet::from_str(policy, &service, &schema).expect("policy lowers");
    let mut authorizer = Authorizer::new(lowered);
    let trace = format!(
        "{}\n{}",
        event_for(action, 0, 0, principal_eid),
        event_for(action, 5, 1, principal_eid)
    );
    let mut last = None;
    for e in &parse_trace(&trace).expect("trace parses") {
        if let Some(r) = authorizer.is_authorized(e) {
            last = Some(r.decision());
        }
    }
    last
}

/// Two events, so the `formerly` window has a prior witness and the temporal condition
/// reduces to the comparison under test. Returns the verdict at the LAST timepoint.
fn verdict(policy: &str, principal_eid: &str, manager_eid: &str) -> Option<Decision> {
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let lowered = LoweredPolicySet::from_str(policy, &service, &schema).expect("policy lowers");
    // Deliberately NOT validated — see the module docs.
    let mut authorizer = Authorizer::new(lowered);
    let trace = format!(
        "{}\n{}",
        event(0, 0, principal_eid, manager_eid),
        event(5, 1, principal_eid, manager_eid)
    );
    let mut last = None;
    for e in &parse_trace(&trace).expect("trace parses") {
        if let Some(r) = authorizer.is_authorized(e) {
            last = Some(r.decision());
        }
    }
    last
}

fn cedar(comparison: &str) -> String {
    format!("permit (principal, action == W::Action::\"Read\", resource)\nwhen {{ {comparison} }};")
}

/// A temporal policy whose predicate carries `pattern` as a FIELD PATTERN, rather than
/// a comparison in the body — the dialect's native way to compare an event field
/// against a term.
/// The Cedar clause scoped to `Duo`, which permits TWO principal types.
fn cedar_duo(comparison: &str) -> String {
    format!("permit (principal, action == W::Action::\"Duo\", resource)\nwhen {{ {comparison} }};")
}

/// The temporal clause scoped to `Duo`.
fn temporal_duo(comparison: &str) -> String {
    format!(
        "permit (principal, action == W::Action::\"Duo\", resource)\n\
         when temporal {{ formerly within 1h \
         (W::Action::\"Duo\"::request{{}} && {comparison}) }};"
    )
}

fn temporal_pattern(pattern: &str) -> String {
    format!(
        "permit (principal, action == W::Action::\"Read\", resource)\n\
         when temporal {{ formerly within 1h \
         (W::Action::\"Read\"::request{{ {pattern} }}) }};"
    )
}

fn temporal(comparison: &str) -> String {
    format!(
        "permit (principal, action == W::Action::\"Read\", resource)\n\
         when temporal {{ formerly within 1h \
         (W::Action::\"Read\"::request{{}} && {comparison}) }};"
    )
}

// ═══════════════════════════════════════════════════════════════════════════
// 1. Cross-type equality with MATCHING ids
// ═══════════════════════════════════════════════════════════════════════════
// The request principal is `W::Staff::"g1"`. The comparison names
// `W::Gateway::"g1"` — same eid, different type. Cedar's structural equality over
// (ty, eid) makes this FALSE, so the permit does not fire and the request is denied.
//
// This is the case a text-flattening comparison can get wrong: if either side
// rendered without its type, the ids would match and the answer would flip to Allow.

#[test]
fn cedar_verdict_cross_type_matching_ids_is_false() {
    assert_eq!(
        verdict(&cedar(r#"principal == W::Gateway::"g1""#), "g1", "m1"),
        Some(Decision::Deny),
        "Cedar: W::Staff::\"g1\" != W::Gateway::\"g1\" — the types differ, so the \
         comparison is false and the permit does not fire"
    );
}

#[test]
fn temporal_verdict_cross_type_matching_ids_is_false() {
    assert_eq!(
        verdict(&temporal(r#"principal == W::Gateway::"g1""#), "g1", "m1"),
        Some(Decision::Deny),
        "temporal: must decide as Cedar does — the ids matching must not make two \
         differently-typed entities equal"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 2. Same-type equality — the controls
// ═══════════════════════════════════════════════════════════════════════════
// Without these, case 1 could pass against an engine that answers Deny to everything.

#[test]
fn cedar_verdict_same_type_matching_ids_is_true() {
    assert_eq!(
        verdict(&cedar(r#"principal == W::Staff::"s1""#), "s1", "m1"),
        Some(Decision::Allow),
        "Cedar: same type, same id"
    );
}

#[test]
fn temporal_verdict_same_type_matching_ids_is_true() {
    assert_eq!(
        verdict(&temporal(r#"principal == W::Staff::"s1""#), "s1", "m1"),
        Some(Decision::Allow),
        "temporal: same type, same id"
    );
}

#[test]
fn cedar_verdict_same_type_different_ids_is_false() {
    assert_eq!(
        verdict(&cedar(r#"principal == W::Staff::"s1""#), "s2", "m1"),
        Some(Decision::Deny),
        "Cedar: same type, different id"
    );
}

#[test]
fn temporal_verdict_same_type_different_ids_is_false() {
    assert_eq!(
        verdict(&temporal(r#"principal == W::Staff::"s1""#), "s2", "m1"),
        Some(Decision::Deny),
        "temporal: same type, different id"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 3. Ids whose text could collide under a naive rendering
// ═══════════════════════════════════════════════════════════════════════════
// Cedar compares a typed pair structurally and never renders an id to text — `Eid`
// implements no `Display` precisely because upstream would not choose an escaping
// convention. Anything that DOES render must not let two distinct uids collapse.
//
// An id containing `::` is the sharpest case: `W::Staff::"a::b"` and a hypothetical
// `W::Staff::"a"` + type `b` could flatten to overlapping text.

#[test]
fn cedar_verdict_id_containing_colons_is_distinct() {
    assert_eq!(
        verdict(&cedar(r#"principal == W::Staff::"a::b""#), "a::b", "m1"),
        Some(Decision::Allow),
        "Cedar: an id containing `::` compares equal to itself"
    );
    assert_eq!(
        verdict(&cedar(r#"principal == W::Staff::"a::b""#), "a", "m1"),
        Some(Decision::Deny),
        "Cedar: `a` is not `a::b`"
    );
}

#[test]
fn temporal_verdict_id_containing_colons_is_distinct() {
    assert_eq!(
        verdict(&temporal(r#"principal == W::Staff::"a::b""#), "a::b", "m1"),
        Some(Decision::Allow),
        "temporal: an id containing `::` compares equal to itself"
    );
    assert_eq!(
        verdict(&temporal(r#"principal == W::Staff::"a::b""#), "a", "m1"),
        Some(Decision::Deny),
        "temporal: `a` is not `a::b` — a rendering that splits on `::` would confuse them"
    );
}

// NOT COVERED HERE: an id containing a SINGLE QUOTE. It cannot be tested through this
// harness, because the quote does not survive the trace parser — a separate,
// pre-existing defect. Measured: with the request principal `W::Staff::"o'brien"` and
// its `id` attribute literally `"o'brien"`, BOTH
//
//     principal.id == "o'brien"
//     principal == W::Staff::"o'brien"
//
// decide Deny under an ordinary Cedar clause. The attribute comparison denying is the
// tell: the value read back is not the value written, so nothing about entity equality
// is being exercised. Asserting either answer here would pin that bug rather than the
// semantics this suite is for.
//
// It matters for the temporal engine question all the same, and more than the `::` case
// does: the single quote is the ONE character the entity SQL literal escapes
// (`id.replace('\'', "''")`). So it needs its own coverage once the trace parser can
// carry it, or via a path that does not go through a trace.

// ═══════════════════════════════════════════════════════════════════════════
// 4. An entity-valued ATTRIBUTE, not just the bare scope root
// ═══════════════════════════════════════════════════════════════════════════
// `Staff.manager` is entity-typed, so the same structural equality applies one level
// in. A bare root and an attribute take different code paths in the interpreter and
// in lowering, so both need pinning.

#[test]
fn cedar_verdict_entity_attribute_equality() {
    assert_eq!(
        verdict(
            &cedar(r#"principal.manager == W::Manager::"m1""#),
            "s1",
            "m1"
        ),
        Some(Decision::Allow),
        "Cedar: the attribute equals the named manager"
    );
    assert_eq!(
        verdict(
            &cedar(r#"principal.manager == W::Manager::"m1""#),
            "s1",
            "m2"
        ),
        Some(Decision::Deny),
        "Cedar: a different manager"
    );
}

#[test]
fn temporal_verdict_entity_attribute_equality() {
    assert_eq!(
        verdict(
            &temporal(r#"principal.manager == W::Manager::"m1""#),
            "s1",
            "m1"
        ),
        Some(Decision::Allow),
        "temporal: the attribute equals the named manager"
    );
    assert_eq!(
        verdict(
            &temporal(r#"principal.manager == W::Manager::"m1""#),
            "s1",
            "m2"
        ),
        Some(Decision::Deny),
        "temporal: a different manager"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 5. Cross-type equality on an attribute, ids matching
// ═══════════════════════════════════════════════════════════════════════════
// Case 1 one level in: the manager is `W::Manager::"m1"` and the comparison names
// `W::Gateway::"m1"`.

#[test]
fn cedar_verdict_attribute_cross_type_matching_ids_is_false() {
    assert_eq!(
        verdict(
            &cedar(r#"principal.manager == W::Gateway::"m1""#),
            "s1",
            "m1"
        ),
        Some(Decision::Deny),
        "Cedar: a Manager is not a Gateway, ids notwithstanding"
    );
}

#[test]
fn temporal_verdict_attribute_cross_type_matching_ids_is_false() {
    assert_eq!(
        verdict(
            &temporal(r#"principal.manager == W::Gateway::"m1""#),
            "s1",
            "m1"
        ),
        Some(Decision::Deny),
        "temporal: a Manager is not a Gateway, ids notwithstanding"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 6. The same equality through the dialect's OWN idiom: a field pattern
// ═══════════════════════════════════════════════════════════════════════════
// Everything above compares entities as a comparison OPERAND, which is the shape
// Cedar shares. The temporal dialect has a second, native way to compare entities:
// a predicate FIELD PATTERN, where an event field is unified against a term. That is
// a different code path — pattern unification rather than `eval_comparison` — so the
// same semantics has to be pinned there too.
//
// `request{ callerPrincipal: principal }` asks whether the event's `callerPrincipal`
// field equals the CURRENT request's principal. Cedar's analogue is an ordinary
// equality against the same uid.

#[test]
fn cedar_verdict_entity_equality_reference() {
    assert_eq!(
        verdict(&cedar(r#"principal == W::Staff::"s1""#), "s1", "m1"),
        Some(Decision::Allow),
        "Cedar reference: the principal is W::Staff::\"s1\""
    );
}

#[test]
fn temporal_verdict_entity_equality_via_field_pattern() {
    assert_eq!(
        verdict(
            &temporal_pattern(r#"callerPrincipal: principal"#),
            "s1",
            "m1"
        ),
        Some(Decision::Allow),
        "temporal: the event's callerPrincipal unifies with the current principal"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 7. Cross-type equality through the field-pattern route
// ═══════════════════════════════════════════════════════════════════════════
// Case 1's question, asked the dialect's own way. `callerResource` is a
// `W::Gateway` and `principal` is a `W::Staff`; the trace gives BOTH the id "gw".
// So the ids match and the types do not, and the pattern must NOT unify — the same
// answer Cedar gives for `==`.
//
// This is the sharpest test in the file for a rendering-based comparison: two
// entities that differ only in type, meeting through the path that unifies event
// fields rather than the one that evaluates comparisons.

#[test]
fn cedar_verdict_cross_type_reference() {
    assert_eq!(
        verdict(&cedar(r#"principal == W::Gateway::"gw""#), "gw", "m1"),
        Some(Decision::Deny),
        "Cedar reference: W::Staff::\"gw\" is not W::Gateway::\"gw\""
    );
}

#[test]
fn temporal_verdict_cross_type_via_field_pattern() {
    assert_eq!(
        verdict(
            &temporal_pattern(r#"callerResource: principal"#),
            "gw",
            "m1"
        ),
        Some(Decision::Deny),
        "temporal: the event's callerResource is a Gateway and the principal is a \
         Staff — matching ids must not make them unify"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 8. The number of PERMITTED principal types does not change the verdict
// ═══════════════════════════════════════════════════════════════════════════
// `Read` permits one principal type, `Duo` permits two. Validation IS sensitive to
// that — a bare `principal` types only when exactly one type is permitted, so the
// same mistake is rejected under `Read` and accepted under `Duo` — but EVALUATION
// must not be: the request carries one concrete entity either way.
//
// Pinning this matters because it says the validation inconsistency has no basis in
// evaluation. If these verdicts differed, the count would be semantically meaningful
// and the fix would be a different one entirely.
//
// The trace is unchanged; only the rule's action scope differs. The verdicts must be
// identical to cases 1 and 2.

#[test]
fn cedar_verdict_cross_type_is_false_under_two_permitted_types() {
    assert_eq!(
        verdict_on(&cedar_duo(r#"principal == W::Gateway::"g1""#), "Duo", "g1"),
        Some(Decision::Deny),
        "Cedar: still false — permitting a second principal type changes nothing"
    );
}

#[test]
fn temporal_verdict_cross_type_is_false_under_two_permitted_types() {
    assert_eq!(
        verdict_on(
            &temporal_duo(r#"principal == W::Gateway::"g1""#),
            "Duo",
            "g1"
        ),
        Some(Decision::Deny),
        "temporal: still false — matches case 1 exactly, so the permitted-type count \
         is a VALIDATION artifact with no evaluation basis"
    );
}

#[test]
fn cedar_verdict_same_type_is_true_under_two_permitted_types() {
    assert_eq!(
        verdict_on(&cedar_duo(r#"principal == W::Staff::"s1""#), "Duo", "s1"),
        Some(Decision::Allow),
        "Cedar: the positive control under two permitted types"
    );
}

#[test]
fn temporal_verdict_same_type_is_true_under_two_permitted_types() {
    assert_eq!(
        verdict_on(&temporal_duo(r#"principal == W::Staff::"s1""#), "Duo", "s1"),
        Some(Decision::Allow),
        "temporal: the positive control under two permitted types"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 9. Nor does narrowing the rule's scope
// ═══════════════════════════════════════════════════════════════════════════
// `principal is W::Staff` under `Duo` is the third validation variant (currently
// accepted where `Read` rejects). Evaluation must again be unchanged.

#[test]
fn cedar_verdict_cross_type_is_false_under_narrowed_scope() {
    assert_eq!(
        verdict_on(
            &format!(
                "permit (principal is W::Staff, action == W::Action::\"Duo\", resource)\n\
                 when {{ principal == W::Gateway::\"g1\" }};"
            ),
            "Duo",
            "g1"
        ),
        Some(Decision::Deny),
        "Cedar: narrowing the scope does not change the comparison's answer"
    );
}

#[test]
fn temporal_verdict_cross_type_is_false_under_narrowed_scope() {
    assert_eq!(
        verdict_on(
            &format!(
                "permit (principal is W::Staff, action == W::Action::\"Duo\", resource)\n\
                 when temporal {{ formerly within 1h \
                 (W::Action::\"Duo\"::request{{}} && principal == W::Gateway::\"g1\") }};"
            ),
            "Duo",
            "g1"
        ),
        Some(Decision::Deny),
        "temporal: narrowing the scope does not change the comparison's answer"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 10. The field-pattern route needs a SAME-TYPE negative control too
// ═══════════════════════════════════════════════════════════════════════════
// Case 6 established that a field pattern unifies when it should. Case 7 that it
// does not unify across types. Neither shows it discriminates between two entities
// of the SAME type — without this, both would pass against an implementation that
// unifies any two entities of matching type.

#[test]
fn cedar_verdict_same_type_mismatch_reference() {
    assert_eq!(
        verdict(&cedar(r#"principal == W::Staff::"other""#), "s1", "m1"),
        Some(Decision::Deny),
        "Cedar reference: W::Staff::\"s1\" is not W::Staff::\"other\""
    );
}

#[test]
fn temporal_verdict_same_type_mismatch_via_field_pattern() {
    assert_eq!(
        verdict(
            &temporal_pattern(r#"callerPrincipal: W::Staff::"other""#),
            "s1",
            "m1"
        ),
        Some(Decision::Deny),
        "temporal: the event's callerPrincipal is W::Staff::\"s1\", so it must not \
         unify with a different Staff uid"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 11. Cross-event correlation: bind in the event, compare to the request
// ═══════════════════════════════════════════════════════════════════════════
// Cases 6-10 unify an event field directly against a term. This binds the field to
// a VARIABLE first and then compares the variable — the shape a real correlation
// uses, and a third code path (binder unification, then `eval_comparison` on the
// bound value) rather than pattern matching alone.
//
// Positive: the bound principal equals the current request's principal.

#[test]
fn temporal_verdict_correlation_via_bound_variable_positive() {
    let policy = concat!(
        "permit (principal, action == W::Action::\"Read\", resource)\n",
        "when temporal { exists (p: Entity). (formerly within 1h ",
        "(W::Action::\"Read\"::request{ callerPrincipal: p }) && p == principal) };"
    );
    assert_eq!(
        verdict(policy, "s1", "m1"),
        Some(Decision::Allow),
        "temporal: the event's callerPrincipal, bound to `p`, equals the current principal"
    );
}

// Negative: the same binding compared against a DIFFERENT uid of the same type.
#[test]
fn temporal_verdict_correlation_via_bound_variable_negative() {
    let policy = concat!(
        "permit (principal, action == W::Action::\"Read\", resource)\n",
        "when temporal { exists (p: Entity). (formerly within 1h ",
        "(W::Action::\"Read\"::request{ callerPrincipal: p }) && p == W::Staff::\"other\") };"
    );
    assert_eq!(
        verdict(policy, "s1", "m1"),
        Some(Decision::Deny),
        "temporal: the bound principal is W::Staff::\"s1\", not W::Staff::\"other\""
    );
}

// Negative across types: the bound value is a Staff, compared to a Gateway with the
// same id.
#[test]
fn temporal_verdict_correlation_via_bound_variable_cross_type() {
    let policy = concat!(
        "permit (principal, action == W::Action::\"Read\", resource)\n",
        "when temporal { exists (p: Entity). (formerly within 1h ",
        "(W::Action::\"Read\"::request{ callerPrincipal: p }) && p == W::Gateway::\"gw\") };"
    );
    assert_eq!(
        verdict(policy, "gw", "m1"),
        Some(Decision::Deny),
        "temporal: the bound Staff must not equal a Gateway with the same id"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 12. An entity-typed CONTEXT FIELD — a fourth route to an entity value
// ═══════════════════════════════════════════════════════════════════════════
// `context.input.owner` is declared `W::Manager`. This is distinct from every route
// above: not a scope root, not an attribute ON a scope entity, and not an event field
// reached by a pattern. It is a context record field whose declared type is an entity,
// and it is the shape the validation question turns on — `param_accepts` governs field
// patterns while `types_compatible` governs equality, and both carry their own copy of
// the entity rule.

#[test]
fn cedar_verdict_context_entity_field_same_type() {
    assert_eq!(
        verdict(
            &cedar(r#"context.input.owner == W::Manager::"m1""#),
            "s1",
            "m1"
        ),
        Some(Decision::Allow),
        "Cedar: the context field holds W::Manager::\"m1\""
    );
}

#[test]
fn temporal_verdict_context_entity_field_same_type() {
    assert_eq!(
        verdict(
            &temporal(r#"context.input.owner == W::Manager::"m1""#),
            "s1",
            "m1"
        ),
        Some(Decision::Allow),
        "temporal: the context field holds W::Manager::\"m1\""
    );
}

#[test]
fn cedar_verdict_context_entity_field_different_id() {
    assert_eq!(
        verdict(
            &cedar(r#"context.input.owner == W::Manager::"other""#),
            "s1",
            "m1"
        ),
        Some(Decision::Deny),
        "Cedar: a different Manager"
    );
}

#[test]
fn temporal_verdict_context_entity_field_different_id() {
    assert_eq!(
        verdict(
            &temporal(r#"context.input.owner == W::Manager::"other""#),
            "s1",
            "m1"
        ),
        Some(Decision::Deny),
        "temporal: a different Manager"
    );
}

// The cross-type case on this route: the field holds a Manager, the comparison names a
// Gateway, and the ids MATCH (`m1`). Must be false, as everywhere else.
#[test]
fn cedar_verdict_context_entity_field_cross_type() {
    assert_eq!(
        verdict(
            &cedar(r#"context.input.owner == W::Gateway::"m1""#),
            "s1",
            "m1"
        ),
        Some(Decision::Deny),
        "Cedar: a Manager is not a Gateway, ids notwithstanding"
    );
}

#[test]
fn temporal_verdict_context_entity_field_cross_type() {
    assert_eq!(
        verdict(
            &temporal(r#"context.input.owner == W::Gateway::"m1""#),
            "s1",
            "m1"
        ),
        Some(Decision::Deny),
        "temporal: a Manager is not a Gateway, ids notwithstanding"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 13. `!=` as well as `==`
// ═══════════════════════════════════════════════════════════════════════════
// `check_types` handles both operators in one arm, and every case above uses `==`.
// The negation of an always-false comparison is always TRUE, which is the more
// dangerous direction: under `forbid` it would fire unconditionally.

#[test]
fn cedar_verdict_cross_type_negated_is_true() {
    assert_eq!(
        verdict(&cedar(r#"principal != W::Gateway::"g1""#), "g1", "m1"),
        Some(Decision::Allow),
        "Cedar: the entities are not equal, so `!=` holds"
    );
}

#[test]
fn temporal_verdict_cross_type_negated_is_true() {
    assert_eq!(
        verdict(&temporal(r#"principal != W::Gateway::"g1""#), "g1", "m1"),
        Some(Decision::Allow),
        "temporal: `!=` on two differently-typed entities holds — the negation of an \
         always-false comparison is always true"
    );
}

#[test]
fn cedar_verdict_same_type_negated_is_false() {
    assert_eq!(
        verdict(&cedar(r#"principal != W::Staff::"s1""#), "s1", "m1"),
        Some(Decision::Deny),
        "Cedar: the control — same entity, so `!=` is false"
    );
}

#[test]
fn temporal_verdict_same_type_negated_is_false() {
    assert_eq!(
        verdict(&temporal(r#"principal != W::Staff::"s1""#), "s1", "m1"),
        Some(Decision::Deny),
        "temporal: the control — same entity, so `!=` is false"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 14. Validation: relaxed for EQUALITY, strict for FIELD PATTERNS
// ═══════════════════════════════════════════════════════════════════════════
// The evaluation semantics above are shared with Cedar. Validation splits, and the two
// halves have different justifications — this went back and forth, so both are recorded.
//
// EQUALITY is not an error. An operand may be MULTI-TYPED, and comparing it against one
// of its possible types is the discriminating idiom
// `a == Ns::T1::"x" || a == Ns::T2::"y"`, where each disjunct is wrong only in isolation.
// Reachable today via a condition or macro reused across `action in [...]`. Cedar's
// equivalent diagnostic is a whole-policy `policy is impossible` WARNING, which cannot
// reach a temporal leaf — so this is SILENT for now, deliberately. Erroring would cement
// a restriction that a future temporal impossibility analysis should lift, and that
// analysis is where the diagnostic belongs.
//
// FIELD PATTERNS stay strict. `param_accepts` takes its expected type from a DECLARED
// field, which has exactly one entity type, so no multi-typed operand can arise and
// rejecting restricts nothing legitimate. That is also where the enum-swap case lives
// (`tests/expected_failures/corpus/1035_field_pattern_entity_type_swap`, two enum types
// with identical ids so the enum-eid check passes the literal), so relaxing equality
// costs no detection there.

#[test]
fn temporal_accepts_cross_type_entity_equality() {
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let src = temporal(r#"principal == W::Gateway::"g1""#);
    let lowered = LoweredPolicySet::from_str(&src, &service, &schema).expect("lowers");
    let errors: Vec<String> = dogwood_language::Validator::new()
        .validate(&lowered)
        .validation_errors()
        .map(|e| format!("{e}"))
        .collect();
    assert!(
        errors.is_empty(),
        "equality against a differently-typed entity is well-typed; a multi-typed \
         operand makes it a legitimate discriminating test. Got:\n{}",
        errors.join("\n")
    );
}

#[test]
fn cedar_witness_warns_on_cross_type_entity_equality() {
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let src = cedar(r#"principal == W::Gateway::"g1""#);
    let lowered = LoweredPolicySet::from_str(&src, &service, &schema).expect("lowers");
    let result = dogwood_language::Validator::new().validate(&lowered);
    assert_eq!(result.validation_errors().count(), 0, "Cedar: well-typed");
    assert!(
        result.validation_warnings().count() > 0,
        "Cedar flags it as an impossible policy. That is the channel a future temporal \
         impossibility analysis should mirror — and its absence inside a temporal leaf is \
         why the temporal side is silent rather than erroring"
    );
}

/// A field pattern against a differently-typed entity IS still rejected.
///
/// Uses a CONTEXT field (`input.owner`), because `param_accepts` is only reached for a
/// field resolvable in the action's context record — a derived event-schema field such as
/// `callerResource` resolves to nothing and is never type-checked at all, which is a
/// separate pre-existing gap.
#[test]
fn temporal_rejects_cross_type_entity_field_pattern() {
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let src = temporal_pattern(r#"input.owner: W::Gateway::"m1""#);
    let lowered = LoweredPolicySet::from_str(&src, &service, &schema).expect("lowers");
    let errors: Vec<String> = dogwood_language::Validator::new()
        .validate(&lowered)
        .validation_errors()
        .map(|e| format!("{e}"))
        .collect();
    assert!(
        !errors.is_empty(),
        "a declared field has exactly one entity type, so a mismatched literal is \
         unambiguously wrong and stays an error"
    );
}
