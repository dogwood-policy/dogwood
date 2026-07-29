//! `sum` must be a sum: order-independent, and exact whenever its result is
//! representable.
//!
//! An aggregate ranges over a SET of rows, so its value cannot depend on the order
//! those rows happen to be folded in. Accumulating in the result's own width breaks
//! that: a partial total can leave the range even when the final total sits well
//! inside it, and once a saturating fold clamps it never recovers — so the answer
//! becomes a function of row order.
//!
//! This is not a hypothetical. The first three cases came from the differential
//! fuzzer, which found them by choosing values that straddle the range: all-valid
//! inputs, a representable final total, unrepresentable intermediates. The rest are
//! boundary and degenerate guards added alongside them, and two of those cannot fail
//! against the old fold — an out-of-range or empty relation does not exercise a defect
//! about totals the range CAN hold.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ServiceSchema, parse_trace,
};

const SCHEMA: &str = r#"namespace Test {
  type MeterInput = { amount: Long };
  type MeterOutput = { result: Bool };
  type SystemContext = { now: datetime };

  entity Gateway;
  entity User = { id: String };

  action "Meter" appliesTo {
    principal: [User], resource: [Gateway],
    context: { input: MeterInput, output?: MeterOutput, system: SystemContext }
  };
}"#;

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal:   principalType(A),
    callerResource:    resourceType(A),
    requestId:         String,
    sessionId:         String,
}
event <A>::response {
    ...inputs(A),
    ...outputs(A),
    callerPrincipal:   principalType(A),
    callerResource:    resourceType(A),
    requestId:         String,
    sessionId:         String,
}
"#;

/// `sum amount over the last hour > threshold`.
fn policy(threshold: i64) -> String {
    format!(
        r#"permit (
  principal,
  action == Test::Action::"Meter",
  resource
)
when temporal {{
  exists (s: Long). (sum a for (a: Long), (t: Timepoint). where formerly within 1h
    (Test::Action::"Meter"::request{{ input.amount: a }} && tp(t))) == s && s > {threshold}
}};"#
    )
}

/// Like [`policy`] but with no `Timepoint` binder, so the projected relation
/// deduplicates equal amounts across time instead of keeping one row per event.
fn policy_no_tp(threshold: i64) -> String {
    format!(
        r#"permit (
  principal,
  action == Test::Action::"Meter",
  resource
)
when temporal {{
  exists (s: Long). (sum a for (a: Long). where formerly within 1h
    (Test::Action::"Meter"::request{{ input.amount: a }})) == s && s > {threshold}
}};"#
    )
}

fn meter(ts: i64, amount: i64) -> String {
    format!(
        "@{ts} scope(principal: Test::User::\"u\", resource: Test::Gateway::\"g\") \
         request_context(input: {{ amount: {amount} }}) \
         Test::Action::\"Meter\"::request(input: {{ amount: {amount} }}, \
         callerPrincipal: Test::User::\"u\", callerResource: Test::Gateway::\"g\", \
         requestId: \"m{ts}\")"
    )
}

/// The verdict at the LAST timepoint of `amounts`, in the order given.
fn verdict(threshold: i64, amounts: &[i64]) -> Option<Decision> {
    verdict_with(&policy(threshold), amounts)
}

/// [`verdict`] against the no-`Timepoint` policy, whose relation collapses duplicates.
fn verdict_no_tp(threshold: i64, amounts: &[i64]) -> Option<Decision> {
    verdict_with(&policy_no_tp(threshold), amounts)
}

fn verdict_with(policy_src: &str, amounts: &[i64]) -> Option<Decision> {
    let trace = amounts
        .iter()
        .enumerate()
        .map(|(i, a)| meter(i as i64, *a))
        .collect::<Vec<_>>()
        .join("\n");

    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("event schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds");
    let lowered =
        LoweredPolicySet::from_str(policy_src, &service, &policy_schema).expect("policy lowers");
    let mut authorizer = Authorizer::new(lowered);

    let events = parse_trace(&trace).expect("trace parses");
    let mut last = None;
    for event in &events {
        if let Some(r) = authorizer.is_authorized(event) {
            last = Some(r.decision());
        }
    }
    last
}

/// A total that FITS must be computed exactly, even when getting there passes
/// outside the range.
///
/// These three amounts are each a valid `Long`, and their exact total is comfortably
/// inside the range. A fold in the result's own width saturates at the second
/// addition and the third then brings it to zero, so `> 1000` becomes a deny.
#[test]
fn a_representable_total_is_exact_even_when_intermediates_are_not() {
    let amounts = [
        9223372036854750991,
        9223372036854719834,
        -9223372036854775807,
    ];
    let exact: i128 = amounts.iter().map(|a| *a as i128).sum();
    assert!(
        i64::try_from(exact).is_ok(),
        "the total ({exact}) must be representable, else this tests the wrong thing"
    );
    assert!(exact > 1000, "and it must clear the threshold: {exact}");

    assert_eq!(
        verdict(1000, &amounts),
        Some(Decision::Allow),
        "the total is {exact}, which is greater than 1000"
    );
}

/// The same multiset in a different order must give the same verdict.
///
/// Order-independence is the property that makes this a sum rather than a fold. A
/// saturating accumulator has it only when no prefix leaves the range, so the two
/// orders below disagree: one saturates, the other does not.
#[test]
fn the_verdict_does_not_depend_on_row_order() {
    let ascending = [
        9223372036854750991,
        9223372036854719834,
        -9223372036854775807,
    ];
    let interleaved = [
        9223372036854750991,
        -9223372036854775807,
        9223372036854719834,
    ];
    let descending = [
        -9223372036854775807,
        9223372036854750991,
        9223372036854719834,
    ];

    let exact: i128 = ascending.iter().map(|a| *a as i128).sum();
    assert!(
        exact > 1000,
        "the shared total ({exact}) must clear the threshold"
    );

    // Assert the VALUE each order produces, not merely that they agree: three
    // orders agreeing on the WRONG answer would satisfy an agreement-only check,
    // and so would an implementation that ignored its input entirely.
    for (label, order) in [
        ("ascending", &ascending),
        ("interleaved", &interleaved),
        ("descending", &descending),
    ] {
        assert_eq!(
            verdict(1000, order),
            Some(Decision::Allow),
            "{label}: the total is {exact} whichever order the rows arrive in"
        );
    }
}

/// A negative total whose intermediates exceed the range in the POSITIVE direction.
///
/// Mirrors the first case so a fix cannot work in one direction only. The exact
/// total is -100, so a threshold of -1000 permits and the saturating fold's large
/// positive residue also permits — the discriminating threshold is between them.
#[test]
fn a_negative_total_is_exact_across_a_positive_excursion() {
    let amounts = [-35039, -9223372036854749758, 18532, 9223372036854766165];
    let exact: i128 = amounts.iter().map(|a| *a as i128).sum();
    assert_eq!(exact, -100, "the test's own arithmetic: exact total");

    assert_eq!(
        verdict(-1000, &amounts),
        Some(Decision::Allow),
        "the total is {exact}, which is greater than -1000"
    );
    assert_eq!(
        verdict(0, &amounts),
        Some(Decision::Deny),
        "the total is {exact}, which is NOT greater than 0 — this is the assertion a \
         saturating fold fails, since its residue is a large positive number"
    );
}

/// A total sitting exactly ON each boundary must be exact, not clamped.
///
/// These are the values the clamp would return, so they distinguish "computed the
/// right answer" from "clamped to a value that happens to be right".
#[test]
fn a_total_exactly_at_each_boundary_is_exact() {
    // i64::MAX reached from above: MAX+1 then -1.
    let at_max = [9223372036854775807, 1, -1];
    let exact: i128 = at_max.iter().map(|a| *a as i128).sum();
    assert_eq!(exact, i64::MAX as i128, "the test's own arithmetic");
    assert_eq!(
        verdict(9223372036854775806, &at_max),
        Some(Decision::Allow),
        "a total of exactly i64::MAX is greater than MAX-1"
    );

    // i64::MIN reached from below: MIN-1 then +1.
    let at_min = [-9223372036854775808, -1, 1];
    let exact: i128 = at_min.iter().map(|a| *a as i128).sum();
    assert_eq!(exact, i64::MIN as i128, "the test's own arithmetic");
    assert_eq!(
        verdict(i64::MIN, &at_min),
        Some(Decision::Deny),
        "a total of exactly i64::MIN is not greater than MIN"
    );
}

/// A total beyond the boundary still DENIES where every conforming reading denies.
///
/// What such a total means is implementation-defined (formal specification §5.4), so
/// this pins only the direction all readings share, and deliberately asserts nothing
/// that would distinguish them.
///
/// Note which direction that is, because it is not the obvious one. These policies
/// bind the aggregate through `exists (s: Long). ((sum ...) == s && ...)`, and an
/// out-of-range total has NO `Long` witness unless the implementation clamps it — so
/// under a widening implementation the existential is empty whatever the threshold.
/// These are `permit` policies, so an empty existential denies; note the polarity
/// matters, because under `forbid` it would stop the rule firing and surface as an
/// Allow instead. Only the DENY direction is therefore common ground here; asserting
/// an Allow would pin clamping and fail against a conforming alternative.
#[test]
fn a_total_beyond_the_boundary_denies_under_every_conforming_reading() {
    // Above the maximum. Against the endpoint itself the readings coincide: clamping
    // binds s to i64::MAX, and MAX is not > MAX; widening has no Long witness. Any
    // LOWER threshold would discriminate (clamping clears it, widening still has no
    // witness), which is exactly what must not be asserted here.
    let beyond: [i64; 2] = [i64::MAX, 1];
    let exact: i128 = beyond.iter().map(|a| *a as i128).sum();
    assert_eq!(exact, i64::MAX as i128 + 1, "the test's own arithmetic");
    assert!(
        i64::try_from(exact).is_err(),
        "the total must be OUT of range, else this tests the wrong thing"
    );
    assert_eq!(
        verdict(i64::MAX, &beyond),
        Some(Decision::Deny),
        "a total of {exact} is not greater than i64::MAX under any reading"
    );

    // Below the minimum: clamping binds s to i64::MIN, which is not > 0; widening has
    // no Long witness, so the existential is empty. Deny either way.
    let below: [i64; 2] = [i64::MIN, -1];
    let exact: i128 = below.iter().map(|a| *a as i128).sum();
    assert!(
        i64::try_from(exact).is_err(),
        "the total ({exact}) must be OUT of range"
    );
    assert_eq!(
        verdict(0, &below),
        Some(Decision::Deny),
        "a total of {exact} is not greater than 0 under any reading"
    );
}

/// An empty relation sums to zero, and a single row sums to itself.
#[test]
fn degenerate_relations_sum_as_expected() {
    // No events at all: the sum is 0, which is not greater than 0.
    assert_eq!(
        verdict(0, &[]),
        None,
        "no decision points in an empty trace"
    );

    // One row: the sum is that row.
    assert_eq!(verdict(41, &[42]), Some(Decision::Allow), "42 > 41");
    assert_eq!(verdict(42, &[42]), Some(Decision::Deny), "42 is not > 42");
}

/// The same, with dedup ACTIVE — the case that tests the fix's stated reason.
///
/// Every test above lists a `Timepoint` binder, so each satisfying row is distinct and
/// the projected relation is already a set. That leaves the premise untested: the fix
/// is justified by an aggregate ranging over a SET, which only bites when dedup
/// actually collapses rows. Omitting the timepoint binder deduplicates equal amounts
/// across time, so a repeated amount contributes ONCE.
#[test]
fn a_sum_over_a_collapsing_relation_is_a_set_sum_and_order_independent() {
    // Dedup before accumulate: {5, 7} totals 12, not the multiset's 17.
    assert_eq!(
        verdict_no_tp(11, &[5, 7, 5]),
        Some(Decision::Allow),
        "the set total 12 exceeds 11"
    );
    assert_eq!(
        verdict_no_tp(12, &[5, 7, 5]),
        Some(Decision::Deny),
        "the set total is 12, not the multiset total 17, so it does not exceed 12"
    );

    // Dedup active AND an unrepresentable partial sum, in four orders. The set total
    // is i64::MAX - 2; a fold that saturates mid-way lands nowhere near it.
    let a = i64::MAX - 1;
    let b = i64::MAX - 2;
    let orders: [[i64; 4]; 4] = [[a, a, b, -a], [-a, b, a, a], [b, a, -a, a], [a, -a, a, b]];
    let exact: i128 = [a, b, -a].iter().map(|v| *v as i128).sum();
    assert_eq!(exact, b as i128, "the SET total is i64::MAX - 2");
    for (i, order) in orders.iter().enumerate() {
        assert_eq!(
            verdict_no_tp(1000, order),
            Some(Decision::Allow),
            "order {i}: the set total {exact} exceeds 1000 whatever the arrival order"
        );
    }
}
