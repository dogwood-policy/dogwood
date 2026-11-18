//! Canonical values: the interpreter compares values as the specification does
//! (`dogwood-lean`, `Dogwood.Spec.Conformance`; the semantics review's spec
//! change 11). The specification's values are Cedar values, which have no null.
//!
//! * **A logged `null` is absent** (review P6, and B6's `null_vs_string_null`
//!   probe). A `*` wildcard does not match it, a variable does not bind to it,
//!   and a pin does not file under it. A `null` in the request context or an
//!   entity attribute is absent too, on both the temporal and the Cedar side.
//!
//! * **Sets compare as sets** (review I-2): an array is a Cedar set, so its
//!   order and its repetitions do not matter, in a comparison, a correlation, a
//!   pin, or a partition key.
//!
//! * **Decimals compare by value** (review P4): `02.5` = `2.5`, in logged values,
//!   pins and literals. The interpreter already did; the cases below pin it.
//! * **Canonical forms** (`Value::canonical`, `Value::canonical_decimal`,
//!   `Event::canonical`): the one representative of each value's class, which an
//!   engine that stores values as text stores, so that equal values are stored
//!   alike. Canonicalizing an event changes no decision.
//!
//! Each case states the specification's verdict, and fails on the interpreter of
//! Dogwood_Language 1.1, unless it says it pins a verdict 1.1 already gave.

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema, Value, parse_trace,
    partition_value_key,
};

#[path = "support/slicing.rs"]
mod support;

/// The action schema of the review's generated cases (`correctness.md` §3).
const F_SCHEMA: &str = r#"
namespace F {
  entity User = { level: Long, dept: String };
  entity Res = { limit: Long };
  type In = { n: Long, s: String, d: decimal, tags: Set<String>, u: User, b: Bool, o?: Long, tag?: String };
  type Out = { ok: Bool, m: Long };
  action "Op" appliesTo { principal: [User], resource: [Res], context: { input: In, output?: Out, session: String, tenant?: String } };
  action "A" appliesTo { principal: [User], resource: [Res], context: { input: In, output?: Out, session: String, tenant?: String } };
  action "B" appliesTo { principal: [User], resource: [Res], context: { input: In, output?: Out, session: String, tenant?: String } };
}
"#;

/// The review's event schema under the principal pin.
const F_EVENTS: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource: resourceType(A),
    sid: String,
    session: String,
    tenant: String,
}

event <A>::response {
    ...inputs(A),
    ...outputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource: resourceType(A),
    sid: String,
    session: String,
    tenant: String,
}
"#;

fn lower(cedar: &str, events: &str, policy: &str) -> LoweredPolicySet {
    let service = ServiceSchema::builder()
        .event_schema_str(events)
        .build()
        .expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(cedar).expect("action schema parses");
    LoweredPolicySet::from_str(policy, &service, &schema).expect("policy lowers")
}

/// The verdict at every event of `log`: `Some(true)` allow, `Some(false)` deny,
/// `None` a history event.
fn verdicts(policies: LoweredPolicySet, partitioned: bool, log: &str) -> Vec<Option<bool>> {
    let mut authorizer = if partitioned {
        Authorizer::builder(policies)
            .partition_temporal()
            .build()
            .expect("partitioned authorizer builds")
    } else {
        Authorizer::new(policies)
    };
    parse_trace(log)
        .expect("trace parses")
        .iter()
        .map(|e| {
            authorizer
                .is_authorized(e)
                .map(|r| r.decision() == Decision::Allow)
        })
        .collect()
}

fn both(cedar: &str, events: &str, policy: &str, log: &str) -> [Vec<Option<bool>>; 2] {
    [
        verdicts(lower(cedar, events, policy), false, log),
        verdicts(lower(cedar, events, policy), true, log),
    ]
}

const A: Option<bool> = Some(true);
const D: Option<bool> = Some(false);
const N: Option<bool> = None;

fn op_request(ts: u32, input: &str, ctx_input: &str) -> String {
    format!(
        r#"@{ts} scope(principal: F::User::"u0", resource: F::Res::"r0") request_context(input: {{ {ctx_input} }}, session: "s1") F::Action::"Op"::request(input: {{ {input} }}, callerPrincipal: F::User::"u0", callerResource: F::Res::"r0", sid: "s1", session: "s1")"#
    )
}

fn a_response(ts: u32, input: &str) -> String {
    format!(
        r#"@{ts} scope(principal: F::User::"u0", resource: F::Res::"r0") F::Action::"A"::response(input: {{ {input} }}, output: {{ ok: true, m: 3 }}, callerPrincipal: F::User::"u0", callerResource: F::Res::"r0", sid: "s1", session: "s1")"#
    )
}

const BASE: &str = r#"n: 0, s: "x", d: 1.5, tags: [], u: F::User::"u0", b: true"#;

// ── P6: a logged null is absent ─────────────────────────────────────────────

/// Review P6 (`shared-null`): one decision event logging `o: null`, under
/// `exists s. Op::request{input.s: s, input.o: *}`. The wildcard needs a present
/// `o`; the specification has no null, so the field is absent: DENY.
#[test]
fn p6_a_wildcard_does_not_match_a_logged_null() {
    let policy = r#"permit (principal, action == F::Action::"Op", resource)
        when temporal { exists (s1: String). (F::Action::"Op"::request{ input.s: s1, input.o: * }) };"#;
    let log = op_request(
        125,
        &format!("{BASE}, o: null"),
        &format!("{BASE}, o: null"),
    );
    assert_eq!(both(F_SCHEMA, F_EVENTS, policy, &log), [vec![D], vec![D]]);
    // Control: a present `o` matches.
    let log = op_request(125, &format!("{BASE}, o: 4"), &format!("{BASE}, o: 4"));
    assert_eq!(both(F_SCHEMA, F_EVENTS, policy, &log), [vec![A], vec![A]]);
}

/// A logged `null` does not bind a variable: `exists o. A::response{input.o: o}`
/// has no witness when `o` is logged `null`.
#[test]
fn p6_a_variable_does_not_bind_a_logged_null() {
    let policy = r#"permit (principal, action == F::Action::"Op", resource)
        when temporal { exists (o1: Long). (formerly within 60s F::Action::"A"::response{ input.o: o1 }) };"#;
    let log = [
        a_response(100, &format!("{BASE}, o: null")),
        op_request(101, BASE, BASE),
    ]
    .join("\n");
    assert_eq!(
        both(F_SCHEMA, F_EVENTS, policy, &log),
        [vec![N, D], vec![N, D]]
    );
    let log = [
        a_response(100, &format!("{BASE}, o: 7")),
        op_request(101, BASE, BASE),
    ]
    .join("\n");
    assert_eq!(
        both(F_SCHEMA, F_EVENTS, policy, &log),
        [vec![N, A], vec![N, A]]
    );
}

/// A `count` over a field counts present values only: two responses, one logging
/// `o: null`, give one `o` to count.
#[test]
fn p6_an_aggregate_does_not_count_a_logged_null() {
    let policy = r#"forbid (principal, action == F::Action::"Op", resource)
        when temporal { (count for (o1: Long). where formerly within 60s F::Action::"A"::response{ input.o: o1 }) >= 2 };
        permit (principal, action == F::Action::"Op", resource);"#;
    let log = [
        a_response(100, &format!("{BASE}, o: 1")),
        a_response(101, &format!("{BASE}, o: null")),
        op_request(102, BASE, BASE),
    ]
    .join("\n");
    assert_eq!(
        both(F_SCHEMA, F_EVENTS, policy, &log),
        [vec![N, N, A], vec![N, N, A]]
    );
}

/// B6's third probe (`null_vs_string_null`): a logged `null` is not the string
/// `"null"`. The interpreter already compared them as typed values; this pins it.
#[test]
fn b6_a_logged_null_is_not_the_string_null() {
    let policy = r#"permit (principal, action == F::Action::"Op", resource)
        when temporal { formerly within 1h F::Action::"A"::response{ input.tag: context.input.tag } };"#;
    let log = [
        a_response(100, &format!("{BASE}, tag: null")),
        op_request(
            200,
            &format!("{BASE}, tag: \"null\""),
            &format!("{BASE}, tag: \"null\""),
        ),
    ]
    .join("\n");
    assert_eq!(
        both(F_SCHEMA, F_EVENTS, policy, &log),
        [vec![N, D], vec![N, D]]
    );
}

/// A `null` on the request side is absent too: a pin or a `context.<path>`
/// reference to it does not resolve, so a logged `null` and a context `null` do
/// not correlate (DENY), where 1.1 found them equal (ALLOW).
#[test]
fn p6_a_request_side_null_does_not_resolve() {
    let policy = r#"permit (principal, action == F::Action::"Op", resource)
        when temporal { formerly within 1h F::Action::"A"::response{ input.tag: context.input.tag } };"#;
    let log = [
        a_response(100, &format!("{BASE}, tag: null")),
        op_request(
            200,
            &format!("{BASE}, tag: null"),
            &format!("{BASE}, tag: null"),
        ),
    ]
    .join("\n");
    assert_eq!(
        both(F_SCHEMA, F_EVENTS, policy, &log),
        [vec![N, D], vec![N, D]]
    );
}

/// A context `null` is absent on the Cedar side: `context.input has tag` is false.
/// Dogwood_Language 1.1 rendered it as the empty string, so `has` held and
/// `context.input.tag == ""` held.
#[test]
fn p6_a_context_null_is_absent_for_cedar() {
    let has = r#"permit (principal, action == F::Action::"Op", resource) when { context.input has tag };"#;
    let empty = r#"permit (principal, action == F::Action::"Op", resource)
        when { context.input has tag && context.input.tag == "" };"#;
    let null = op_request(
        100,
        &format!("{BASE}, tag: null"),
        &format!("{BASE}, tag: null"),
    );
    let present = op_request(
        100,
        &format!("{BASE}, tag: \"t\""),
        &format!("{BASE}, tag: \"t\""),
    );
    for policy in [has, empty] {
        assert_eq!(
            verdicts(lower(F_SCHEMA, F_EVENTS, policy), false, &null),
            vec![D],
            "{policy}"
        );
    }
    assert_eq!(
        verdicts(lower(F_SCHEMA, F_EVENTS, has), false, &present),
        vec![A]
    );
}

/// A pin field logged as `null` is not logged: under the session pin, a response
/// logging `session: null` is in no session, and a decision whose session is
/// `null` has no session to read. Dogwood_Language 1.1 filed both under the
/// value `null` and let the decision see the response (ALLOW); the
/// specification's decision sees nothing (DENY), in global and in partitioned
/// mode alike.
#[test]
fn p6_a_null_pin_field_files_under_no_key() {
    let events = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource: resourceType(A),
    pin session: String = context.session,
}

event <A>::response {
    ...inputs(A),
    ...outputs(A),
    callerPrincipal: principalType(A),
    callerResource: resourceType(A),
    pin session: String = context.session,
}
"#;
    let policy = r#"permit (principal, action == F::Action::"Op", resource)
        when temporal { formerly within 60s F::Action::"A"::response{} };"#;
    let response = |session: &str| {
        format!(
            r#"@100 scope(principal: F::User::"u0", resource: F::Res::"r0") request_context(input: {{ {BASE} }}, session: {session}) F::Action::"A"::response(input: {{ {BASE} }}, output: {{ ok: true, m: 3 }}, callerPrincipal: F::User::"u0", callerResource: F::Res::"r0", session: {session})"#
        )
    };
    let request = |session: &str| {
        format!(
            r#"@101 scope(principal: F::User::"u0", resource: F::Res::"r0") request_context(input: {{ {BASE} }}, session: {session}) F::Action::"Op"::request(input: {{ {BASE} }}, callerPrincipal: F::User::"u0", callerResource: F::Res::"r0", session: {session})"#
        )
    };
    let log = [response("\"s1\""), request("\"s1\"")].join("\n");
    assert_eq!(
        both(F_SCHEMA, events, policy, &log),
        [vec![N, A], vec![N, A]]
    );
    let log = [response("null"), request("\"s1\"")].join("\n");
    assert_eq!(
        both(F_SCHEMA, events, policy, &log),
        [vec![N, D], vec![N, D]]
    );
    let log = [response("null"), request("null")].join("\n");
    assert_eq!(
        both(F_SCHEMA, events, policy, &log),
        [vec![N, D], vec![N, D]]
    );
}

// ── I-2: sets compare as sets ───────────────────────────────────────────────

/// Review I-2 (`set_order`): a response logged `tags: ["a", "b"]` correlates
/// with a request whose `context.input.tags` is `["b", "a"]`: one set, ALLOW.
#[test]
fn i2_a_correlation_compares_sets_as_sets() {
    let policy = r#"permit (principal, action == F::Action::"Op", resource)
        when temporal { formerly within 60s F::Action::"A"::response{ input.tags: context.input.tags } };"#;
    let tags = |t: &str| format!(r#"n: 0, s: "x", d: 1.5, tags: {t}, u: F::User::"u0", b: true"#);
    for (logged, asked, want) in [
        (r#"["a", "b"]"#, r#"["b", "a"]"#, A),
        (r#"["a", "b", "a"]"#, r#"["b", "a"]"#, A),
        (r#"["a", "b"]"#, r#"["a"]"#, D),
        (r#"[]"#, r#"[]"#, A),
    ] {
        let log = [
            a_response(100, &tags(logged)),
            op_request(102, &tags(asked), &tags(asked)),
        ]
        .join("\n");
        assert_eq!(
            both(F_SCHEMA, F_EVENTS, policy, &log),
            [vec![N, want], vec![N, want]],
            "{logged} against {asked}"
        );
    }
}

// The grammar admits neither a set-typed binder nor a set-typed pin, so a set
// reaches a comparison only through a correlation with a request-side value, as
// above; `partition_value_key` is checked on values below.

/// `Value::dom_eq` is the set equality, and `partition_value_key` renders equal
/// sets alike and unequal ones apart.
#[test]
fn i2_value_equality_and_keys_are_set_equality() {
    let s =
        |items: &[&str]| Value::Array(items.iter().map(|i| Value::String(i.to_string())).collect());
    let equal = [
        (s(&["a", "b"]), s(&["b", "a"])),
        (s(&["a", "a", "b"]), s(&["b", "a"])),
        (
            Value::Array(vec![Value::String("a".into()), Value::Null]),
            s(&["a"]),
        ),
        (
            Value::Array(vec![s(&["x", "y"]), s(&["z"])]),
            Value::Array(vec![s(&["z"]), s(&["y", "x"]), s(&["z"])]),
        ),
    ];
    for (x, y) in &equal {
        assert!(x.dom_eq(y) && y.dom_eq(x), "{x:?} = {y:?}");
        assert_eq!(
            partition_value_key(x),
            partition_value_key(y),
            "{x:?} = {y:?}"
        );
    }
    let unequal = [
        (s(&["a", "b"]), s(&["a"])),
        (s(&["ab"]), s(&["a", "b"])),
        (s(&[]), s(&[""])),
    ];
    for (x, y) in &unequal {
        assert!(!x.dom_eq(y) && !y.dom_eq(x), "{x:?} != {y:?}");
        assert_ne!(
            partition_value_key(x),
            partition_value_key(y),
            "{x:?} != {y:?}"
        );
    }
}

// ── Decimals by value (P4) ──────────────────────────────────────────────────

/// A logged `02.5` matches the literal `decimal("2.5")`, and a request-side
/// `2.50` correlates with a logged `02.5` (pins 1.1's verdicts).
#[test]
fn p4_decimals_compare_by_value_in_logged_values_literals_and_correlations() {
    let d = |v: &str| format!(r#"n: 0, s: "x", d: {v}, tags: [], u: F::User::"u0", b: true"#);
    let literal = r#"permit (principal, action == F::Action::"Op", resource)
        when temporal { formerly within 60s F::Action::"A"::response{ input.d: decimal("2.5") } };"#;
    let correlated = r#"permit (principal, action == F::Action::"Op", resource)
        when temporal { formerly within 60s F::Action::"A"::response{ input.d: context.input.d } };"#;
    for (logged, asked, want) in [
        ("02.5", "2.50", A),
        ("-0.0", "0.0", A),
        ("2.5001", "2.5", D),
    ] {
        let log = [
            a_response(100, &d(logged)),
            op_request(102, &d(asked), &d(asked)),
        ]
        .join("\n");
        let want_literal = if logged == "02.5" { A } else { D };
        assert_eq!(
            both(F_SCHEMA, F_EVENTS, literal, &log),
            [vec![N, want_literal], vec![N, want_literal]],
            "{logged}"
        );
        assert_eq!(
            both(F_SCHEMA, F_EVENTS, correlated, &log),
            [vec![N, want], vec![N, want]],
            "{logged} ~ {asked}"
        );
    }
}

// ── Canonical forms ─────────────────────────────────────────────────────────

#[test]
fn canonical_decimal_spellings() {
    for (spelling, canonical) in [
        ("02.5", Some("2.5")),
        ("2.50", Some("2.5")),
        ("2.0000", Some("2.0")),
        ("-0.0", Some("0.0")),
        ("-0.25", Some("-0.25")),
        ("0.0001", Some("0.0001")),
        ("922337203685477.5807", Some("922337203685477.5807")),
        ("-922337203685477.5808", Some("-922337203685477.5808")),
        ("1", None),
        ("1.23456", None),
        (".5", None),
        ("922337203685477.5808", None),
    ] {
        assert_eq!(
            Value::canonical_decimal(spelling).as_deref(),
            canonical,
            "{spelling}"
        );
        if let Some(c) = canonical {
            // The canonical spelling is itself accepted, and canonical.
            assert_eq!(Value::canonical_decimal(c).as_deref(), Some(c), "{c}");
        }
    }
}

fn samples() -> Vec<Value> {
    let s = |x: &str| Value::String(x.to_string());
    let d = |x: &str| Value::Decimal(x.to_string());
    let obj = |m: &[(&str, Value)]| {
        Value::Object(m.iter().map(|(k, v)| (k.to_string(), v.clone())).collect())
    };
    vec![
        Value::Null,
        Value::Bool(true),
        Value::Int(0),
        Value::Int(-3),
        d("2.5"),
        d("02.50"),
        d("-0.0"),
        d("0.0"),
        d("1"),
        d("01"),
        s("2.5"),
        s(""),
        s("<none>"),
        s("a\u{1f}b"),
        Value::Entity {
            ty: "F::User".into(),
            id: "u0".into(),
        },
        Value::Entity {
            ty: "F::User".into(),
            id: "u0\"".into(),
        },
        Value::Array(vec![]),
        Value::Array(vec![s("a"), s("b")]),
        Value::Array(vec![s("b"), s("a"), s("b"), Value::Null]),
        Value::Array(vec![d("1.50"), d("1.5")]),
        Value::Array(vec![
            Value::Array(vec![s("y"), s("x")]),
            Value::Array(vec![s("x"), s("y")]),
        ]),
        obj(&[("a", Value::Int(1))]),
        obj(&[("a", Value::Int(1)), ("b", Value::Null)]),
        obj(&[("a", d("01.0")), ("t", Value::Array(vec![s("q"), s("p")]))]),
        obj(&[("a", d("1.0")), ("t", Value::Array(vec![s("p"), s("q")]))]),
    ]
}

/// `dom_eq` is equality of canonical forms; the canonical form is idempotent and
/// has the same partition key.
#[test]
fn canonical_forms_decide_dom_eq() {
    let values = samples();
    for x in &values {
        let cx = x.canonical();
        assert_eq!(cx.canonical(), cx, "idempotent on {x:?}");
        assert!(x.dom_eq(&cx), "{x:?} = its canonical form");
        assert_eq!(partition_value_key(x), partition_value_key(&cx), "{x:?}");
        for y in &values {
            assert_eq!(x.dom_eq(y), cx == y.canonical(), "{x:?} vs {y:?}");
            assert_eq!(
                x.dom_eq(y),
                partition_value_key(x) == partition_value_key(y),
                "{x:?} vs {y:?}"
            );
        }
    }
}

/// Canonicalizing every event changes no decision, over both temporal corpora:
/// under each case's own event schema in global mode, and under the default
/// (pinned) event schema in partitioned mode. A trace whose events are already
/// canonical decides alike trivially, so only the others are replayed.
#[test]
fn canonical_events_decide_as_the_originals_over_the_corpora() {
    let (mut replayed, mut already) = (0usize, 0usize);
    for case in support::corpus() {
        for (_, trace, _) in &case.traces {
            let Ok(events) = parse_trace(trace) else {
                continue;
            };
            let canonical: Vec<Event> = events.iter().map(Event::canonical).collect();
            if canonical == events {
                already += 1;
                continue;
            }
            for (event_schema, partitioned) in [
                (case.event_schema.clone(), false),
                (dogwood_language::DEFAULT_EVENT_SCHEMA.to_string(), true),
            ] {
                let case = support::Case {
                    event_schema,
                    ..case.clone()
                };
                if case.lower().is_err() {
                    continue;
                }
                let run = |events: &[Event]| {
                    let mut a = if partitioned {
                        Authorizer::builder(case.lower().unwrap())
                            .partition_temporal()
                            .build()
                            .unwrap()
                    } else {
                        Authorizer::new(case.lower().unwrap())
                    };
                    events
                        .iter()
                        .map(|e| a.is_authorized(e).map(|r| r.decision()))
                        .collect::<Vec<_>>()
                };
                assert_eq!(
                    run(&events),
                    run(&canonical),
                    "{} (partitioned: {partitioned})",
                    case.name
                );
                replayed += 1;
            }
        }
    }
    assert!(
        replayed > 20 && already > 500,
        "replayed {replayed}, already canonical {already}"
    );
}
