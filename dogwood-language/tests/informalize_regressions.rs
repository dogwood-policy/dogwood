//! Regression tests for the informalizer (`dogwood explain`): each rewrite,
//! the cases where it must not apply, and edge cases of the phrasing.

use dogwood_language::{ParsedPolicySet, PolicySchema, ServiceSchema};

fn explain(src: &str, service: &ServiceSchema) -> String {
    let parsed = ParsedPolicySet::parse(src, service).expect("policy parses");
    parsed.informalize(None).to_string()
}

/// Author text containing `{<digits>}` (or doubled braces) is reproduced
/// verbatim rather than read as a template slot, which would panic (`slot
/// {0} out of range`) or splice in the wrong child.
#[test]
fn braces_in_author_text_are_literal() {
    let src = r#"
@id("rule {0}")
@doc("hello {0} world }} {{")
permit (
    principal == Svc::User::"{1}",
    action == Svc::Action::"Read",
    resource
)
when { context["{0}"] == "{0}" && context.input.stock like "{0}*" }
when { { "{0}": 42 } == { foo: 1 } && context has "{0}" };
"#;
    let text = explain(src, &ServiceSchema::defaults());
    for expected in [
        r#"@id("rule {0}")"#,
        r#"Svc::User::"{1}""#,
        r#"(@doc: "hello {0} world }} {{")"#,
        r#"the request's {0} == "{0}""#,
        r#"matches the pattern "{0}*""#,
        "{ {0}: 42 } == { foo: 1 }",
        "the request context has {0}",
    ] {
        assert!(text.contains(expected), "missing {expected:?} in:\n{text}");
    }
}

/// The `when:` row of a single-rule, single-`when` policy over `cond`.
fn when_row(cond: &str) -> String {
    let src = format!(
        "permit (principal, action == Svc::Action::\"Sell\", resource)\nwhen {{ {cond} }};"
    );
    let text = explain(&src, &ServiceSchema::defaults());
    text.lines()
        .find_map(|l| l.trim_start().strip_prefix("when: "))
        .unwrap_or_else(|| panic!("no `when:` row in:\n{text}"))
        .to_string()
}

/// A compound operand is parenthesized, so the prose keeps the AST's
/// grouping instead of reading as a different expression.
#[test]
fn compound_cedar_operands_are_parenthesized() {
    for (cond, expected) in [
        (
            "(context.input.shares + 1) * 2 > 10",
            "(the request's shares + 1) * 2 > 10",
        ),
        (
            "-(context.input.shares - 5) < 0",
            "-(the request's shares - 5) < 0",
        ),
        (
            "context.input.shares - (3 - 1) == 0",
            "the request's shares - (3 - 1) == 0",
        ),
        (
            "(if context.input.stock == \"X\" then 1 else 2) + 3 == 4",
            "(if the request's stock == \"X\" then 1, otherwise 2) + 3 == 4",
        ),
        (
            "(context.input.shares > 1) == (context.input.stock == \"X\")",
            "(the request's shares > 1) == (the request's stock == \"X\")",
        ),
        (
            "(context.input.stock like \"A*\") == false",
            "(the request's stock matches the pattern \"A*\") is false",
        ),
        (
            "(context has input) == true",
            "(the request context has input) is true",
        ),
        (
            "(if context.input.stock == \"X\" then context.input else context.input).shares > 0",
            "the shares field of (if the request's stock == \"X\" then the request's input, otherwise the request's input) > 0",
        ),
    ] {
        assert_eq!(when_row(cond), expected, "for `{cond}`");
    }
}

/// A macro body is an operand like any other once expanded: `f(x) * 2` with
/// `f(?n) = ?n + 1` must not read "x + 1 * 2".
#[test]
fn expanded_macro_operand_is_parenthesized() {
    let src = r#"
def cedar f(?n) { ?n + 1 };
permit (principal, action == Svc::Action::"Sell", resource)
when { f(context.input.shares) * 2 > 10 };
"#;
    let text = explain(src, &ServiceSchema::defaults());
    assert!(
        text.contains("when: (the request's shares + 1) * 2 > 10"),
        "got:\n{text}"
    );
}

/// A nested `if` in the condition or then-branch is fenced (its
/// ", otherwise" would otherwise read as the outer one's); an `else if`
/// chain is not, since it reads naturally.
#[test]
fn nested_if_is_fenced_except_else_if_chain() {
    assert_eq!(
        when_row(
            "if context.input.stock == \"A\" then (if context.input.shares > 1 then true else false) else false"
        ),
        "if the request's stock == \"A\" then (if the request's shares > 1 then true, otherwise false), otherwise false",
    );
    assert_eq!(
        when_row(
            "context.input.shares <= (if context.input.stock == \"A\" then 10 else if context.input.stock == \"B\" then 50 else 1000)"
        ),
        "the request's shares <= (if the request's stock == \"A\" then 10, otherwise if the request's stock == \"B\" then 50, otherwise 1000)",
    );
}

/// Operands that are already self-delimiting stay bare: arithmetic directly
/// under a comparison, request paths, negation, value constructors, calls,
/// and `not (…)`.
#[test]
fn simple_operands_stay_bare() {
    for (cond, expected) in [
        (
            "context.input.shares + 1 <= 10",
            "the request's shares + 1 <= 10",
        ),
        ("-context.input.shares < 0", "-the request's shares < 0"),
        (
            "-(-context.input.shares) < 0",
            "-(-the request's shares) < 0",
        ),
        (
            "!(context.input.stock == \"X\")",
            "not (the request's stock == \"X\")",
        ),
        (
            "context.input.shares * 2 == context.input.shares + context.input.shares",
            "the request's shares * 2 == the request's shares + the request's shares",
        ),
        (
            "context.input.price < decimal(\"0.5\")",
            "the request's price < the decimal \"0.5\"",
        ),
    ] {
        assert_eq!(when_row(cond), expected, "for `{cond}`");
    }
}

/// Action schema for the `action in` tests: `CallTool` is a group of `A`;
/// `Solo` is a plain action. Used only to drop the namespace.
const GROUPS_SCHEMA: &str = r#"
namespace Svc {
  entity User;
  entity Res;
  action "CallTool" appliesTo { principal: [User], resource: [Res] };
  action "A" in [Action::"CallTool"] appliesTo { principal: [User], resource: [Res] };
  action "Solo" appliesTo { principal: [User], resource: [Res] };
}
"#;

/// The action part of the header for `action in <scope>`: the text between
/// "to perform " and " on any resource".
fn action_in_scope(scope: &str, with_schema: bool) -> String {
    let src = format!("permit (principal, action in {scope}, resource);");
    let parsed = ParsedPolicySet::parse(&src, &ServiceSchema::defaults()).expect("policy parses");
    let schema = PolicySchema::from_cedarschema_str(GROUPS_SCHEMA).expect("schema parses");
    let text = parsed
        .informalize(with_schema.then_some(&schema))
        .to_string();
    let (_, rest) = text
        .split_once("to perform ")
        .unwrap_or_else(|| panic!("no header in:\n{text}"));
    let (action, _) = rest
        .split_once(" on any resource")
        .unwrap_or_else(|| panic!("no resource in:\n{text}"));
    action.to_string()
}

/// `action in G` matches G itself and everything grouped under it, so it
/// reads "any action in G", never as the single action G ("one of G"), with
/// or without a schema and whether or not the listed actions have members.
#[test]
fn action_in_reads_any_action_in() {
    for (scope, with_schema, expected) in [
        (r#"Svc::Action::"CallTool""#, true, "any action in CallTool"),
        (r#"Svc::Action::"Solo""#, true, "any action in Solo"),
        (
            r#"[Svc::Action::"Solo", Svc::Action::"A"]"#,
            true,
            "any action in Solo or A",
        ),
        (
            r#"[Svc::Action::"Solo", Svc::Action::"CallTool", Svc::Action::"A"]"#,
            true,
            "any action in Solo, CallTool, or A",
        ),
        (
            r#"Svc::Action::"CallTool""#,
            false,
            r#"any action in Svc::Action::"CallTool""#,
        ),
        (
            r#"[Svc::Action::"Solo", Svc::Action::"A"]"#,
            false,
            r#"any action in Svc::Action::"Solo" or Svc::Action::"A""#,
        ),
    ] {
        assert_eq!(
            action_in_scope(scope, with_schema),
            expected,
            "for `{scope}` (schema: {with_schema})"
        );
    }
}

/// The pin preamble (the lines before the first rule) for a one-rule temporal
/// policy under `event_schema`.
fn pin_preamble(event_schema: &str) -> Vec<String> {
    let service = ServiceSchema::builder()
        .event_schema_str(event_schema)
        .build()
        .expect("event schema builds");
    let src = r#"
permit (principal, action == Svc::Action::"Write", resource)
when temporal { formerly within 1h Svc::Action::"Read"::request{ } };
"#;
    let text = explain(src, &service);
    text.lines()
        .take_while(|l| !l.is_empty() && !l.starts_with("Rule "))
        .map(str::to_string)
        .collect()
}

/// A pin nested in a record field is enforced by the engine, so the preamble
/// must state it (by its dotted path) instead of silently omitting it.
#[test]
fn nested_pin_appears_in_preamble() {
    let event_schema = r#"
decision event <A>::request {
    ...inputs(A),
    __drupe: { pin session_id: String = context.__drupe.session_id },
}

event <A>::response {
    ...inputs(A),
    ...outputs(A),
    __drupe: { pin session_id: String = context.__drupe.session_id },
}
"#;
    assert_eq!(
        pin_preamble(event_schema),
        ["Only past events with this request's __drupe.session_id count."],
    );
}

/// Top-level and nested pins are listed together, per kind when the kinds
/// differ.
#[test]
fn nested_and_top_level_pins_per_kind() {
    let event_schema = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    __drupe: { pin session_id: String = context.__drupe.session_id },
}

event <A>::response {
    ...inputs(A),
    ...outputs(A),
    __drupe: { pin session_id: String = context.__drupe.session_id },
}
"#;
    assert_eq!(
        pin_preamble(event_schema),
        [
            "Only past request events from this request's principal and with this \
             request's __drupe.session_id count.",
            "Only past response events with this request's __drupe.session_id count.",
        ],
    );
}

/// The default schema's principal pin reads "from this request's principal";
/// a pin onto the request's same-named field reads "with this request's …";
/// any other pin reads "whose <field> is <value>".
#[test]
fn pin_preamble_phrasings() {
    let src = r#"
permit (principal, action == Svc::Action::"Write", resource)
when temporal { formerly within 1h Svc::Action::"Read"::request{ } };
"#;
    let text = explain(src, &ServiceSchema::defaults());
    assert_eq!(
        text.lines().next(),
        Some("Only past events from this request's principal count."),
        "full output:\n{text}"
    );

    let event_schema = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerResource: resourceType(A) = resource,
    pin user: String = context.input.user,
    pin approver: String = context.input.user,
}
"#;
    assert_eq!(
        pin_preamble(event_schema),
        [
            // The event's top-level `user` is pinned to the request's
            // `input.user`: different fields, so not "the same user".
            "Only past events on this request's resource and whose user is the \
             request's input user and whose approver is the request's input user count."
        ],
    );

    // Without a top-level `user`, `input.user` reads as just "user".
    let event_schema = r#"
decision event <A>::request {
    ...inputs(A),
    pin approver: String = context.input.user,
}
"#;
    assert_eq!(
        pin_preamble(event_schema),
        ["Only past events whose approver is the request's user count."],
    );
}

/// A single policy's informalization carries the pin preamble when it has a
/// temporal clause (the pins change what it matches) and then reads exactly
/// as it does inside the set; a non-temporal policy gets no preamble.
#[test]
fn single_policy_includes_pin_preamble() {
    let src = r#"
permit (principal, action == Svc::Action::"Sell", resource)
when { context.input.shares < 10 };

permit (principal, action == Svc::Action::"Write", resource)
when temporal { formerly within 1h Svc::Action::"Read"::request{ } };
"#;
    let parsed = ParsedPolicySet::parse(src, &ServiceSchema::defaults()).expect("policy parses");
    let set = parsed.informalize(None);
    let singles: Vec<_> = parsed.policies().map(|p| p.informalize(None)).collect();

    assert_eq!(singles[0].preamble, None);
    assert_eq!(singles[0].rules, [set.rules[0].clone()]);

    assert_eq!(singles[1].preamble, set.preamble);
    assert_eq!(singles[1].rules, [set.rules[1].clone()]);
    let text = singles[1].to_string();
    assert!(
        text.starts_with("Only past events from this request's principal count.\n\nRule 2\n"),
        "got:\n{text}"
    );
}

/// A temporal clause reads "when:" like any other (the temporal phrases say
/// "occurred within …" themselves), and a temporal block inside a Cedar
/// expression adds no framing of its own.
#[test]
fn temporal_clauses_have_no_extra_framing() {
    let src = r#"
permit (principal, action == Svc::Action::"Sell", resource)
when temporal { formerly within 1h Svc::Action::"Read"::request{ } }
when { context.input.shares > 5 && temporal { formerly within 1h Svc::Action::"Sell"::request{ } } };
"#;
    let text = explain(src, &ServiceSchema::defaults());
    let rule: Vec<&str> = text
        .lines()
        .skip_while(|l| !l.starts_with("Rule "))
        .collect();
    assert_eq!(
        rule[2..],
        [
            "  when:",
            "    a Svc::Action::\"Read\" request occurred within the last 1 hour",
            "  when:",
            "    the request's shares > 5",
            "    and a Svc::Action::\"Sell\" request occurred within the last 1 hour",
        ],
        "full output:\n{text}"
    );
}

/// `since` reads in time order: the anchor (right operand) with its window
/// first, then what has (or has not) held at every step since then, so each
/// row is a complete statement and the window clearly bounds the anchor.
#[test]
fn since_reads_anchor_first() {
    let src = r#"
permit (principal, action == Svc::Action::"Write", resource)
when temporal {
    !Svc::Action::"Revoke"::request{ input.user: context.input.user }
    since within 1h
    Svc::Action::"Grant"::request{ input.user: context.input.user }
}
when temporal {
    Svc::Action::"Ping"::request{ } since within 5m Svc::Action::"Login"::request{ }
}
when temporal {
    !(Svc::Action::"Revoke"::request{ } && Svc::Action::"Audit"::request{ })
    since within 1h
    (Svc::Action::"Grant"::request{ } && Svc::Action::"Approve"::request{ })
}
when temporal {
    (Svc::Action::"Ping"::request{ } && Svc::Action::"Pong"::request{ })
    since within 5m
    Svc::Action::"Login"::request{ }
};
"#;
    let text = explain(src, &ServiceSchema::defaults());
    let rule: Vec<&str> = text
        .lines()
        .skip_while(|l| !l.starts_with("Rule "))
        .collect();
    assert_eq!(
        rule[2..],
        [
            "  when:",
            "    a Svc::Action::\"Grant\" request with this request's user occurred within the last 1 hour",
            "    and no Svc::Action::\"Revoke\" request for that user has occurred since then",
            "  when:",
            "    a Svc::Action::\"Login\" request occurred within the last 5 minutes",
            "    and every event since then has been a Svc::Action::\"Ping\" request",
            "  when:",
            "    at some point within the last 1 hour:",
            "      the event is a Svc::Action::\"Grant\" request",
            "      and the event is a Svc::Action::\"Approve\" request",
            "    and at no step since then:",
            "      the event is a Svc::Action::\"Revoke\" request",
            "      and the event is a Svc::Action::\"Audit\" request",
            "  when:",
            "    a Svc::Action::\"Login\" request occurred within the last 5 minutes",
            "    and at every step since then:",
            "      the event is a Svc::Action::\"Ping\" request",
            "      and the event is a Svc::Action::\"Pong\" request",
        ],
        "full output:\n{text}"
    );
}

/// A predicate's same-as-the-request fields merge into one phrase at the
/// position of the first; a `since` whose two sides compare the same fields
/// refers back ("for that …") on its second row, and repeats them otherwise.
#[test]
fn same_as_request_fields_merge_and_back_reference() {
    let src = r#"
permit (principal, action == Svc::Action::"Write", resource)
when temporal {
    formerly within 1h Svc::Action::"Approve"::response{
        input.user: context.input.user, input.amount: 5, input.stock: context.input.stock,
        output.ok: true
    }
}
when temporal {
    Svc::Action::"Ping"::request{ input.user: context.input.user, input.stock: context.input.stock }
    since within 5m
    Svc::Action::"Login"::request{ input.stock: context.input.stock, input.user: context.input.user }
}
when temporal {
    !Svc::Action::"Sell"::request{ input.user: context.input.user, input.stock: context.input.stock }
    since within 1h
    Svc::Action::"Login"::request{ input.user: context.input.user }
};
"#;
    let text = explain(src, &ServiceSchema::defaults());
    let rule: Vec<&str> = text
        .lines()
        .skip_while(|l| !l.starts_with("Rule "))
        .collect();
    assert_eq!(
        rule[2..],
        [
            "  when:",
            "    a Svc::Action::\"Approve\" response with this request's user and stock \
             and amount = 5 and output ok = true occurred within the last 1 hour",
            "  when:",
            "    a Svc::Action::\"Login\" request with this request's stock and user \
             occurred within the last 5 minutes",
            "    and every event since then has been a Svc::Action::\"Ping\" request for that user and stock",
            "  when:",
            "    a Svc::Action::\"Login\" request with this request's user \
             occurred within the last 1 hour",
            "    and no Svc::Action::\"Sell\" request with this request's user and stock \
             has occurred since then",
        ],
        "full output:\n{text}"
    );
}

/// An unconstrained scope reads "any principal" / "any resource", with no
/// list of `appliesTo` types even when a schema is given; constrained scopes
/// keep their type or entity.
#[test]
fn unconstrained_scope_lists_no_types() {
    let header = |scope: &str| -> String {
        let src = format!("permit ({scope});");
        let parsed =
            ParsedPolicySet::parse(&src, &ServiceSchema::defaults()).expect("policy parses");
        let schema = PolicySchema::from_cedarschema_str(GROUPS_SCHEMA).expect("schema parses");
        let text = parsed.informalize(Some(&schema)).to_string();
        text.lines().nth(1).expect("header row").to_string()
    };
    for (scope, expected) in [
        (
            r#"principal, action == Svc::Action::"Solo", resource"#,
            "PERMIT any principal to perform Solo on any resource",
        ),
        (
            r#"principal in Svc::User::"admins", action, resource in Svc::Res::"r1""#,
            r#"PERMIT any principal in User "admins" to perform any action on any resource in Res "r1""#,
        ),
        (
            r#"principal is Svc::User, action == Svc::Action::"Solo", resource == Svc::Res::"r1""#,
            r#"PERMIT any User to perform Solo on the resource Res "r1""#,
        ),
    ] {
        assert_eq!(header(scope), expected, "for `{scope}`");
    }
}

/// A wildcard field always reads "with any f", even where the schemas declare
/// the field required: a wildcard still requires the field in the logged
/// event, and logged events are not checked against the action schema, so
/// leaving it out would describe events the policy rejects.
#[test]
fn wildcard_fields_are_always_kept() {
    const SCHEMA: &str = r#"
namespace Svc {
  entity User;
  entity Res;
  type SellInput = { user: String, notes?: String };
  type SellOutput = { approved: Bool };
  action "Sell" appliesTo {
    principal: [User], resource: [Res],
    context: { input: SellInput, output?: SellOutput }
  };
  action "Alert" appliesTo { principal: [User], resource: [Res], context: {} };
}
"#;
    let src = r#"
permit (principal, action == Svc::Action::"Alert", resource)
when temporal { formerly within 1h Svc::Action::"Sell"::request{ input.user: * } }
when temporal { formerly within 1h Svc::Action::"Sell"::request{ requestId: _ } }
when temporal { formerly within 1h Svc::Action::"Sell"::request{ input.notes: * } }
when temporal { formerly within 1h Svc::Action::"Sell"::response{ output.approved: * } };
"#;
    let parsed = ParsedPolicySet::parse(src, &ServiceSchema::defaults()).expect("policy parses");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema parses");
    let rows: Vec<String> = parsed
        .informalize(Some(&schema))
        .to_string()
        .lines()
        .filter(|l| l.starts_with("    "))
        .map(|l| l.trim().to_string())
        .collect();
    assert_eq!(
        rows,
        [
            "a Sell request with any user occurred within the last 1 hour",
            "a Sell request with any requestId occurred within the last 1 hour",
            "a Sell request with any notes occurred within the last 1 hour",
            "a Sell response with any output approved occurred within the last 1 hour",
        ],
    );
}

/// Aggregates whose timepoint binder only makes each event count once are
/// phrased without it; any other aggregate keeps the general wording.
#[test]
fn aggregate_idioms_hide_the_timepoint_binder() {
    let src = r#"
permit (principal, action == Svc::Action::"Alert", resource)
when temporal {
    (count for (t: Timepoint). where (formerly within 1h (Svc::Action::"Transfer"::request{ } && tp(t)))) == 3
}
when temporal {
    (sum a for (a: Long), (t: Timepoint). where (
        formerly within 24h (Svc::Action::"Refund"::response{ output.amount: a } && tp(t))
    )) <= 100
}
when temporal {
    (count for (t: Timepoint). where (Svc::Action::"Login"::request{ } && tp(t))) == 1
}
when temporal {
    (sum a for (a: Long). where (formerly within 24h Svc::Action::"Refund"::response{ output.amount: a })) <= 100
}
when temporal {
    (count for (u: String). where (formerly within 1h Svc::Action::"Login"::request{ input.user: u })) <= 3
}
when temporal {
    (sum a for (a: Long), (t: Timepoint). where (
        formerly within 1h (Svc::Action::"Transfer"::request{ input.amount: a, input.tags: [a] } && tp(t))
    )) == 3
};
"#;
    let text = explain(src, &ServiceSchema::defaults());
    let rows: Vec<&str> = text
        .lines()
        .filter(|l| l.starts_with("    "))
        .map(str::trim)
        .collect();
    assert_eq!(
        rows,
        [
            "the number of Svc::Action::\"Transfer\" requests within the last 1 hour == 3",
            "the total output amount of Svc::Action::\"Refund\" responses within the last 24 hours <= 100",
            "(the number of Svc::Action::\"Login\" requests, counting only this request itself) == 1",
            // No timepoint in the `for` list: equal amounts are deduplicated,
            // so this is not a per-event total.
            "(the sum of a over the distinct values a for which a Svc::Action::\"Refund\" response \
             with output amount = a occurred within the last 24 hours) <= 100",
            // Counts distinct users, not events.
            "(the number of distinct values u for which a Svc::Action::\"Login\" request with \
             user = u occurred within the last 1 hour) <= 3",
            // `a` also appears inside another field's value: no shortcut, or
            // "tags = [a]" would name a variable never introduced.
            "(the sum of a over the distinct (a, t) for which a Svc::Action::\"Transfer\" request \
             with amount = a and tags = [a] occurred at some timepoint t within the last 1 hour) == 3",
        ],
        "full output:\n{text}"
    );
}

/// `exists (n). (agg == n && n op x)` with `n` used nowhere else reads as the
/// comparison itself; any other use of `n` keeps the binder.
#[test]
fn aggregate_binder_used_once_reads_as_comparison() {
    let count = r#"(count for (t: Timepoint). where (formerly within 1h (Svc::Action::"Sell"::request{ } && tp(t))))"#;
    let src = format!(
        r#"
permit (principal, action == Svc::Action::"Alert", resource)
when temporal {{ exists (n: Long). ({count} == n && n <= 3) }}
when temporal {{ exists (n: Long). (n == {count} && 3 < n) }}
when temporal {{ exists (n: Long). ({count} == n && n > context.input.limit) }}
when temporal {{
    exists (total: Long). ((sum a for (a: Long). where Svc::Action::"Sell"::request{{ input.amount: a }}) == total && total > 200)
}}
when temporal {{ exists (n: Long). ({count} == n && n > 1 && n < 5) }};
"#
    );
    let text = explain(&src, &ServiceSchema::defaults());
    let rule: Vec<&str> = text
        .lines()
        .skip_while(|l| !l.starts_with("Rule "))
        .collect();
    let sells = "the number of Svc::Action::\"Sell\" requests within the last 1 hour";
    assert_eq!(
        rule[2..],
        [
            "  when:".to_string(),
            format!("    {sells} <= 3"),
            "  when:".to_string(),
            format!("    3 < {sells}"),
            "  when:".to_string(),
            format!("    {sells} > the request's limit"),
            "  when:".to_string(),
            "    (the sum of a over the distinct values a for which the current event is a \
             Svc::Action::\"Sell\" request with amount = a) > 200"
                .to_string(),
            // Two filters on `n`: not the idiom, the binder stays.
            "  when:".to_string(),
            "    for some number n:".to_string(),
            format!("      n = {sells}"),
            "      and n > 1".to_string(),
            "      and n < 5".to_string(),
        ],
        "full output:\n{text}"
    );
}

/// `exists (a). (L && a op x)` where `a` is bound by exactly one predicate
/// field in `L` folds the comparison into that field; any other use of `a`
/// keeps the binder.
#[test]
fn single_field_filter_folds_into_the_event() {
    let src = r#"
permit (principal, action == Svc::Action::"Alert", resource)
when temporal {
    exists (a: Long). (formerly within 1h Svc::Action::"Transfer"::request{ input.amount: a } && a > 100)
}
when temporal {
    exists (a: Long). (formerly within 1h Svc::Action::"Transfer"::request{ input.amount: a } && 100 > a)
}
when temporal {
    exists (a: Long). (
        formerly within 1h Svc::Action::"Transfer"::request{ input.amount: a }
        && formerly within 1h Svc::Action::"Login"::request{ }
        && a <= context.input.limit
    )
}
when temporal {
    exists (a: Long). (
        formerly within 1h Svc::Action::"Transfer"::request{ input.amount: a }
        && formerly within 1h Svc::Action::"Refund"::request{ input.amount: a }
        && a > 100
    )
};
"#;
    let text = explain(src, &ServiceSchema::defaults());
    let rule: Vec<&str> = text
        .lines()
        .skip_while(|l| !l.starts_with("Rule "))
        .collect();
    let transfer = "a Svc::Action::\"Transfer\" request";
    assert_eq!(
        rule[2..],
        [
            "  when:".to_string(),
            format!("    {transfer} with amount > 100 occurred within the last 1 hour"),
            "  when:".to_string(),
            format!("    {transfer} with amount < 100 occurred within the last 1 hour"),
            "  when:".to_string(),
            format!("    {transfer} with amount <= the request's limit occurred within the last 1 hour"),
            "    and a Svc::Action::\"Login\" request occurred within the last 1 hour".to_string(),
            // `a` correlates two events: not a single-field filter.
            "  when:".to_string(),
            "    for some amount a:".to_string(),
            format!("      {transfer} with amount = a occurred within the last 1 hour"),
            "      and a Svc::Action::\"Refund\" request with amount = a occurred within the last 1 hour"
                .to_string(),
            "      and a > 100".to_string(),
        ],
        "full output:\n{text}"
    );
}

/// A binder compared inside arithmetic is not a plain filter, so the fold
/// does not apply and the binder is kept.
///
/// EXPERIMENTAL-ARITHMETIC: runs only with the `experimental-arithmetic`
/// feature on; a default build rejects this policy at parse time.
#[cfg(feature = "experimental-arithmetic")]
#[test]
fn arithmetic_operand_keeps_the_binder() {
    let src = r#"
permit (principal, action == Svc::Action::"Alert", resource)
when temporal {
    exists (a: Long). (formerly within 1h Svc::Action::"Transfer"::request{ input.amount: a } && context.input.amount <= a + 50)
};
"#;
    let text = explain(src, &ServiceSchema::defaults());
    let rule: Vec<&str> = text
        .lines()
        .skip_while(|l| !l.starts_with("Rule "))
        .collect();
    assert_eq!(
        rule[2..],
        [
            "  when:".to_string(),
            "    for some amount a:".to_string(),
            "      a Svc::Action::\"Transfer\" request with amount = a occurred within the last 1 hour".to_string(),
            "      and the request's amount <= a + 50".to_string(),
        ],
        "full output:\n{text}"
    );
}

/// A binder is named after the field it is bound to when every such field
/// has the same name (and the binder is not itself named so), else after its
/// type.
#[test]
fn binder_named_after_its_field() {
    let src = r#"
permit (principal, action == Svc::Action::"Alert", resource)
when temporal {
    exists (u: String). (
        formerly within 1h Svc::Action::"Login"::request{ input.user: u }
        && formerly within 1h Svc::Action::"Transfer"::request{ input.user: u }
    )
}
when temporal {
    exists (x: String). (
        formerly within 1h Svc::Action::"Login"::request{ input.user: x }
        && formerly within 1h Svc::Action::"Transfer"::request{ input.payee: x }
    )
}
when temporal {
    exists (user: String). (
        formerly within 1h Svc::Action::"Login"::request{ input.user: user }
        && formerly within 1h Svc::Action::"Transfer"::request{ input.user: user }
    )
}
when temporal {
    exists (v: String). (
        formerly within 1h Svc::Action::"Login"::request{ input.user: v }
        && (count for (v: String). where (formerly within 1h Svc::Action::"Transfer"::request{ input.payee: v })) > 2
    )
};
"#;
    let text = explain(src, &ServiceSchema::defaults());
    let heads: Vec<&str> = text
        .lines()
        .map(str::trim)
        .filter(|l| l.starts_with("for some"))
        .collect();
    assert_eq!(
        heads,
        [
            "for some user u:",
            "for some string x:",
            "for some string user:",
            // The aggregate's own `v` (bound to `payee`) is a different
            // variable, so the outer `v` is named after `user` alone.
            "for some user v:",
        ],
        "full output:\n{text}"
    );
}

/// An event schema with a top-level `user` field alongside `input.user`, so
/// two different fields share a short name.
const TOP_LEVEL_USER_EVENTS: &str = r#"
decision event <A>::request {
    ...inputs(A),
    user: String,
}

event <A>::response {
    ...inputs(A),
    ...outputs(A),
    user: String,
}
"#;

fn explain_with_events(src: &str, event_schema: &str) -> String {
    let service = ServiceSchema::builder()
        .event_schema_str(event_schema)
        .build()
        .expect("event schema builds");
    explain(src, &service)
}

/// A `since` refers back ("for that …") only when both sides compare the
/// same fields by path; `user` and `input.user` are different fields.
#[test]
fn since_back_reference_compares_field_paths() {
    let src = r#"
permit (principal, action == Svc::Action::"Alert", resource)
when temporal {
    !Svc::Action::"Transfer"::request{ user: context.user }
    since within 1h
    Svc::Action::"Login"::request{ input.user: context.input.user }
};
"#;
    let text = explain_with_events(src, TOP_LEVEL_USER_EVENTS);
    assert!(
        !text.contains("for that"),
        "must not refer back across different fields:\n{text}"
    );
}

/// `input.` is dropped from a field name only when no other field in the
/// rule reads the same: with a top-level `user` in play, `input.user` keeps
/// its group, in Cedar paths and predicate fields alike.
#[test]
fn input_group_kept_when_short_name_is_ambiguous() {
    let src = r#"
permit (principal, action == Svc::Action::"Alert", resource)
when { context.input.user like "a*" && context.user like "b*" && context.input.amount > 1 }
when temporal {
    formerly within 1h Svc::Action::"Transfer"::request{ input.user: context.input.user, user: context.user }
};

permit (principal, action == Svc::Action::"Alert", resource)
when { context.input.user like "a*" };
"#;
    let text = explain_with_events(src, TOP_LEVEL_USER_EVENTS);
    let rows: Vec<&str> = text
        .lines()
        .filter(|l| l.starts_with("    "))
        .map(str::trim)
        .collect();
    assert_eq!(
        rows,
        [
            "the request's input user matches the pattern \"a*\"",
            "and the request's user matches the pattern \"b*\"",
            "and the request's amount > 1",
            "a Svc::Action::\"Transfer\" request with this request's input user and user \
             occurred within the last 1 hour",
        ],
        "full output:\n{text}"
    );
    // Decided per rule: the second rule has no top-level `user`.
    assert!(
        text.contains("when: the request's user matches the pattern \"a*\""),
        "full output:\n{text}"
    );
}

/// A comparison folded into an event under a past operator is phrased at
/// that past event: an aggregate in it reads "counting only that event
/// itself", not "this request itself".
#[test]
fn folded_filter_keeps_the_past_scan() {
    let src = r#"
permit (principal, action == Svc::Action::"Alert", resource)
when temporal {
    formerly within 1h (
        exists (a: Long). (
            Svc::Action::"Transfer"::request{ input.amount: a }
            && a > (count for (t: Timepoint). where (Svc::Action::"Login"::request{ } && tp(t)))
        )
    )
};
"#;
    let text = explain(src, &ServiceSchema::defaults());
    assert!(
        text.contains(
            "within the last 1 hour, at some point: the event is a Svc::Action::\"Transfer\" request \
             with amount > (the number of Svc::Action::\"Login\" requests, counting only that event itself)"
        ),
        "full output:\n{text}"
    );
}

/// Text after a multi-row operand (a closing parenthesis, a trailing
/// comparison) stays on that operand's last row rather than on a detached
/// row of its own.
#[test]
fn text_after_a_multi_row_operand_stays_attached() {
    let src = r#"
permit (principal, action == Svc::Action::"Alert", resource)
when { (context.input.a > 1 && context.input.b > 2) == context.input.c }
when temporal {
    (sum a for (a: Long), (t: Timepoint). where (
        formerly within 1h (Svc::Action::"Transfer"::request{ input.amount: a } && !Svc::Action::"Refund"::request{ } && tp(t))
    )) > 1000
};
"#;
    let text = explain(src, &ServiceSchema::defaults());
    let rule: Vec<&str> = text
        .lines()
        .skip_while(|l| !l.starts_with("Rule "))
        .collect();
    assert_eq!(
        rule[2..],
        [
            "  when:",
            "    (the request's a > 1",
            "      and the request's b > 2) == the request's c",
            "  when:",
            "    (the sum of a over the distinct (a, t) for which within the last 1 hour, at some point:",
            "      the event is a Svc::Action::\"Transfer\" request with amount = a",
            "      and not (the event is a Svc::Action::\"Refund\" request)",
            "      and that timepoint is t) > 1000",
        ],
        "full output:\n{text}"
    );
}

/// A comparison with a boolean literal reads "is true" / "is not false"
/// (either side, compound operands fenced); a field of anything other than
/// the request reads "the f field of …"; an event field keeps "= true".
#[test]
fn booleans_and_fields_of_values_read_plainly() {
    let src = r#"
permit (principal, action == Svc::Action::"Sell", resource)
when {
    context.input.ok == true
    && false != context.input.ok
    && (context.input.n > 1) == false
    && Text::Scan(context.input.notes).flagged == true
}
when temporal {
    exists (b: Bool). (formerly within 1h Svc::Action::"Sell"::request{ input.ok: b } && b == true)
}
when temporal { formerly within 1h Svc::Action::"Sell"::response{ output.ok: true } };
"#;
    let text = explain(src, &ServiceSchema::defaults());
    let rows: Vec<&str> = text
        .lines()
        .filter(|l| l.starts_with("    "))
        .map(str::trim)
        .collect();
    assert_eq!(
        rows,
        [
            "the request's ok is true",
            "and the request's ok is not false",
            "and (the request's n > 1) is false",
            "and the flagged field of Text::Scan(the request's notes) is true",
            "a Svc::Action::\"Sell\" request with ok = true occurred within the last 1 hour",
            "a Svc::Action::\"Sell\" response with output ok = true occurred within the last 1 hour",
        ],
        "full output:\n{text}"
    );
}

/// A field compared with the request's own reads "this request's f", which
/// cannot be misread as the events sharing a value among themselves.
#[test]
fn same_as_request_reads_as_this_requests_field() {
    let src = r#"
permit (principal, action == Svc::Action::"Sell", resource)
when temporal {
    (count for (t: Timepoint). where (
        formerly within 1h (Svc::Action::"Sell"::request{ input.user: context.input.user } && tp(t))
    )) <= 3
};
"#;
    let text = explain(src, &ServiceSchema::defaults());
    assert!(
        text.starts_with("Only past events from this request's principal count.\n"),
        "full output:\n{text}"
    );
    assert!(
        text.contains(
            "the number of Svc::Action::\"Sell\" requests with this request's user within the last 1 hour <= 3"
        ),
        "full output:\n{text}"
    );
}

/// A macro-minted binder is named as the rendered policy names it: the first
/// free surface name, never one a user binder in the same condition already
/// has (so `explain` and `expanded_source` agree and never conflate them).
#[test]
fn macro_binder_names_match_render_and_avoid_user_binders() {
    let policy = |user_binder: Option<&str>| {
        let extra = user_binder
            .map(|b| {
                format!(
                    " && exists ({b}: Timepoint). formerly within 2h (Svc::Action::\"B\"::request{{ }} && tp({b}))"
                )
            })
            .unwrap_or_default();
        format!(
            r#"
def temporal seen(?s) {{ exists ($t: Timepoint). formerly within 1h (?s && tp($t)) }};
permit (principal, action == Svc::Action::"Alert", resource)
when temporal {{ seen(Svc::Action::"A"::request{{ }}){extra} }};
"#
        )
    };
    let binders = |src: &str| -> (Vec<String>, String) {
        let parsed = ParsedPolicySet::parse(src, &ServiceSchema::defaults()).expect("parses");
        let rendered = parsed
            .policies()
            .next()
            .expect("one policy")
            .expanded_source();
        let text = parsed.informalize(None).to_string();
        let names = text
            .lines()
            .filter_map(|l| l.split_once("for some timepoint "))
            .map(|(_, rest)| rest.split(':').next().expect("binder").to_string())
            .collect();
        (names, rendered)
    };

    // The macro's binder alone: whatever render calls it, explain agrees.
    let (names, rendered) = binders(&policy(None));
    let [gensym] = names.as_slice() else {
        panic!("one binder expected, got {names:?}");
    };
    assert!(
        rendered.contains(&format!("({gensym}: Timepoint)")),
        "{rendered}"
    );

    // A user binder with that very name: the macro's binder moves aside.
    let (names, rendered) = binders(&policy(Some(gensym)));
    assert_eq!(names, [format!("{gensym}_1"), gensym.clone()]);
    assert!(
        rendered.contains(&format!("({gensym}_1: Timepoint)")),
        "{rendered}"
    );
}
