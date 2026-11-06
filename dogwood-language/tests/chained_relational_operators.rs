//! A chain of relational operators such as `a == b == c` is rejected at
//! parse time, as in Cedar. It used to be folded left, so
//! `context.x == false == false` loaded as `(context.x == false) == false`,
//! which is `context.x`: the inverse of the chained reading.

use dogwood_language::{ParsedPolicySet, ServiceSchema};

fn parse(condition: &str) -> Result<ParsedPolicySet, String> {
    parse_with_macros(condition, "")
}

fn parse_with_macros(condition: &str, macros: &str) -> Result<ParsedPolicySet, String> {
    let policy = format!("{macros}\nforbid (principal, action, resource) when {{ {condition} }};");
    let service = ServiceSchema::builder().build();
    ParsedPolicySet::parse(&policy, &service.map_err(|e| e.to_string())?).map_err(|e| e.to_string())
}

#[test]
fn relational_chains_are_rejected() {
    for condition in [
        "context.x == false == false",
        "context.x != true != true",
        "1 < 2 == true",
        "principal in resource in action",
        "context.a == context.b == context.c == context.d",
    ] {
        let err = parse(condition)
            .err()
            .unwrap_or_else(|| panic!("`{condition}` loaded"));
        assert!(
            err.contains("multiple relational operators"),
            "for `{condition}`, got: {err}"
        );
    }
}

#[test]
fn parenthesized_chains_keep_their_grouping() {
    for (condition, rendered) in [
        (
            "(context.x == false) == false",
            "(context.x == false) == false",
        ),
        (
            "context.x == (false == false)",
            "context.x == (false == false)",
        ),
        ("context.x == false", "context.x == false"),
    ] {
        let parsed = parse(condition).expect("parenthesized");
        let source = parsed
            .policies()
            .next()
            .expect("one policy")
            .expanded_source();
        assert!(
            source.contains(rendered),
            "for `{condition}`, got:\n{source}"
        );
    }
}

#[test]
fn macros_reject_chains_in_their_body_but_not_across_an_argument() {
    let Err(err) = parse_with_macros("f()", "def cedar f() { context.x == false == false };")
    else {
        panic!("a chained macro body loaded");
    };
    assert!(err.contains("multiple relational operators"), "got: {err}");

    // The argument is substituted as an operand, so it keeps its grouping.
    let parsed = parse_with_macros("g(context.x == false)", "def cedar g(?x) { ?x == false };")
        .expect("a comparison passed to a macro");
    let source = parsed
        .policies()
        .next()
        .expect("one policy")
        .expanded_source();
    assert!(
        source.contains("(context.x == false) == false"),
        "got:\n{source}"
    );
}
