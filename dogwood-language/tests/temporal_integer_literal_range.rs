//! An integer literal outside the i64 range in a temporal block or a
//! `def temporal` body is rejected at parse time, as in the Cedar dialect.
//! It used to be read as `0`, so `n >= 20000000000000000000` loaded as
//! `n >= 0`.

use dogwood_language::{ParsedPolicySet, ServiceSchema};

/// A rate-limit forbid over a `window`-hour window with threshold `limit`.
fn policy(window: &str, limit: &str) -> String {
    format!(
        r#"forbid (principal, action == Drupe::Action::"Transfer", resource) when temporal {{
    exists (n: Long). (
        (count for (t: Timepoint). where (formerly within {window}h Drupe::Action::"Transfer"::request{{}} && tp(t))) == n
        && n >= {limit}
    )
}};"#
    )
}

fn parse(policy: &str, macros: &str) -> Result<ParsedPolicySet, String> {
    let service = ServiceSchema::builder().macros_str(macros).build();
    ParsedPolicySet::parse(policy, &service.map_err(|e| e.to_string())?).map_err(|e| e.to_string())
}

const BIG: &str = "20000000000000000000";

fn assert_rejected(policy: &str, macros: &str, literal: &str) {
    let err = parse(policy, macros)
        .err()
        .unwrap_or_else(|| panic!("`{literal}` loaded"));
    let expected = format!("integer literal `{literal}` is out of range");
    assert!(err.contains(&expected), "for `{literal}`, got: {err}");
}

#[test]
fn out_of_range_integer_literals_are_rejected() {
    for (window, limit, literal) in [
        ("1", BIG, BIG),
        ("1", "-9223372036854775809", "-9223372036854775809"),
        ("9223372036854775808", "3", "9223372036854775808"),
    ] {
        assert_rejected(&policy(window, limit), "", literal);
    }
    let library = format!("def temporal recently(?s) {{ formerly within {BIG}h ?s }};");
    assert_rejected(&policy("1", "3"), &library, BIG);
}

#[test]
fn in_range_integer_literals_keep_their_value() {
    for (limit, rendered) in [
        ("9223372036854775807", "n >= 9223372036854775807"),
        ("-9223372036854775808", "n >= -9223372036854775808"),
        ("-0", "n >= 0"),
        ("007", "n >= 7"),
    ] {
        let parsed = parse(&policy("1", limit), "").expect("in range");
        let source = parsed
            .policies()
            .next()
            .expect("one policy")
            .expanded_source();
        assert!(source.contains(rendered), "for `{limit}`, got:\n{source}");
    }
}
