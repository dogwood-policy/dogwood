//! Record keys, row by row against Cedar's parser.
//!
//! As in Cedar, a record key is a string literal or an unqualified name, read
//! from its tokens, and appears at most once; keys compare after decoding.
//! Dogwood used to take a key from the key's source text, so a comment after
//! the key made a valid record fail to load, and `{ a.b: 1 }`, `{ true: 1 }`,
//! and `{ ("a"): 1 }` loaded with keys Cedar does not allow. It also kept the
//! last value of a repeated key, which Cedar refuses.
//!
//! Each row of `CASES` is one condition and states, and the test checks:
//!
//! 1. what Cedar does with it: accepts, or refuses with a given error;
//! 2. what Dogwood does with it: lowers to the Cedar condition Cedar gives the
//!    same text, or refuses with a given error;
//! 3. for a row Dogwood lowers, the condition `expanded_source` renders, that
//!    the rendered policy lowers to the same Cedar condition as the authored
//!    one, and that rendering the rendered policy changes nothing.
//!
//! Keys Dogwood accepts and Cedar refuses (`{ if: 1 }`, and names Cedar
//! reserves such as `{ in: 1 }`) are not rows yet.

use cedar_policy_core::ast::{self, Expr};
use cedar_policy_core::parser::parse_policyset;
use dogwood_language::{Error, LoweredPolicySet, ParsedPolicySet, PolicySchema, ServiceSchema};

const SCHEMA: &str = r#"namespace Ns {
  type In = { flag: Bool };
  entity User;
  entity Res;
  action "Call" appliesTo {
    principal: [User], resource: [Res],
    context: { input: In }
  };
}"#;

/// Dogwood's error for a key that is not a string literal or a name.
const INVALID: &str = "record keys must be identifiers or string literals";
/// Both parsers' error for an escape a string does not admit.
const BAD_ESCAPE: &str = "is not a valid escape";
/// Cedar's error for a key that is an expression other than a name.
const CEDAR_INVALID: &str = "invalid attribute name";
/// Cedar's error for a qualified name as a key.
const CEDAR_QUALIFIED: &str = "cannot be used as an attribute as it contains a namespace";
/// Cedar's error for a reserved word as a key.
const CEDAR_RESERVED: &str = "this identifier is reserved and cannot be used";

enum Cedar {
    Accepts,
    /// Refuses, with an error containing this text.
    Refuses(&'static str),
}

enum Dogwood {
    /// Lowers to what Cedar makes of the same text; `rendered` is the
    /// condition `expanded_source` writes.
    AsCedar { rendered: &'static str },
    /// Refuses, with a parse error containing this text.
    Refuses(&'static str),
}

struct Case {
    condition: &'static str,
    cedar: Cedar,
    dogwood: Dogwood,
}

const fn accepted(condition: &'static str, rendered: &'static str) -> Case {
    Case {
        condition,
        cedar: Cedar::Accepts,
        dogwood: Dogwood::AsCedar { rendered },
    }
}

const fn refused(condition: &'static str, cedar: &'static str, dogwood: &'static str) -> Case {
    Case {
        condition,
        cedar: Cedar::Refuses(cedar),
        dogwood: Dogwood::Refuses(dogwood),
    }
}

const CASES: &[Case] = &[
    // ─── Names ──────────────────────────────────────────────────────────
    accepted("{ a: 1 } == {}", "({ a: 1 } == {})"),
    accepted("{ _x9: 1, b: 2 } == {}", "({ _x9: 1, b: 2 } == {})"),
    accepted("{ b: 1, a: 2, } == {}", "({ a: 2, b: 1 } == {})"),
    accepted(
        "{ principal: 1, action: 2, resource: 3, context: 4 } == {}",
        "({ action: 2, context: 4, principal: 1, resource: 3 } == {})",
    ),
    accepted(
        "{ permit: 1, forbid: 2, when: 3, unless: 4 } == {}",
        "({ forbid: 2, permit: 1, unless: 4, when: 3 } == {})",
    ),
    accepted("{ a: { b: 1 } } == {}", "({ a: { b: 1 } } == {})"),
    accepted(
        "{ temporal: 1, def: 2, cedar: 3, guardrails: 4 } == {}",
        "({ cedar: 3, def: 2, guardrails: 4, temporal: 1 } == {})",
    ),
    accepted("{ a // c\n : 1 } == {}", "({ a: 1 } == {})"),
    accepted("{ a : // c\n 1 } == {}", "({ a: 1 } == {})"),
    // ─── String literals ────────────────────────────────────────────────
    accepted(r#"{ "a": 1 } == {}"#, "({ a: 1 } == {})"),
    accepted(r#"{ "": 1 } == {}"#, r#"({ "": 1 } == {})"#),
    accepted(r#"{ "a b": 1 } == {}"#, r#"({ "a b": 1 } == {})"#),
    accepted(r#"{ "a\u{62}": 1 } == {}"#, "({ ab: 1 } == {})"),
    accepted(r#"{ "a\"b": 1 } == {}"#, r#"({ "a\"b": 1 } == {})"#),
    // Keys compare as decoded strings, with no Unicode normalization.
    accepted(
        r#"{ "\u{e9}": 1, "e\u{301}": 2 } == {}"#,
        "({ \"e\u{301}\": 2, \"\u{e9}\": 1 } == {})",
    ),
    accepted(
        r#"{ "\u{1F600}": 1 } == {}"#,
        "({ \"\u{1F600}\": 1 } == {})",
    ),
    accepted(
        r#"{ "true": 1, "in": 2, "if": 3, "__cedar": 4 } == {}"#,
        r#"({ "__cedar": 4, "if": 3, "in": 2, "true": 1 } == {})"#,
    ),
    accepted(
        r#"{ "a" // c
 : 1 } == {}"#,
        "({ a: 1 } == {})",
    ),
    // ─── Paths and qualified names ──────────────────────────────────────
    refused("{ principal.b: 1 } == {}", CEDAR_INVALID, INVALID),
    refused("{ context.input.path: 1 } == {}", CEDAR_INVALID, INVALID),
    refused("{ Ns::a: 1 } == {}", CEDAR_QUALIFIED, INVALID),
    refused(r#"{ Ns::User::"a": 1 } == {}"#, CEDAR_INVALID, INVALID),
    // ─── Literals other than a string ───────────────────────────────────
    refused("{ true: 1 } == {}", CEDAR_RESERVED, INVALID),
    refused("{ false: 1 } == {}", CEDAR_RESERVED, INVALID),
    refused("{ 5: 1 } == {}", CEDAR_INVALID, INVALID),
    // ─── Parentheses and other expressions ──────────────────────────────
    refused(r#"{ ("a"): 1 } == {}"#, CEDAR_INVALID, INVALID),
    refused("{ (principal): 1 } == {}", CEDAR_INVALID, INVALID),
    refused("{ -1: 1 } == {}", CEDAR_INVALID, INVALID),
    refused("{ !true: 1 } == {}", CEDAR_INVALID, INVALID),
    refused(r#"{ ip("1.2.3.4"): 1 } == {}"#, CEDAR_INVALID, INVALID),
    refused("{ 1 + 1: 1 } == {}", CEDAR_INVALID, INVALID),
    refused("{ [1]: 1 } == {}", CEDAR_INVALID, INVALID),
    refused("{ {}: 1 } == {}", CEDAR_INVALID, INVALID),
    refused("{ ?principal: 1 } == {}", CEDAR_INVALID, INVALID),
    refused("{ ?resource: 1 } == {}", CEDAR_INVALID, INVALID),
    // ─── An escape a string does not admit ──────────────────────────────
    refused(r#"{ "a\q": 1 } == {}"#, BAD_ESCAPE, BAD_ESCAPE),
    // ─── A repeated key ─────────────────────────────────────────────────
    refused(
        "{ a: 1, a: 2 } == {}",
        "duplicate key `a` in record literal",
        "duplicate key `a` in record literal",
    ),
    refused(
        r#"{ "a": 1, a: 2 } == {}"#,
        "duplicate key `a` in record literal",
        "duplicate key `a` in record literal",
    ),
    refused(
        r#"{ a: 1, "\u{61}": 2 } == {}"#,
        "duplicate key `a` in record literal",
        "duplicate key `a` in record literal",
    ),
    refused(
        "{ a: { b: 1 }, b: 2, a: 3 } == {}",
        "duplicate key `a` in record literal",
        "duplicate key `a` in record literal",
    ),
    refused(
        r#"{ a: 1, "\x61": 2 } == {}"#,
        "duplicate key `a` in record literal",
        "duplicate key `a` in record literal",
    ),
    refused(
        r#"{ "\u{1F600}": 1, "😀": 2 } == {}"#,
        "duplicate key `😀` in record literal",
        "duplicate key `😀` in record literal",
    ),
    refused(
        "{ b: { a: 1, a: 2 } } == {}",
        "duplicate key `a` in record literal",
        "duplicate key `a` in record literal",
    ),
    refused(
        "[{ a: 1, a: 2 }] == []",
        "duplicate key `a` in record literal",
        "duplicate key `a` in record literal",
    ),
    refused(
        r#"{ a: 1, a: 1 + "x" } == {}"#,
        "duplicate key `a` in record literal",
        "duplicate key `a` in record literal",
    ),
    // Cedar refuses `if` as a key; Dogwood accepts one, but not two.
    refused(
        "{ if: 1, if: 2 } == {}",
        CEDAR_RESERVED,
        "duplicate key `if` in record literal",
    ),
    refused(
        r#"{ if: 1, "if": 2 } == {}"#,
        CEDAR_RESERVED,
        "duplicate key `if` in record literal",
    ),
];

fn policy(condition: &str) -> String {
    format!(
        "permit (principal, action == Ns::Action::\"Call\", resource) \
         when {{ {condition} }};"
    )
}

fn lower(src: &str) -> Result<LoweredPolicySet, Error> {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema parses");
    LoweredPolicySet::from_str(src, &ServiceSchema::defaults(), &schema)
}

fn expanded_source(src: &str) -> String {
    let parsed = ParsedPolicySet::parse(src, &ServiceSchema::defaults()).expect("source parses");
    let policy = parsed.policies().next().expect("one policy");
    policy.expanded_source()
}

/// The condition of the single policy in `set`.
fn condition(set: &ast::PolicySet) -> Expr {
    let mut policies = set.policies();
    let policy = policies.next().expect("one policy");
    assert!(policies.next().is_none(), "one policy");
    policy.condition()
}

/// The condition of the single policy Dogwood lowered, from its Cedar AST.
fn lowered_condition(lowered: &LoweredPolicySet) -> Expr {
    condition(lowered.as_cedar().as_ref())
}

/// The parse error lowering produced, or what happened instead.
fn parse_error(result: Result<LoweredPolicySet, Error>) -> Result<String, String> {
    match result {
        Ok(lowered) => Err(format!(
            "lowered to {}",
            lowered.as_cedar().to_string().trim()
        )),
        Err(Error::Parse(errs)) => Ok(errs.iter().map(|e| e.to_string()).collect()),
        Err(other) => Err(format!("not a parse error: {other}")),
    }
}

/// Checks one row, returning a description of each way it does not hold.
fn check(case: &Case) -> Vec<String> {
    let mut failures = Vec::new();
    let src = policy(case.condition);

    // 1. Cedar.
    let cedar = parse_policyset(&src);
    match (&case.cedar, &cedar) {
        (Cedar::Accepts, Ok(_)) => {}
        (Cedar::Accepts, Err(e)) => failures.push(format!("Cedar refuses it: {e}")),
        (Cedar::Refuses(_), Ok(_)) => failures.push("Cedar accepts it".to_string()),
        (Cedar::Refuses(expected), Err(e)) => {
            let message = e.iter().map(|e| e.to_string()).collect::<String>();
            if !message.contains(expected) {
                failures.push(format!("Cedar's error `{message}` lacks `{expected}`"));
            }
        }
    }

    // 2. Dogwood.
    let rendered = match &case.dogwood {
        Dogwood::Refuses(expected) => {
            match parse_error(lower(&src)) {
                Ok(message) if message.contains(expected) => {}
                Ok(message) => failures.push(format!("error `{message}` lacks `{expected}`")),
                Err(outcome) => failures.push(outcome),
            }
            return failures;
        }
        Dogwood::AsCedar { rendered } => *rendered,
    };
    let expected = match &cedar {
        Ok(set) => condition(set),
        Err(_) => {
            failures.push("AsCedar for text Cedar refuses".to_string());
            return failures;
        }
    };
    let lowered = match lower(&src) {
        Ok(lowered) => lowered,
        Err(e) => {
            failures.push(format!("does not lower: {e}"));
            return failures;
        }
    };
    let actual = lowered_condition(&lowered);
    if !actual.eq_shape(&expected) {
        failures.push(format!("lowers to {actual}, not {expected}"));
    }

    // 3. The round trip through `expanded_source`.
    let once = expanded_source(&src);
    let condition = once
        .split_once("when { ")
        .and_then(|(_, rest)| rest.strip_suffix(" };"))
        .unwrap_or(&once);
    if condition != rendered {
        failures.push(format!("renders as `{condition}`, not `{rendered}`"));
    }
    match lower(&once) {
        Ok(relowered) => {
            let relowered = lowered_condition(&relowered);
            if !relowered.eq_shape(&actual) {
                failures.push(format!("rendered form lowers to {relowered}, not {actual}"));
            }
            let twice = expanded_source(&once);
            if twice != once {
                failures.push(format!(
                    "rendering is not idempotent: `{once}` then `{twice}`"
                ));
            }
        }
        Err(e) => failures.push(format!("rendered form `{once}` does not lower: {e}")),
    }
    failures
}

#[test]
fn every_record_key_matches_its_row() {
    let failures: Vec<String> = CASES
        .iter()
        .flat_map(|case| {
            check(case)
                .into_iter()
                .map(move |f| format!("{:?}: {f}", case.condition))
        })
        .collect();
    assert!(failures.is_empty(), "\n{}", failures.join("\n"));
}

/// Records in a `def cedar` body and in a macro argument follow the same
/// rules, and a macro parameter is not a key. Cedar has no macros, so these
/// are not rows of `CASES`.
#[test]
fn macro_records_follow_the_same_rules() {
    let with = |defs: &str, condition: &str| format!("{defs}\n{}", policy(condition));
    let duplicate = "duplicate key `a` in record literal";

    for (defs, condition, expected) in [
        ("def cedar m() { { a: 1, a: 2 } == {} };", "m()", duplicate),
        ("def cedar m() { { a: 1, a: 2 } == {} };", "true", duplicate),
        (
            "def cedar m(?r) { ?r == {} };",
            "m({ a: 1, a: 2 })",
            duplicate,
        ),
        ("def cedar m(?x) { { ?x: 1 } == {} };", "m(1)", INVALID),
    ] {
        let src = with(defs, condition);
        match parse_error(lower(&src)) {
            Ok(message) => assert!(message.contains(expected), "{src}: error `{message}`"),
            Err(outcome) => panic!("{src}: {outcome}"),
        }
    }

    let src = with("def cedar m(?v) { { a: ?v } == {} };", "m(1)");
    lower(&src).unwrap_or_else(|e| panic!("{src}: {e}"));
    let rendered = expanded_source(&src);
    assert!(rendered.contains("({ a: 1 } == {})"), "{rendered}");
}
