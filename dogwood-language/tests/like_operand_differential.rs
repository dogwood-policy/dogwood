//! The right-hand side of `like`, row by row against Cedar's parser.
//!
//! The grammar admits any `add` after `like`, as Cedar's does, and Cedar then
//! refuses every operand that is not a single string literal. Dogwood used to
//! build the pattern from the first string literal anywhere in the operand and
//! drop the rest, so `like "~/secrets" + "/*"` matched `"~/secrets"`, and
//! `like context.prefix + "/*"` matched `"/*"`.
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
//! Conditions are compared as Cedar ASTs, with Cedar's structural equality
//! (`Expr::eq_shape`, which ignores source locations): Cedar's parse of the
//! text on one side, and on the other the Cedar policy set Dogwood lowers to,
//! read directly rather than printed and parsed again.

use cedar_policy_core::ast::{self, Expr};
use cedar_policy_core::parser::parse_policyset;
use dogwood_language::{Error, LoweredPolicySet, ParsedPolicySet, PolicySchema, ServiceSchema};

const SCHEMA: &str = r#"namespace Ns {
  type In = { path: String, prefix: String, suffix: String, flag: Bool };
  entity User;
  entity Res;
  action "Call" appliesTo {
    principal: [User], resource: [Res],
    context: { input: In }
  };
}"#;

/// Cedar's error for an operand that is not a pattern literal.
const CEDAR_INVALID: &str = "must be a pattern literal";
/// Dogwood's error for an operand that is not a string literal.
const INVALID: &str = "`like` requires a string-literal pattern";
/// Both parsers' error for an escape a pattern does not admit.
const BAD_ESCAPE: &str = "is not a valid escape";

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
    // ─── A single string literal: both accept, and lower alike ──────────
    accepted(
        r#"context.input.path like "/home/u/secrets/*""#,
        r#"context.input.path like "/home/u/secrets/*""#,
    ),
    accepted(r#"context.input.path like "*""#, r#"context.input.path like "*""#),
    accepted(r#"context.input.path like """#, r#"context.input.path like """#),
    accepted(
        r#"context.input.path like "a*b*c""#,
        r#"context.input.path like "a*b*c""#,
    ),
    accepted(
        r#"context.input.path like "a\*b""#,
        r#"context.input.path like "a\*b""#,
    ),
    accepted(
        r#"context.input.path like "a\\*""#,
        r#"context.input.path like "a\\*""#,
    ),
    accepted(
        r#"context.input.path like "a\"b*""#,
        r#"context.input.path like "a\"b*""#,
    ),
    accepted(
        r#"context.input.path like "a\u{2d}b""#,
        r#"context.input.path like "a-b""#,
    ),
    accepted(
        r#"context.input.path   like    "a/*""#,
        r#"context.input.path like "a/*""#,
    ),
    accepted(
        "context.input.path like\n\"a/*\"",
        r#"context.input.path like "a/*""#,
    ),
    accepted(
        "context.input.path like // a comment\n \"a/*\"",
        r#"context.input.path like "a/*""#,
    ),
    accepted(
        r#"context.input.path like"a/*""#,
        r#"context.input.path like "a/*""#,
    ),
    accepted(
        "context.input.path like \"a/*\" // a comment\n",
        r#"context.input.path like "a/*""#,
    ),
    // `\u{2a}` decodes to `*`, which is a wildcard in both parsers.
    accepted(
        r#"context.input.path like "a\u{2a}""#,
        r#"context.input.path like "a*""#,
    ),
    accepted(
        r#"context.input.path like "a\u{1F600}*""#,
        "context.input.path like \"a\u{1F600}*\"",
    ),
    accepted(r#"context.input.path like "\0""#, r#"context.input.path like "\0""#),
    // The literal ends the operand; a lower-precedence operator after it is
    // not part of the pattern.
    accepted(
        r#"context.input.path like "a/*" && context.input.flag"#,
        r#"((context.input.path like "a/*") && context.input.flag)"#,
    ),
    accepted(
        r#"context.input.path like "a/*" || context.input.path like "b/*""#,
        r#"((context.input.path like "a/*") || (context.input.path like "b/*"))"#,
    ),
    accepted(
        r#"!(context.input.path like "a/*")"#,
        r#"!(context.input.path like "a/*")"#,
    ),
    // ─── Operators: the first literal used to be the pattern ────────────
    refused(
        r#"context.input.path like "/home/u/secrets" + "/*""#,
        CEDAR_INVALID,
        INVALID,
    ),
    refused(
        r#"context.input.path like "/home/u/project" + context.input.suffix"#,
        CEDAR_INVALID,
        INVALID,
    ),
    refused(
        r#"context.input.path like context.input.prefix + "/*""#,
        CEDAR_INVALID,
        INVALID,
    ),
    refused(
        r#"context.input.path like "a" + "b" + "c""#,
        CEDAR_INVALID,
        INVALID,
    ),
    refused(r#"context.input.path like "a" - "b""#, CEDAR_INVALID, INVALID),
    refused(r#"context.input.path like "a" * 2"#, CEDAR_INVALID, INVALID),
    refused(r#"context.input.path like "a" * "b""#, CEDAR_INVALID, INVALID),
    refused(r#"context.input.path like -"a""#, CEDAR_INVALID, INVALID),
    refused(r#"context.input.path like !"a""#, CEDAR_INVALID, INVALID),
    refused(r#"context.input.path like !!"a""#, CEDAR_INVALID, INVALID),
    // ─── Parentheses and compound expressions ───────────────────────────
    refused(
        r#"context.input.path like ("/home/u/secrets/*")"#,
        CEDAR_INVALID,
        INVALID,
    ),
    refused(r#"context.input.path like (("a/*"))"#, CEDAR_INVALID, INVALID),
    refused(r#"context.input.path like ("a" + "b")"#, CEDAR_INVALID, INVALID),
    refused(
        r#"context.input.path like (if context.input.flag then "a/*" else "b/*")"#,
        CEDAR_INVALID,
        INVALID,
    ),
    refused(r#"context.input.path like ["a/*"]"#, CEDAR_INVALID, INVALID),
    refused(r#"context.input.path like ["a/*", "b/*"]"#, CEDAR_INVALID, INVALID),
    refused(r#"context.input.path like { p: "a/*" }"#, CEDAR_INVALID, INVALID),
    // ─── Accesses and calls on a literal ────────────────────────────────
    refused(r#"context.input.path like "a/*".x"#, CEDAR_INVALID, INVALID),
    refused(r#"context.input.path like "a/*"["x"]"#, CEDAR_INVALID, INVALID),
    refused(
        r#"context.input.path like "a/*".contains("a")"#,
        CEDAR_INVALID,
        INVALID,
    ),
    // ─── Names, entity references, slots, and extension calls ───────────
    refused("context.input.path like principal", CEDAR_INVALID, INVALID),
    refused("context.input.path like ?resource", CEDAR_INVALID, INVALID),
    refused(
        r#"context.input.path like Ns::User::"a""#,
        CEDAR_INVALID,
        INVALID,
    ),
    refused(r#"context.input.path like decimal("1.0")"#, CEDAR_INVALID, INVALID),
    // ─── Other operands with no string literal ──────────────────────────
    refused(
        "context.input.path like context.input.prefix",
        CEDAR_INVALID,
        INVALID,
    ),
    refused("context.input.path like true", CEDAR_INVALID, INVALID),
    refused("context.input.path like 1", CEDAR_INVALID, INVALID),
    // ─── Another relational operator after the literal ──────────────────
    refused(
        r#"context.input.path like "a" like "b""#,
        "unexpected token `like`",
        "unexpected token `like`",
    ),
    refused(
        r#"context.input.path like "a" in principal"#,
        "unexpected token `in`",
        "unexpected token `in`",
    ),
    refused(
        r#"context.input.path like "a" == true"#,
        "unexpected token `==`",
        "unexpected token `==`",
    ),
    // ─── A literal with an escape a pattern does not admit ──────────────
    refused(r#"context.input.path like "a\qb""#, BAD_ESCAPE, BAD_ESCAPE),
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
fn every_like_operand_matches_its_row() {
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

/// A `def cedar` body is parsed by the same rule, and a macro argument cannot
/// supply the pattern. Cedar has no macros, so these are not rows of `CASES`.
#[test]
fn macro_bodies_take_only_a_literal_pattern() {
    let with = |defs: &str, condition: &str| format!("{defs}\n{}", policy(condition));

    for (defs, condition) in [
        (
            r#"def cedar under(?p) { ?p like "/home/u/secrets" + "/*" };"#,
            "under(context.input.path)",
        ),
        (
            r#"def cedar under(?p) { ?p like ("/home/u/secrets/*") };"#,
            "under(context.input.path)",
        ),
        (
            "def cedar matches(?s, ?p) { ?s like ?p };",
            r#"matches(context.input.path, "/home/u/secrets/*")"#,
        ),
    ] {
        let src = with(defs, condition);
        match parse_error(lower(&src)) {
            Ok(message) => assert!(message.contains(INVALID), "{src}: error `{message}`"),
            Err(outcome) => panic!("{src}: {outcome}"),
        }
    }

    let src = with(
        r#"def cedar under(?p) { ?p like "/home/u/secrets/*" };"#,
        "under(context.input.path)",
    );
    lower(&src).unwrap_or_else(|e| panic!("{src}: {e}"));
    let rendered = expanded_source(&src);
    assert!(
        rendered.contains(r#"context.input.path like "/home/u/secrets/*""#),
        "{rendered}"
    );
}
