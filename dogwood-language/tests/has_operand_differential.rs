//! The right-hand side of `has`, row by row against Cedar's parser.
//!
//! The grammar admits any `add` after `has`, as Cedar's does, and Cedar then
//! refuses every operand that is not an attribute path (`to_has_rhs`). Dogwood
//! used to read the leftmost name of such an operand and drop the rest, so an
//! unquoted `has tool-approval` (which lexes as `tool - approval`) tested
//! `has tool`, and `has x.y["z"].w` tested `has x.y.w`.
//!
//! Each row of `CASES` is one condition and states, and the test checks:
//!
//! 1. what Cedar does with it: accepts, or refuses with a given error;
//! 2. what Dogwood does with it: lowers to the Cedar condition Cedar gives the
//!    same text, lowers to a stated Cedar condition (the reserved-word
//!    extension, which Cedar refuses), or refuses with a given error;
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
  type In = { tool: String, x?: { y?: { z?: String } } };
  entity User;
  entity Res;
  action "Call" appliesTo {
    principal: [User], resource: [Res],
    context: { input: In }
  };
}"#;

/// Cedar's error for an operand that is not an attribute path.
const CEDAR_INVALID: &str = "invalid RHS of a `has` operation";
/// Cedar's error for a reserved word used as a name.
const CEDAR_RESERVED: &str = "reserved";
/// Dogwood's error for an operand that is not an attribute path.
const INVALID: &str = "invalid right-hand side of `has`";

enum Cedar {
    Accepts,
    /// Refuses, with an error containing this text.
    Refuses(&'static str),
}

enum Dogwood {
    /// Lowers to what Cedar makes of the same text; `rendered` is the
    /// condition `expanded_source` writes.
    AsCedar { rendered: &'static str },
    /// Lowers to the Cedar condition `cedar`, for text Cedar refuses.
    As {
        cedar: &'static str,
        rendered: &'static str,
    },
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

const fn reserved(condition: &'static str, cedar: &'static str, rendered: &'static str) -> Case {
    Case {
        condition,
        cedar: Cedar::Refuses(CEDAR_RESERVED),
        dogwood: Dogwood::As { cedar, rendered },
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
    // ─── Attribute paths: both accept, and lower alike ──────────────────
    accepted("context.input has tool", r#"context.input has "tool""#),
    accepted("context.input has x.y", "context.input has x.y"),
    accepted("context.input has x.y.z", "context.input has x.y.z"),
    accepted("context.input has x . y", "context.input has x.y"),
    accepted(
        "context.input has x // a comment\n .y",
        "context.input has x.y",
    ),
    accepted(
        r#"context.input has "tool-approval""#,
        r#"context.input has "tool-approval""#,
    ),
    accepted(r#"context.input has """#, r#"context.input has """#),
    accepted(
        r#"context.input has "a\u{2d}b""#,
        r#"context.input has "a-b""#,
    ),
    accepted("context.input has permit", r#"context.input has "permit""#),
    accepted(
        "context.input has principal",
        r#"context.input has "principal""#,
    ),
    accepted("context.input has action", r#"context.input has "action""#),
    accepted(
        "context.input has resource",
        r#"context.input has "resource""#,
    ),
    accepted(
        "context.input has context",
        r#"context.input has "context""#,
    ),
    accepted(
        "context.input has principal.x",
        "context.input has principal.x",
    ),
    accepted("context.input has context.x", "context.input has context.x"),
    accepted(
        "context.input has temporal",
        r#"context.input has "temporal""#,
    ),
    accepted(
        "context.input has temporal.x",
        "context.input has temporal.x",
    ),
    accepted(
        "context.input has guardrails",
        r#"context.input has "guardrails""#,
    ),
    accepted(r#"context.input has "a\"b""#, r#"context.input has "a\"b""#),
    accepted(r#"context.input has "\u{0}""#, r#"context.input has "\0""#),
    // An index is an expression, so it may stand on the left of `has`; these
    // are the spellings of a nested name that is not an identifier.
    accepted(
        r#"context["input"] has "tool-approval""#,
        r#"context.input has "tool-approval""#,
    ),
    accepted(
        r#"context["input"]["x"] has "a b""#,
        r#"context.input.x has "a b""#,
    ),
    accepted(
        "context has input && context.input has x",
        r#"((context has "input") && (context.input has "x"))"#,
    ),
    // ─── Reserved words as names: Cedar refuses, Dogwood tests the name ─
    reserved(
        "context.input has if",
        r#"context.input has "if""#,
        r#"context.input has "if""#,
    ),
    reserved(
        "context.input has if.x",
        r#"context.input has "if" && context.input["if"] has x"#,
        "context.input has if.x",
    ),
    reserved(
        "context.input has x.if",
        r#"context.input has x && context.input.x has "if""#,
        "context.input has x.if",
    ),
    reserved(
        "context.input has x.true",
        r#"context.input has x && context.input.x has "true""#,
        "context.input has x.true",
    ),
    reserved(
        "context.input has then",
        r#"context.input has "then""#,
        r#"context.input has "then""#,
    ),
    reserved(
        "context.input has has",
        r#"context.input has "has""#,
        r#"context.input has "has""#,
    ),
    reserved(
        "context.input has in.x",
        r#"context.input has "in" && context.input["in"] has x"#,
        "context.input has in.x",
    ),
    reserved(
        "context.input has like.x",
        r#"context.input has "like" && context.input["like"] has x"#,
        "context.input has like.x",
    ),
    reserved(
        "context.input has __cedar",
        r#"context.input has "__cedar""#,
        r#"context.input has "__cedar""#,
    ),
    reserved(
        "context.input has then.x",
        r#"context.input has "then" && context.input["then"] has x"#,
        "context.input has then.x",
    ),
    reserved(
        "context.input has else.x",
        r#"context.input has "else" && context.input["else"] has x"#,
        "context.input has else.x",
    ),
    reserved(
        "context.input has is.x",
        r#"context.input has "is" && context.input["is"] has x"#,
        "context.input has is.x",
    ),
    reserved(
        "context.input has has.x",
        r#"context.input has "has" && context.input["has"] has x"#,
        "context.input has has.x",
    ),
    reserved(
        "context.input has if.if",
        r#"context.input has "if" && context.input["if"] has "if""#,
        "context.input has if.if",
    ),
    reserved(
        "context.input has if // a comment\n . x",
        r#"context.input has "if" && context.input["if"] has x"#,
        "context.input has if.x",
    ),
    reserved(
        "if context.input has then then true else false",
        r#"if context.input has "then" then true else false"#,
        r#"if context.input has "then" then true else false"#,
    ),
    // ─── Operators: each used to test the leftmost name ─────────────────
    refused(
        "context.input has tool-approval",
        "invalid RHS of a `has` operation: tool - approval",
        "invalid right-hand side of `has`: `tool-approval`",
    ),
    refused("context.input has tool - approval", CEDAR_INVALID, INVALID),
    refused("context.input has x-y.z", CEDAR_INVALID, INVALID),
    refused("context.input has tool+approval", CEDAR_INVALID, INVALID),
    refused("context.input has tool * approval", CEDAR_INVALID, INVALID),
    refused("context.input has tool / approval", CEDAR_INVALID, INVALID),
    refused("context.input has tool % approval", CEDAR_INVALID, INVALID),
    refused("context.input has -tool", CEDAR_INVALID, INVALID),
    refused("context.input has -1", CEDAR_INVALID, INVALID),
    refused("context.input has x.y + 1", CEDAR_INVALID, INVALID),
    refused("context.input has !tool", CEDAR_INVALID, INVALID),
    refused("context.input has !!tool", CEDAR_INVALID, INVALID),
    // ─── Other expressions: each used to test the first name inside ─────
    refused("context.input has (tool)", CEDAR_INVALID, INVALID),
    refused("context.input has (tool || x)", CEDAR_INVALID, INVALID),
    refused("context.input has (tool).x", CEDAR_INVALID, INVALID),
    refused("context.input has [tool, x]", CEDAR_INVALID, INVALID),
    refused("context.input has [tool].x", CEDAR_INVALID, INVALID),
    refused("context.input has {tool: 1}", CEDAR_INVALID, INVALID),
    refused(
        "context.input has temporal { true }",
        "unexpected token `{`",
        INVALID,
    ),
    // ─── Indexes and calls: each used to be dropped from the path ───────
    refused(r#"context.input has x["y"]"#, CEDAR_INVALID, INVALID),
    refused(r#"context.input has x.y["z"]"#, CEDAR_INVALID, INVALID),
    refused(r#"context.input has x.y["z"].w"#, CEDAR_INVALID, INVALID),
    refused(
        r#"context.input has x["security review"]"#,
        CEDAR_INVALID,
        INVALID,
    ),
    refused(r#"context has input["x"]"#, CEDAR_INVALID, INVALID),
    refused(
        r#"context.input has tool.contains("a")"#,
        CEDAR_INVALID,
        INVALID,
    ),
    refused("context.input has tool()", CEDAR_INVALID, INVALID),
    refused(r#"context.input has if["x"]"#, CEDAR_RESERVED, INVALID),
    refused(r#"context.input has if["x"].y"#, CEDAR_RESERVED, INVALID),
    refused("context.input has if.x()", CEDAR_RESERVED, INVALID),
    // ─── A quoted name stands alone ─────────────────────────────────────
    refused(r#"context.input has "x".y"#, CEDAR_INVALID, INVALID),
    refused(r#"context.input has "x"["y"]"#, CEDAR_INVALID, INVALID),
    // ─── Not names at all ───────────────────────────────────────────────
    refused(
        "context.input has Ns::tool",
        "contains a namespace",
        INVALID,
    ),
    refused(r#"context.input has Ns::User::"a""#, CEDAR_INVALID, INVALID),
    refused(
        "context.input has x.y::z",
        "unexpected token `::`",
        "unexpected token `::`",
    ),
    refused("context.input has true", CEDAR_RESERVED, INVALID),
    refused("context.input has true.x", CEDAR_RESERVED, INVALID),
    refused("context.input has false", CEDAR_RESERVED, INVALID),
    refused("context.input has false.x", CEDAR_RESERVED, INVALID),
    refused(
        "context.input has Ns::f(1)",
        "contains a namespace",
        INVALID,
    ),
    refused(
        r#"context.input has "\*""#,
        "is not a valid escape",
        "is not a valid escape",
    ),
    refused("context.input has 1", CEDAR_INVALID, INVALID),
    refused("context.input has ?principal", CEDAR_INVALID, INVALID),
    refused("context.input has ?x", CEDAR_INVALID, INVALID),
    refused("context.input has ?resource.x", CEDAR_INVALID, INVALID),
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

/// The condition of the single policy in Cedar source `src`, as Cedar parses
/// it.
fn cedar_condition(src: &str) -> Expr {
    condition(&parse_policyset(src).expect("Cedar parses"))
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
    let (expected, rendered) = match &case.dogwood {
        Dogwood::Refuses(expected) => {
            match parse_error(lower(&src)) {
                Ok(message) if message.contains(expected) => {}
                Ok(message) => failures.push(format!("error `{message}` lacks `{expected}`")),
                Err(outcome) => failures.push(outcome),
            }
            return failures;
        }
        Dogwood::AsCedar { rendered } => match cedar {
            Ok(_) => (cedar_condition(&src), *rendered),
            Err(_) => {
                failures.push("AsCedar for text Cedar refuses".to_string());
                return failures;
            }
        },
        Dogwood::As { cedar, rendered } => match parse_policyset(&policy(cedar)) {
            Ok(set) => (condition(&set), *rendered),
            Err(e) => {
                failures.push(format!("Cedar refuses the stated condition `{cedar}`: {e}"));
                return failures;
            }
        },
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
fn every_has_operand_matches_its_row() {
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
