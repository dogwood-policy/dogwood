//! A line comment between two tokens must not change what a policy means.
//!
//! The grammar skips `//` comments between the tokens of a rule, as Cedar's
//! lexer does, but the parser used to read some values from a rule's source
//! text, comments included: it counted the `!` and `-` characters of a run
//! (`! // not!` then `! x` was `!!!x`), and split a qualified name on `::`
//! (`Ns // ::Admin` then `::User` was `Ns::Admin::User`).
//!
//! Each seed below is written with a space between every two tokens, and no
//! space inside a string literal. For each space, the test replaces that one
//! space with `COMMENT`, a line comment that holds the characters the parser
//! could misread, and checks that:
//!
//! - for a `CEDAR` seed, Cedar's parser accepts the variant, and Dogwood
//!   lowers it to the same Cedar policy as Cedar's parse of the same text:
//!   the same effect and annotations, and the same condition, which includes
//!   the scope (`Expr::eq_shape`, which ignores source locations);
//! - for a `DOGWOOD` seed, which Cedar cannot parse, the variant renders
//!   through `expanded_source` exactly as the seed does.

use cedar_policy_core::ast::{self, Expr};
use cedar_policy_core::parser::parse_policyset;
use dogwood_language::{
    Arg, Error, LoweredPolicySet, ParsedPolicySet, PolicySchema, ServiceSchema,
};

const SCHEMA: &str = r#"namespace Ns {
  type In = { flag: Bool, n: Long, s: String };
  entity Group;
  entity User in [Group];
  entity Admin in [Group];
  entity Res;
  action "Call" appliesTo {
    principal: [User, Admin], resource: [Res],
    context: { input: In }
  };
}"#;

/// The comment that replaces one space.
const COMMENT: &str = " // ! !! - -- :: Admin:: \" { } ( ) [ ] ; , . == && ||\n";

/// Policies both parsers accept.
const CEDAR: &[&str] = &[
    // `!` and `-` runs.
    r#"permit ( principal , action , resource ) when { ! context . input . flag } ;"#,
    r#"permit ( principal , action , resource ) when { ! ! context . input . flag } ;"#,
    r#"permit ( principal , action , resource ) when { ! ! ! context . input . flag } ;"#,
    r#"permit ( principal , action , resource ) when { ! ! ! ! context . input . flag } ;"#,
    r#"permit ( principal , action , resource ) when { - 5 == - 5 } ;"#,
    r#"permit ( principal , action , resource ) when { - - 5 == 5 } ;"#,
    r#"permit ( principal , action , resource ) when { - - - 5 == - 5 } ;"#,
    r#"permit ( principal , action , resource ) when { - - - - 5 == 5 } ;"#,
    r#"permit ( principal , action , resource ) when { - context . input . n == 1 } ;"#,
    r#"permit ( principal , action , resource ) when { - ( 5 ) == - 5 } ;"#,
    r#"permit ( principal , action , resource ) when { - 9223372036854775808 == context . input . n } ;"#,
    r#"permit ( principal , action , resource ) when { ! ( ! context . input . flag ) } ;"#,
    r#"permit ( principal , action , resource ) when { - - 9223372036854775808 == context . input . n } ;"#,
    r#"permit ( principal , action , resource ) when { - - ( 5 ) == 5 } ;"#,
    r#"permit ( principal , action , resource ) when { - - context . input . n == 1 } ;"#,
    // Entity references and qualified names.
    r#"permit ( principal == Ns :: User :: "alice" , action == Ns :: Action :: "Call" , resource == Ns :: Res :: "r" ) ;"#,
    r#"permit ( principal in Ns :: Group :: "g" , action in [ Ns :: Action :: "Call" ] , resource ) ;"#,
    r#"permit ( principal , action , resource ) when { principal == Ns :: User :: "alice" } ;"#,
    r#"permit ( principal , action , resource ) when { Ns :: User :: "alice" in principal } ;"#,
    r#"permit ( principal , action , resource ) when { principal in [ Ns :: Group :: "a" , Ns :: Group :: "b" ] } ;"#,
    // `is`, in the scope and in a condition.
    r#"permit ( principal is Ns :: User , action , resource is Ns :: Res ) ;"#,
    r#"permit ( principal is Ns :: User in Ns :: Group :: "g" , action , resource ) ;"#,
    r#"permit ( principal , action , resource ) when { principal is Ns :: User } ;"#,
    r#"permit ( principal , action , resource ) when { principal is Ns :: User in Ns :: Group :: "g" } ;"#,
    r#"permit ( principal , action , resource ) when { principal is principal } ;"#,
    // Function and method calls.
    r#"permit ( principal , action , resource ) when { decimal ( "1.5" ) . lessThan ( decimal ( "2.0" ) ) } ;"#,
    r#"permit ( principal , action , resource ) when { ip ( "10.0.0.1" ) . isLoopback ( ) } ;"#,
    r#"permit ( principal , action , resource ) when { [ 1 , 2 ] . contains ( 1 ) } ;"#,
    // Other expression forms.
    r#"permit ( principal , action , resource ) when { { a : 1 , "b" : 2 } . a == 1 } ;"#,
    r#"permit ( principal , action , resource ) when { { "b c" : 1 , principal : 2 } . principal == 2 } ;"#,
    r#"permit ( principal , action , resource ) when { context . input [ "s" ] == "x" } ;"#,
    r#"permit ( principal , action , resource ) when { context . input has flag && context . input . s like "a*" } ;"#,
    r#"permit ( principal , action , resource ) when { if context . input . flag then 1 else 2 == 1 } ;"#,
    r#"permit ( principal , action , resource ) when { context . input . n + 1 * 2 < 3 || false } ;"#,
    r#"@id ( "r" ) forbid ( principal , action , resource ) unless { true } ;"#,
    r#"@ id ( "r" ) @ note ( "a b" ) @ flag permit ( principal , action , resource ) ;"#,
];

/// Policies only Dogwood accepts: temporal conditions and macros.
const DOGWOOD: &[&str] = &[
    r#"def cedar not2 ( ?x ) { ! ! ?x } ; permit ( principal , action , resource ) when { not2 ( context . input . flag ) } ;"#,
    r#"def cedar alice ( ) { principal == Ns :: User :: "alice" } ; permit ( principal , action , resource ) when { alice ( ) } ;"#,
    r#"forbid ( principal , action , resource ) when temporal { ! formerly within 1h A :: Action :: "Fetch" :: request { input . url : "x" } } ;"#,
];

/// Each variant of `seed` with one space replaced by `COMMENT`. Spaces inside
/// a string literal are kept.
fn variants(seed: &str) -> Vec<String> {
    let mut gaps = Vec::new();
    let mut in_string = false;
    let mut escaped = false;
    for (i, c) in seed.char_indices() {
        match c {
            _ if escaped => escaped = false,
            '\\' if in_string => escaped = true,
            '"' => in_string = !in_string,
            ' ' if !in_string => gaps.push(i),
            _ => {}
        }
    }
    gaps.into_iter()
        .map(|i| format!("{}{COMMENT}{}", &seed[..i], &seed[i + 1..]))
        .collect()
}

fn lower(src: &str) -> Result<LoweredPolicySet, Error> {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema parses");
    LoweredPolicySet::from_str(src, &ServiceSchema::defaults(), &schema)
}

fn expanded_source(src: &str) -> Result<String, Error> {
    let parsed = ParsedPolicySet::parse(src, &ServiceSchema::defaults())?;
    Ok(parsed
        .policies()
        .map(|p| p.expanded_source())
        .collect::<Vec<_>>()
        .join("\n"))
}

/// The single policy in `set`, as its effect, annotations, and condition.
fn policy(set: &ast::PolicySet) -> (ast::Effect, Vec<(String, String)>, Expr) {
    let mut policies = set.policies();
    let policy = policies.next().expect("one policy");
    assert!(policies.next().is_none(), "one policy");
    let annotations = policy
        .annotations()
        .map(|(key, value)| (key.to_string(), value.as_ref().to_string()))
        .collect();
    (policy.effect(), annotations, policy.condition())
}

/// Checks one `CEDAR` source, returning a description of each way it does
/// not hold.
fn check_cedar(src: &str) -> Option<String> {
    let (cedar_effect, cedar_annotations, cedar) = match parse_policyset(src) {
        Ok(set) => policy(&set),
        Err(e) => return Some(format!("Cedar refuses it: {e}")),
    };
    let (effect, annotations, lowered) = match lower(src) {
        Ok(lowered) => policy(lowered.as_cedar().as_ref()),
        Err(e) => return Some(format!("Dogwood refuses it: {e}")),
    };
    if effect != cedar_effect || annotations != cedar_annotations {
        return Some(format!(
            "Cedar: {cedar_effect:?} {cedar_annotations:?}\n  Dogwood: {effect:?} {annotations:?}"
        ));
    }
    (!lowered.eq_shape(&cedar)).then(|| format!("Cedar: {cedar}\n  Dogwood: {lowered}"))
}

#[test]
fn a_comment_between_tokens_does_not_change_a_cedar_policy() {
    let mut failures = Vec::new();
    for seed in CEDAR {
        if let Some(f) = check_cedar(seed) {
            failures.push(format!("seed {seed:?}: {f}"));
            continue;
        }
        for variant in variants(seed) {
            if let Some(f) = check_cedar(&variant) {
                failures.push(format!("{variant:?}:\n  {f}"));
            }
        }
    }
    assert!(failures.is_empty(), "\n{}", failures.join("\n"));
}

#[test]
fn a_comment_between_tokens_does_not_change_a_dogwood_policy() {
    let mut failures = Vec::new();
    for seed in DOGWOOD {
        let expected = match expanded_source(seed) {
            Ok(rendered) => rendered,
            Err(e) => {
                failures.push(format!("seed {seed:?} does not parse: {e}"));
                continue;
            }
        };
        for variant in variants(seed) {
            match expanded_source(&variant) {
                Ok(rendered) if rendered == expected => {}
                Ok(rendered) => {
                    failures.push(format!("{variant:?}:\n  {rendered}\n  not {expected}"))
                }
                Err(e) => failures.push(format!("{variant:?}: does not parse: {e}")),
            }
        }
    }
    assert!(failures.is_empty(), "\n{}", failures.join("\n"));
}

/// A provider call is named by its tokens, however it is spaced, so the
/// spaced `Ns :: Fn` and every comment variant of it call `Ns::Fn`, and render
/// as `Ns::Fn(1)`. (A `DOGWOOD` seed only compares variants with the seed's
/// own rendering.)
#[test]
fn a_provider_call_is_named_by_its_tokens() {
    let seed = "permit ( principal , action , resource ) when { Ns :: Fn ( 1 ) == 1 } ;";
    let rendered = "permit (principal, action, resource)\nwhen { (Ns::Fn(1) == 1) };";
    let mut failures = Vec::new();
    for src in std::iter::once(seed.to_string()).chain(variants(seed)) {
        match ParsedPolicySet::parse(&src, &ServiceSchema::defaults()) {
            Ok(parsed) => {
                let calls: Vec<String> = parsed
                    .policies()
                    .flat_map(|p| p.provider_invocations().collect::<Vec<_>>())
                    .collect();
                if calls != ["Ns::Fn"] {
                    failures.push(format!("{src:?}: calls {calls:?}"));
                }
            }
            Err(e) => failures.push(format!("{src:?}: does not parse: {e}")),
        }
        if expanded_source(&src).ok().as_deref() != Some(rendered) {
            failures.push(format!("{src:?}: renders {:?}", expanded_source(&src)));
        }
    }
    assert!(failures.is_empty(), "\n{}", failures.join("\n"));
}

/// A negative integer provider argument is a single `-` before the number,
/// which the parser folds into the literal. Any other negation is refused, as
/// Cedar refuses `--5` in a restricted expression; base read `--5` as `5`.
/// `None` is a refused argument.
#[test]
fn a_negated_integer_provider_argument_is_a_single_dash() {
    const ROWS: &[(&str, Option<i64>)] = &[
        ("5", Some(5)),
        ("-5", Some(-5)),
        ("-9223372036854775808", Some(i64::MIN)),
        ("--5", None),
        ("- - 5", None),
        ("- // c\n- 5", None),
        ("---1", None),
        ("----5", None),
        ("-(5)", None),
    ];
    let args = |arg: &str| {
        let src =
            format!("permit ( principal , action , resource ) when {{ Ns::Fn({arg}) == 1 }} ;");
        let parsed = ParsedPolicySet::parse(&src, &ServiceSchema::defaults())
            .unwrap_or_else(|e| panic!("{arg:?} does not parse: {e}"));
        let policy = parsed.policies().next().expect("one policy");
        policy
            .provider_invocations_with_args()
            .map(|invocations| {
                let [invocation] = invocations.as_slice() else {
                    panic!("{arg:?}: not one invocation: {invocations:?}");
                };
                invocation.args.clone()
            })
            .map_err(|e| e.to_string())
    };
    let mut failures = Vec::new();
    for &(arg, value) in ROWS {
        match (args(arg), value) {
            (Ok(got), Some(n)) if got == [Arg::Integer(n)] => {}
            (Err(e), None) if e.contains("not allowed to use `-` except directly before a number") => {}
            (got, _) => failures.push(format!("{arg:?}: {got:?}, expected {value:?}")),
        }
    }
    assert!(failures.is_empty(), "\n{}", failures.join("\n"));
}
