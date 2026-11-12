//! A policy's `when`/`unless` clauses lower to a balanced `&&` tree in clause
//! order, so the clause count adds ⌈log₂ n⌉ depth, not n: a policy with
//! hundreds of thousands of clauses lowers, validates, and authorizes on a
//! 2 MiB thread. Evaluation order and short-circuiting are those of the
//! left-nested chain Cedar itself builds, which the differential test checks
//! against one explicit `when { c0 && c1 && ... }` clause.

use std::time::Instant;

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, ParsedPolicySet, PolicySchema, ServiceSchema,
    Validator, Value,
};

/// Rust's default stack size for spawned threads.
const STACK: usize = 2 << 20;

const SCHEMA: &str = r#"
namespace Ns {
  type Input = { x?: Bool, y?: Long, z?: Bool };
  entity User;
  entity Res;
  action "Read" appliesTo {
    principal: [User], resource: [Res], context: { input: Input } };
}
"#;

const SCOPE: &str = r#"(principal, action == Ns::Action::"Read", resource)"#;

fn on_small_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("must not panic")
}

fn schema() -> PolicySchema {
    PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds")
}

/// `@id("p") permit (...)` followed by `clauses`, each a full `when {..}` /
/// `unless {..}` clause.
fn policy<S: AsRef<str>>(clauses: &[S]) -> String {
    let body: String = clauses
        .iter()
        .map(|c| format!(" {}", c.as_ref()))
        .collect();
    format!("@id(\"p\") permit {SCOPE}{body};")
}

fn lower(src: &str) -> LoweredPolicySet {
    ParsedPolicySet::parse(src, &ServiceSchema::defaults())
        .expect("parses")
        .lower(&schema())
        .expect("lowers")
}

/// A `Read` request whose `context.input` carries `x = true` (and no `y`/`z`).
fn request() -> Event {
    Event::builder("Ns::Action::Read", "request")
        .timestamp(0)
        .principal("Ns::User::\"u\"")
        .resource("Ns::Res::\"r\"")
        .field("input", "x", Value::Bool(true))
        .request_context("input", "x", Value::Bool(true))
        .build()
}

/// The decision and whether any policy reported an evaluation error.
fn authorize(lowered: LoweredPolicySet) -> (Decision, bool) {
    let mut authorizer = Authorizer::new(lowered);
    let response = authorizer.is_authorized(&request()).expect("decides");
    (response.decision(), response.diagnostics().errors().next().is_some())
}

// ── shape ────────────────────────────────────────────────────────────────

/// The `&&` structure of the single policy's condition, read from its Cedar
/// JSON (EST) form, fully parenthesized: leaves are `has x`, `!has z`, `.x`.
/// The EST is the authoritative shape; the printed text depends on the Cedar
/// version's parenthesization (Cedar 4.11 parenthesizes every operand).
fn shape(src: &str) -> String {
    fn render(e: &serde_json::Value) -> String {
        let obj = e.as_object().expect("EST expression is an object");
        if let Some(and) = obj.get("&&") {
            return format!("({} && {})", render(&and["left"]), render(&and["right"]));
        }
        if let Some(not) = obj.get("!") {
            return format!("!{}", render(&not["arg"]));
        }
        if let Some(has) = obj.get("has") {
            return format!("has {}", has["attr"].as_str().expect("attr"));
        }
        if let Some(get) = obj.get(".") {
            return format!(".{}", get["attr"].as_str().expect("attr"));
        }
        panic!("unexpected EST node {e}");
    }
    let lowered = lower(src);
    let policy = lowered.as_cedar().policies().next().expect("one policy");
    let json = policy.to_json().expect("policy to JSON");
    let conditions = json["conditions"].as_array().expect("conditions");
    assert_eq!(conditions.len(), 1, "one lowered `when`: {json}");
    assert_eq!(conditions[0]["kind"], "when");
    render(&conditions[0]["body"])
}

/// The lowered Cedar text of the set's single policy, whitespace-collapsed.
fn cedar_text(src: &str) -> String {
    let text = lower(src).as_cedar().to_string();
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[test]
fn four_clauses_lower_to_a_balanced_tree() {
    let src = policy(&[
        "when { context.input has x }",
        "when { context.input has y }",
        "unless { context.input has z }",
        "when { context.input.x }",
    ]);
    let (shape, text) = on_small_stack(move || (shape(&src), cedar_text(&src)));
    assert_eq!(shape, "((has x && has y) && (!has z && .x))");
    // Cedar 4.11's printer parenthesizes every operand, so the text shows both
    // groups (newer Cedar drops the left group's parentheses).
    assert!(
        text.ends_with(
            "when { (((context.input) has x) && ((context.input) has y)) && \
             ((!((context.input) has z)) && ((context.input).x)) };"
        ),
        "{text}"
    );
}

#[test]
fn three_clauses_carry_the_odd_one_up_a_level() {
    let src = policy(&[
        "when { context.input has x }",
        "when { context.input has y }",
        "when { context.input has z }",
    ]);
    let (shape, text) = on_small_stack(move || (shape(&src), cedar_text(&src)));
    assert_eq!(shape, "((has x && has y) && has z)");
    assert!(
        text.ends_with(
            "when { (((context.input) has x) && ((context.input) has y)) && \
             ((context.input) has z) };"
        ),
        "{text}"
    );
}

#[test]
fn five_clauses_pair_then_carry() {
    let src = policy(&["when { context.input has x }"; 5]);
    let shape = on_small_stack(move || shape(&src));
    assert_eq!(shape, "(((has x && has x) && (has x && has x)) && has x)");
}

#[test]
fn one_and_zero_clauses_are_unchanged() {
    let one_src = policy(&["unless { context.input has z }"]);
    let (one, zero) =
        on_small_stack(move || (shape(&one_src), cedar_text(&policy::<&str>(&[]))));
    assert_eq!(one, "!has z");
    assert!(zero.ends_with("when { true };"), "zero clauses lower to `true`: {zero}");
}

// ── scale ────────────────────────────────────────────────────────────────

/// Parse, lower, validate, and authorize `src` on a 2 MiB thread; returns the
/// decision and the elapsed wall time.
fn end_to_end(src: String) -> (Decision, bool, std::time::Duration) {
    on_small_stack(move || {
        let start = Instant::now();
        let lowered = lower(&src);
        let result = Validator::new().validate(&lowered);
        let errors: Vec<_> = result.validation_errors().map(|e| e.to_string()).collect();
        assert!(errors.is_empty(), "validate: {errors:?}");
        let (decision, errored) = authorize(lowered);
        (decision, errored, start.elapsed())
    })
}

fn many_when(n: usize) -> String {
    policy(&vec!["when { context.input has x }"; n])
}

#[test]
fn five_hundred_when_clauses_authorize_on_a_small_stack() {
    let (decision, errored, elapsed) = end_to_end(many_when(500));
    eprintln!("500 when clauses: {elapsed:?}");
    assert_eq!(decision, Decision::Allow);
    assert!(!errored);
}

#[test]
fn a_hundred_thousand_when_clauses_authorize_on_a_small_stack() {
    let (decision, errored, elapsed) = end_to_end(many_when(100_000));
    eprintln!("100,000 when clauses: {elapsed:?}");
    assert_eq!(decision, Decision::Allow);
    assert!(!errored);
}

#[test]
fn mixed_when_and_unless_clauses_authorize_on_a_small_stack() {
    let clauses: Vec<&str> = (0..10_000)
        .map(|i| {
            if i % 3 == 0 {
                "unless { context.input has z }"
            } else {
                "when { context.input has x }"
            }
        })
        .collect();
    let (decision, errored, elapsed) = end_to_end(policy(&clauses));
    eprintln!("10,000 mixed clauses: {elapsed:?}");
    assert_eq!(decision, Decision::Allow);
    assert!(!errored);

    // The last `unless` fails: one false clause anywhere denies.
    let mut denied = clauses.clone();
    denied.push("unless { context.input has x }");
    let (decision, _, _) = end_to_end(policy(&denied));
    assert_eq!(decision, Decision::Deny);
}

// ── semantics ────────────────────────────────────────────────────────────

/// Each case is a list of clause bodies. `T`/`F` are true/false without error;
/// `E` errors (an access on `context.input.y`, which the request lacks).
const T: &str = "context.input has x";
const F: &str = "context.input has z";
const E: &str = "context.input.y > 0";

#[test]
fn separate_clauses_match_one_explicit_conjunction() {
    let cases: &[&[&str]] = &[
        &[T],
        &[E],
        &[F, E],
        &[T, F, E],
        &[T, T, T, F, E, E],
        &[T, E, F],
        &[T, T, E, T],
        &[T, T, T, T],
        &[T, T, T, T, T, F, E],
        &[E, F, T],
    ];
    for &bodies in cases {
        let separate = policy(
            &bodies
                .iter()
                .map(|b| format!("when {{ {b} }}"))
                .collect::<Vec<_>>(),
        );
        let joined = policy(&[format!("when {{ {} }}", bodies.join(" && "))]);
        let (got, want) = on_small_stack(move || {
            (authorize(lower(&separate)), authorize(lower(&joined)))
        });
        assert_eq!(got, want, "clauses {bodies:?}");
        // Sanity: the error is reached exactly when no false clause precedes it.
        let first_stop = bodies.iter().find(|b| **b != T);
        assert_eq!(got.1, first_stop == Some(&E), "clauses {bodies:?}: {got:?}");
        assert_eq!(
            got.0 == Decision::Allow,
            first_stop.is_none(),
            "clauses {bodies:?}: {got:?}"
        );
    }
}

/// `unless` clauses fold the same way: `unless { b }` is `!b`, and `!` of an
/// error is an error.
#[test]
fn unless_clauses_match_the_explicit_negated_conjunction() {
    let cases: &[&[(bool, &str)]] = &[
        &[(true, F), (false, E)],
        &[(false, T), (true, E)],
        &[(true, F), (true, F), (false, F), (true, E)],
        &[(true, E), (false, T)],
    ];
    for &clauses in cases {
        let separate = policy(
            &clauses
                .iter()
                .map(|(unless, b)| {
                    if *unless {
                        format!("unless {{ {b} }}")
                    } else {
                        format!("when {{ {b} }}")
                    }
                })
                .collect::<Vec<_>>(),
        );
        let joined_body = clauses
            .iter()
            .map(|(unless, b)| if *unless { format!("!({b})") } else { b.to_string() })
            .collect::<Vec<_>>()
            .join(" && ");
        let joined = policy(&[format!("when {{ {joined_body} }}")]);
        let (got, want) = on_small_stack(move || {
            (authorize(lower(&separate)), authorize(lower(&joined)))
        });
        assert_eq!(got, want, "clauses {clauses:?}");
    }
}
