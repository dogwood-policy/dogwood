//! Pathologically nested or chained policy text is an ordinary parse error,
//! never a stack overflow, and text at the limit parses, expands, lowers, and
//! validates on a 2 MiB thread in any build profile.
//!
//! One limit, by default `dogwood_language::DEFAULT_MAX_DEPTH` (32), bounds
//! the depth of every finished tree the frontend returns (temporal blocks and
//! macro expansion included), measured at the root with an explicit-stack
//! walker, and the nesting that the generated parsers see: open brackets,
//! plus `if` in a policy and the operand-introducing keywords in a temporal
//! block, each counted until the bracket enclosing it closes. The builders do
//! not count — chains build deep trees through loops and are freed without
//! recursion — so a bracket level costs the generated parser and builder
//! about nine stack frames; these tests are what show that 32 levels of each
//! fit 2 MiB. The last section sets the limit through `ParseOptions`.

use dogwood_language::{
    DEFAULT_MAX_DEPTH, Error, LoweredPolicySet, ParseOptions, ParsedPolicySet, PolicySchema,
    ServiceSchema, Validator,
};

/// Rust's default stack size for spawned threads.
const STACK: usize = 2 << 20;

const NESTING: &str = "nesting exceeds the maximum depth of 32";
const EXPR: &str = "expression nested deeper than the limit of 32";
const EXPANSION: &str = "macro expansion nested deeper than the limit of 32";
const TEMPORAL: &str = "temporal expression nested deeper than the limit of 32";

/// `L0` is `{ x: Bool }` and each `Ln` is `{ x: L(n-1) }`, so
/// `context.input` followed by `.x` 30 times is a `Bool` at depth 32.
fn action_schema() -> String {
    let records: String = (1..=DEFAULT_MAX_DEPTH - 3)
        .map(|n| format!("  type L{n} = {{ x: L{} }};\n", n - 1))
        .collect();
    format!(
        "namespace Ns {{\n  type L0 = {{ x: Bool }};\n{records}  entity User;\n  entity Res;\n  \
         action \"Read\" appliesTo {{\n    principal: [User],\n    resource: [Res],\n    \
         context: {{ input: L{} }}\n  }};\n}}\n",
        DEFAULT_MAX_DEPTH - 3
    )
}

const SCOPE: &str = r#"(principal, action == Ns::Action::"Read", resource)"#;
const READ: &str = r#"Ns::Action::"Read"::request{}"#;

fn policy(body: &str) -> String {
    format!("@id(\"p\") permit {SCOPE} when {{ {body} }};")
}

fn temporal_policy(body: &str) -> String {
    format!("@id(\"p\") permit {SCOPE} when temporal {{ {body} }};")
}

/// The nesting scan's error for a temporal block's `body`, if any.
fn temporal_scan(body: &str) -> Option<pest::error::Error<dogwood_syntax::Rule>> {
    dogwood_syntax::nesting_depth_error(
        body,
        dogwood_language::TEMPORAL_NESTING_KEYWORDS,
        DEFAULT_MAX_DEPTH,
    )
}

fn on_small_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("must not panic")
}

fn describe(error: Error) -> String {
    match error {
        Error::Parse(_) => format!("parse: {error}"),
        Error::Macro(_) => format!("macro: {error}"),
        other => format!("other: {other}"),
    }
}

/// Parse and macro-expand `src` on a thread with a 2 MiB stack.
fn parse_on_small_stack(src: String) -> Result<(), String> {
    on_small_stack(move || {
        ParsedPolicySet::parse(&src, &ServiceSchema::defaults())
            .map(drop)
            .map_err(describe)
    })
}

/// Parse, macro-expand, lower, and validate `src` on a thread with a 2 MiB
/// stack, and require every step to succeed.
#[track_caller]
fn assert_accepted(src: String) {
    let outcome = on_small_stack(move || {
        let policy_schema = PolicySchema::from_cedarschema_str(&action_schema())
            .map_err(|e| format!("schema: {e}"))?;
        let parsed = ParsedPolicySet::parse(&src, &ServiceSchema::defaults()).map_err(describe)?;
        let lowered = parsed.lower(&policy_schema).map_err(describe)?;
        let result = Validator::new().validate(&lowered);
        if !result.validation_passed() {
            let errors: Vec<_> = result.validation_errors().map(|e| e.to_string()).collect();
            return Err(format!("validate: {errors:?}"));
        }
        Ok(())
    });
    if let Err(error) = outcome {
        panic!("expected the policy to be accepted, got {error}");
    }
}

#[track_caller]
fn assert_rejected(src: String, phase: &str, message: &str) {
    let error = parse_on_small_stack(src).expect_err("must be rejected");
    assert!(
        error.starts_with(phase) && error.contains(message),
        "expected a {phase} error mentioning {message:?}, got: {error}"
    );
}

// ── Bracket and `if` nesting ────────────────────────────────────────────

#[test]
fn nested_parens_are_a_parse_error() {
    let n = 10_000;
    let body = format!("{}context.input.x == 1{}", "(".repeat(n), ")".repeat(n));
    assert_rejected(policy(&body), "parse", NESTING);
}

#[test]
fn nested_set_literals_are_a_parse_error() {
    let n = 2_000;
    let body = format!("{}1{} == [1]", "[".repeat(n), "]".repeat(n));
    assert_rejected(policy(&body), "parse", NESTING);
}

#[test]
fn nested_record_literals_are_a_parse_error() {
    let n = 2_000;
    let body = format!("{}1{} == {{}}", "{a: ".repeat(n), "}".repeat(n));
    assert_rejected(policy(&body), "parse", NESTING);
}

#[test]
fn nested_if_then_else_is_a_parse_error() {
    let n = 5_000;
    let nested_condition = format!(
        "{}true{}",
        "if ".repeat(n),
        " then true else true".repeat(n)
    );
    assert_rejected(policy(&nested_condition), "parse", NESTING);
    let else_if_chain = format!("{}true", "if true then true else ".repeat(n));
    assert_rejected(policy(&else_if_chain), "parse", NESTING);
}

#[test]
fn nested_macro_call_arguments_are_a_parse_error() {
    let n = 2_000;
    let src = format!(
        "def cedar m(?x) {{ ?x }};\n{}",
        policy(&format!("{}true{}", "m(".repeat(n), ")".repeat(n)))
    );
    assert_rejected(src, "parse", NESTING);
}

#[test]
fn nested_temporal_operators_are_a_parse_error() {
    let n = 2_000;
    let body = format!(
        "{}{READ}{}",
        "formerly within 1h (".repeat(n),
        ")".repeat(n)
    );
    assert_rejected(temporal_policy(&body), "parse", NESTING);
}

#[test]
fn deep_event_schema_records_are_an_error() {
    let n = 5_000;
    let schema = format!(
        "decision event <A>::request {{ ...inputs(A), f: {}String{} }}",
        "{ g: ".repeat(n),
        " }".repeat(n)
    );
    let error = on_small_stack(move || {
        ServiceSchema::builder()
            .event_schema_str(&schema)
            .build()
            .map(drop)
    })
    .expect_err("must be rejected");
    assert!(error.to_string().contains(NESTING), "{error}");
}

// ── Flat chains that build deep trees ───────────────────────────────────
//
// The builders fold chains with loops, so each of these builds a tree about
// 200,000 levels deep, which the measured root check then refuses. Building,
// measuring, rejecting, and freeing that tree must all fit the 2 MiB stack:
// the surface trees drop with an explicit worklist (`deep_drop`), not
// recursion, so these tests are also the regression tests for the
// non-recursive drop. A derived drop would abort them.

const CHAIN: usize = 200_000;

#[test]
fn a_bang_run_is_a_parse_error() {
    assert_rejected(policy(&format!("{}true", "!".repeat(CHAIN))), "parse", EXPR);
}

#[test]
fn a_dash_run_is_a_parse_error() {
    let body = format!("{}1 == 1", "-".repeat(CHAIN));
    assert_rejected(policy(&body), "parse", EXPR);
}

#[test]
fn an_and_chain_is_a_parse_error() {
    assert_rejected(policy(&vec!["true"; CHAIN].join(" && ")), "parse", EXPR);
}

#[test]
fn an_or_chain_is_a_parse_error() {
    assert_rejected(policy(&vec!["true"; CHAIN].join(" || ")), "parse", EXPR);
}

#[test]
fn an_add_chain_is_a_parse_error() {
    let body = format!("{} == 1", vec!["1"; CHAIN].join(" + "));
    assert_rejected(policy(&body), "parse", EXPR);
}

#[test]
fn a_member_access_chain_is_a_parse_error() {
    let body = format!("context{} == 1", ".x".repeat(CHAIN));
    assert_rejected(policy(&body), "parse", EXPR);
}

#[test]
fn a_deep_def_cedar_body_is_a_parse_error() {
    let src = format!(
        "def cedar m() {{ {} }};\n{}",
        vec!["true"; CHAIN].join(" && "),
        policy("m()")
    );
    assert_rejected(src, "parse", EXPR);
}

#[test]
fn temporal_chains_are_a_parse_error() {
    for body in [
        vec![READ; CHAIN].join(" && "),
        format!("{}{READ}", "!".repeat(CHAIN)),
        format!("{} > 1", vec!["1"; CHAIN].join(" + ")),
        format!("{} > 1", vec!["1"; CHAIN].join(" * ")),
    ] {
        assert_rejected(temporal_policy(&body), "parse", TEMPORAL);
    }
    let src = format!(
        "def temporal m() {{ {} }};\n{}",
        vec![READ; CHAIN].join(" && "),
        temporal_policy("m()")
    );
    assert_rejected(src, "parse", TEMPORAL);
}

#[test]
fn temporal_binder_runs_are_a_parse_error() {
    // The generated parser nests once per binder with no bracket open.
    let n = 20_000;
    for body in [
        format!("{}{READ}", "exists (t: Long). ".repeat(n)),
        format!(
            "{}{READ}{}",
            "count for (t: Long). where ".repeat(n),
            " >= 1".repeat(n)
        ),
        format!(
            "{}{READ}{}",
            "sum ?v for (t: Long). where ".repeat(n),
            " >= 1".repeat(n)
        ),
    ] {
        assert_rejected(temporal_policy(&body), "parse", NESTING);
    }
    let src = format!(
        "def temporal m() {{ {}{READ} }};\n{}",
        "exists (t: Long). ".repeat(n),
        temporal_policy("m()")
    );
    assert_rejected(src, "parse", NESTING);
}

#[test]
fn a_binder_dot_releases_no_keyword() {
    // A binder list ends at `.`, so the keyword right after it, with no
    // space, still opens a level. A scan that skipped a keyword after `.`
    // saw none of these and let the generated parser overflow the stack.
    let n = 20_000;
    for body in [
        format!("{}{READ}", "exists (t: Long).".repeat(n)),
        format!(
            "{}{READ}{}",
            "count for (t: Long).where ".repeat(n),
            " >= 1".repeat(n)
        ),
    ] {
        assert_rejected(temporal_policy(&body), "parse", NESTING);
    }
}

#[test]
fn a_binder_dot_run_the_scan_admits_still_parses() {
    // In the block's body, each `exists` and the predicate's braces are one
    // level each, so the scan admits 31 binders and refuses 32.
    let run = |n| format!("{}{READ}", "exists (t: Long).".repeat(n));
    assert!(temporal_scan(&run(DEFAULT_MAX_DEPTH - 1)).is_none());
    assert!(temporal_scan(&run(DEFAULT_MAX_DEPTH)).is_some());
    // Range-restricted binders with no space after the dot parse, expand,
    // lower, and validate up to the same limit as the spaced spelling.
    let binders = |n: usize| {
        let names: Vec<_> = (0..n).map(|i| format!("t{i}")).collect();
        let open: String = names
            .iter()
            .map(|t| format!("exists ({t}: Timepoint)."))
            .collect();
        let uses: Vec<_> = names.iter().map(|t| format!("tp({t})")).collect();
        format!("{open}({})", uses.join(" && "))
    };
    assert_accepted(temporal_policy(&binders((DEFAULT_MAX_DEPTH - 1) / 2)));
    assert_rejected(
        temporal_policy(&binders((DEFAULT_MAX_DEPTH - 1) / 2 + 1)),
        "parse",
        // The block alone is within the limit; the marker's level tips the
        // whole tree over, so the root measure reports the expression limit.
        EXPR,
    );
}

// ── Keyword word boundaries ─────────────────────────────────────────────
//
// The nesting scan counts a temporal keyword only as a whole word, so the
// grammar must too: a keyword glued to the next word or number is not a
// keyword, and `countfor(t:Long).where` is a syntax error rather than a
// parse that nests the generated parser once per run the scan cannot see.

/// The error a run of `countfor(t:Long).where` produces: `countfor` is an
/// identifier, so `countfor(` opens a macro call whose `t` argument is not
/// followed by `,` or `)`.
/// A `sum` body that range-restricts its bound variable `?v`.
const SUMMED: &str = r#"Ns::Action::"Read"::request{ x: ?v }"#;

const RUN_TOGETHER: &str = "unexpected token `:`, expected arithmetic operator, comparison operator";

#[test]
fn run_together_count_for_where_is_a_parse_error() {
    // Before keywords had a word boundary, each shape below overflowed a
    // 2 MiB stack at its smallest `n` (the bare run at 1000, the
    // comparison-wrapped run at 100).
    for n in [100, 1_000] {
        for body in [
            "countfor(t:Long).where".repeat(n),
            format!("{}tp(t)", "0 < countfor(t:Long).where".repeat(n)),
        ] {
            assert!(temporal_scan(&body).is_none(), "the scan sees no keyword");
            assert_rejected(temporal_policy(&body), "parse", RUN_TOGETHER);
        }
    }
}

#[test]
fn a_keyword_glued_to_a_keyword_or_number_is_a_parse_error() {
    for (body, message) in [
        // `formerlywithin1h` is one identifier, so `(` opens a call that
        // never closes (few enough that the bracket scan admits them).
        (
            "formerlywithin1h(".repeat(3),
            "unexpected end of input, expected argument",
        ),
        (
            format!("formerly within1h({READ})"),
            "unexpected token `within1h`",
        ),
        (
            format!("formerlywithin 1h {READ}"),
            "unexpected token `1`, expected arithmetic operator, comparison operator",
        ),
        (
            format!("previouswithin 1h {READ}"),
            "unexpected token `1`, expected arithmetic operator, comparison operator",
        ),
        (
            format!("{READ} sincewithin 1h {READ}"),
            "unexpected token `sincewithin`",
        ),
        (
            format!("existsfor(t: Long). {READ}"),
            "unexpected token `:`, expected arithmetic operator, comparison operator",
        ),
        (
            "0 < count for (t: Long).wheretp(t)".to_string(),
            "unexpected token `wheretp`",
        ),
    ] {
        assert_rejected(temporal_policy(&body), "parse", message);
    }
}

#[test]
fn spaced_keywords_still_parse() {
    for body in [
        "0 < count for (t: Long). where tp(t)".to_string(),
        format!("formerly within 1h {READ}"),
        format!("previous within 1h {READ}"),
        format!("{READ} since within 1h {READ}"),
        "exists (t: Long). tp(t)".to_string(),
        r#"0 < sum v for (v: Long). where Ns::Action::"Read"::request{ x: v }"#.to_string(),
        // A keyword followed by punctuation needs no space.
        "0 < count for(t: Long).where(tp(t))".to_string(),
        format!("formerly within 1h({READ})"),
    ] {
        let src = temporal_policy(&body);
        if let Err(error) = parse_on_small_stack(src) {
            panic!("expected {body:?} to parse, got {error}");
        }
    }
    let src = format!(
        "def temporal total(?v) {{ sum ?v for (?v: Long). where {SUMMED} }};\n{}",
        temporal_policy("0 < total(v)")
    );
    if let Err(error) = parse_on_small_stack(src) {
        panic!("expected the `sum` macro to parse, got {error}");
    }
}

#[test]
fn a_keyword_prefix_is_an_ordinary_identifier() {
    // A field name in a predicate's or field block's `{ ... }`.
    let fields =
        r#"Ns::Action::"Read"::request{ counter: 1, former: 2, within_x: 3 }{ sums: 4 }"#;
    // A binder and its use, and a binder used as a `sum` bound variable.
    let binders = format!(
        "exists (counter: Long). exists (formerly_seen: Timepoint). \
         tp(formerly_seen) && (count for (forward: Timepoint). where tp(forward)) == counter && \
         0 < sum sums for (sums: Long). where {READ}{{ x: sums }}"
    );
    // A macro call name and an event kind.
    let src = format!(
        "def temporal forward(?c) {{ ?c }};\n\
         def temporal existsAny(?c) {{ ?c }};\n\
         def temporal counted() {{ count for ($t: Timepoint). where tp($t) }};\n{}",
        temporal_policy(&format!(
            r#"forward({READ}) && existsAny({READ}) && counted() > 0 && Ns::Action::"Read"::sincere{{}}"#
        ))
    );
    for src in [temporal_policy(fields), temporal_policy(&binders), src] {
        if let Err(error) = parse_on_small_stack(src.clone()) {
            panic!("expected {src:?} to parse, got {error}");
        }
    }
}

#[test]
fn a_def_cedar_body_error_points_into_the_body() {
    let body = format!("{}true", "!".repeat(DEFAULT_MAX_DEPTH));
    let src = format!("{}\ndef cedar m() {{ {body} }};", policy("true"));
    let errors = match ParsedPolicySet::parse(&src, &ServiceSchema::defaults()) {
        Err(Error::Parse(errors)) => errors,
        other => panic!("expected parse errors, got {other:?}"),
    };
    let span = errors.iter().next().expect("one error").location().span();
    assert_eq!(span.offset(), src.find('!').expect("the body"));
}

#[test]
fn every_deep_policy_is_reported() {
    let deep = policy(&format!("{}true", "!".repeat(DEFAULT_MAX_DEPTH)));
    let src = format!("{deep}\n{}\n{deep}", policy("true"));
    let errors = match ParsedPolicySet::parse(&src, &ServiceSchema::defaults()) {
        Err(Error::Parse(errors)) => errors,
        other => panic!("expected parse errors, got {other:?}"),
    };
    let offsets: Vec<_> = errors
        .iter()
        .map(|e| e.location().span().offset())
        .collect();
    assert_eq!(offsets.len(), 2, "{errors:?}");
    assert!(offsets[0] < deep.len(), "{offsets:?}");
    assert!(offsets[1] > src.len() - deep.len(), "{offsets:?}");
}

#[test]
fn expansion_deeper_than_the_limit_is_an_error() {
    // Each body and each call site is within the limit; the expansion of the
    // nested calls is not.
    let body = format!("?x{}", " && true".repeat(DEFAULT_MAX_DEPTH - 2));
    let call = format!("{}true{}", "m(".repeat(4), ")".repeat(4));
    let src = format!("def cedar m(?x) {{ {body} }};\n{}", policy(&call));
    assert_rejected(src, "macro", EXPANSION);

    // Each expansion adds ten binders.
    let binders: String = (0..10).map(|i| format!("exists ($b{i}: Long). ")).collect();
    let src = format!(
        "def temporal m(?c) {{ {binders}?c }};\n{}",
        temporal_policy(&format!("{}{READ}{}", "m(".repeat(4), ")".repeat(4)))
    );
    assert_rejected(src, "macro", EXPANSION);
}

// ── At the limit ────────────────────────────────────────────────────────

#[test]
fn nesting_at_the_limit_is_accepted_on_a_small_stack() {
    // The condition braces are the first level.
    let n = DEFAULT_MAX_DEPTH - 1;
    assert_accepted(policy(&format!(
        "{}context.input.x.x == context.input.x.x{}",
        "(".repeat(n),
        ")".repeat(n)
    )));
    assert_accepted(policy(&format!(
        "{}true{}",
        "if ".repeat(n),
        " then true else true".repeat(n)
    )));
    let body = format!(
        "{}context.input.x.x == context.input.x.x{}",
        "(".repeat(n + 1),
        ")".repeat(n + 1)
    );
    assert_rejected(policy(&body), "parse", NESTING);
    let body = format!(
        "{}true{}",
        "if ".repeat(n + 1),
        " then true else true".repeat(n + 1)
    );
    assert_rejected(policy(&body), "parse", NESTING);
}

#[test]
fn set_and_record_literals_at_the_limit_are_accepted_on_a_small_stack() {
    // Each literal is a level of both nesting and the tree, under the `==`.
    let n = DEFAULT_MAX_DEPTH - 2;
    let set = |n| format!("{}true{}", "[".repeat(n), "]".repeat(n));
    let record = |n| format!("{}true{}", "{a: ".repeat(n), "}".repeat(n));
    assert_accepted(policy(&format!("{} == {}", set(n), set(n))));
    assert_accepted(policy(&format!("{} == {}", record(n), record(n))));
    assert_rejected(
        policy(&format!("{} == {}", set(n + 1), set(n + 1))),
        "parse",
        EXPR,
    );
    assert_rejected(
        policy(&format!("{} == {}", record(n + 1), record(n + 1))),
        "parse",
        EXPR,
    );
}

#[test]
fn a_chain_at_the_limit_is_accepted_on_a_small_stack() {
    let terms = |n| vec!["true"; n].join(" && ");
    assert_accepted(policy(&terms(DEFAULT_MAX_DEPTH)));
    assert_rejected(policy(&terms(DEFAULT_MAX_DEPTH + 1)), "parse", EXPR);

    let bangs = |n| format!("{}true", "!".repeat(n));
    assert_accepted(policy(&bangs(DEFAULT_MAX_DEPTH - 1)));
    assert_rejected(policy(&bangs(DEFAULT_MAX_DEPTH)), "parse", EXPR);

    // `context` and `.input` are two levels; the schema nests `x` deep enough.
    let members = |n| format!("context.input{}", ".x".repeat(n));
    assert_accepted(policy(&members(DEFAULT_MAX_DEPTH - 2)));
    assert_rejected(policy(&members(DEFAULT_MAX_DEPTH - 1)), "parse", EXPR);
}

#[test]
fn macro_expansion_at_the_limit_is_accepted_on_a_small_stack() {
    // `?x` sits at depth 16 of the body, and the argument is 17 deep.
    let body = format!("?x{}", " && true".repeat(15));
    let call = |n| format!("m({})", vec!["true"; n].join(" && "));
    let src = |n| format!("def cedar m(?x) {{ {body} }};\n{}", policy(&call(n)));
    assert_accepted(src(17));
    assert_rejected(src(18), "macro", EXPANSION);
}

#[test]
fn a_temporal_block_at_the_limit_is_accepted_on_a_small_stack() {
    // The marker is the first level and the `&&` chain's root the second, so
    // the first of 30 conjuncts is at depth 31 and its predicate at 32.
    let wide = |n| vec![format!("formerly within 1h {READ}"); n].join(" && ");
    assert_accepted(temporal_policy(&wide(DEFAULT_MAX_DEPTH - 2)));
    assert_rejected(
        temporal_policy(&wide(DEFAULT_MAX_DEPTH - 1)),
        "parse",
        // Within the block the chain fits; with the marker's level the whole
        // tree is one too deep, reported by the root measure.
        EXPR,
    );
    // Sibling `formerly`s accumulate in the scan: 32 of them, then the last
    // predicate's braces, are past its limit before the builder runs.
    assert_rejected(temporal_policy(&wide(DEFAULT_MAX_DEPTH)), "parse", NESTING);

    // The marker, each `!`, the `formerly`, and the predicate are one level
    // each, and every `!` opens a bracket.
    let deep = |n| {
        format!(
            "{}formerly within 1h {READ}{}",
            "!(".repeat(n),
            ")".repeat(n)
        )
    };
    assert_accepted(temporal_policy(&deep(DEFAULT_MAX_DEPTH - 3)));
    assert_rejected(
        temporal_policy(&deep(DEFAULT_MAX_DEPTH - 2)),
        "parse",
        // One too deep only with the marker's level, so the root measure
        // reports the expression limit.
        EXPR,
    );

    // Binders range-restricted by `tp`: the marker, each binder, each `&&`,
    // and the last `tp` are one level each.
    let binders = |n: usize| {
        let names: Vec<_> = (0..n).map(|i| format!("t{i}")).collect();
        let open: String = names
            .iter()
            .map(|t| format!("exists ({t}: Timepoint). "))
            .collect();
        let uses: Vec<_> = names.iter().map(|t| format!("tp({t})")).collect();
        format!("{open}({})", uses.join(" && "))
    };
    assert_accepted(temporal_policy(&binders((DEFAULT_MAX_DEPTH - 1) / 2)));
    assert_rejected(
        temporal_policy(&binders((DEFAULT_MAX_DEPTH - 1) / 2 + 1)),
        "parse",
        // As above: the marker's level tips the combined count.
        EXPR,
    );

    // A comparison is one level and each of its terms another; an
    // aggregate is two, the term and its expression. One `!` more is also
    // past the scan's limit: the `!(`s, the aggregate's parenthesis, its
    // `count`, `for`, and `where`, and `tp(` are 33 levels, so the scan
    // refuses it first.
    let compared = |n| {
        format!(
            "{}(count for (t: Timepoint). where tp(t)) >= 1{}",
            "!(".repeat(n),
            ")".repeat(n)
        )
    };
    assert_accepted(temporal_policy(&compared(DEFAULT_MAX_DEPTH - 5)));
    assert_rejected(
        temporal_policy(&compared(DEFAULT_MAX_DEPTH - 4)),
        "parse",
        NESTING,
    );
}

#[test]
fn what_builds_no_temporal_node_is_not_a_level() {
    // Seventeen conjuncts are a tree about 20 deep.
    let conjuncts = vec![format!("formerly within 1h {READ}"); 17].join(" && ");
    assert_accepted(temporal_policy(&conjuncts));

    // `-1` is one integer token, not a negation over `1`: 29 `!`s, the
    // comparison, and its terms are exactly the limit.
    let negative = |n| format!("{}context.input.x == -1{}", "!(".repeat(n), ")".repeat(n));
    parse_on_small_stack(temporal_policy(&negative(DEFAULT_MAX_DEPTH - 3)))
        .expect("`-1` is a leaf");
    assert_rejected(
        temporal_policy(&negative(DEFAULT_MAX_DEPTH - 2)),
        "parse",
        // One too deep only once the marker's level is counted, so the root
        // measure reports the expression limit.
        EXPR,
    );

    // A field named like a binder or an operator counts as a keyword, but
    // only until its predicate's braces close.
    let fields = "count: 1, sum: 1, previous: 1, formerly: 1, since: 1, exists: 1, where: 1";
    let predicate = format!(r#"Ns::Action::"Read"::request{{ {fields} }}"#);
    let conjuncts = vec![format!("formerly within 1h {predicate}"); 17].join(" && ");
    parse_on_small_stack(temporal_policy(&conjuncts)).expect("the braces release the fields");
}

#[test]
fn one_count_spans_cedar_and_temporal() {
    // The block is the first of `n` Cedar terms, so the marker sits at depth
    // `n`, its `formerly` at `n + 1`, and the predicate at `n + 2`.
    let chain = |n| {
        let mut terms = vec!["true".to_string(); n];
        terms[0] = format!("temporal {{ formerly within 1h {READ} }}");
        policy(&terms.join(" && "))
    };
    assert_accepted(chain(DEFAULT_MAX_DEPTH - 2));
    // Either way past the limit, the one measured count over the whole tree
    // (Cedar levels plus the block's) refuses it at the root.
    assert_rejected(chain(DEFAULT_MAX_DEPTH - 1), "parse", EXPR);
    assert_rejected(chain(DEFAULT_MAX_DEPTH + 1), "parse", EXPR);
}

#[test]
fn the_deepest_text_the_scans_admit_is_an_error_on_a_small_stack() {
    // The scans admit 32 levels in the policy and, in the block, 32 levels of
    // open brackets and keywords; the generated parsers recurse through all
    // of them. An `exists` is one keyword, and 31 of them, then the
    // predicate's braces, are a tree the measured root check rejects. An aggregate is
    // three (`count` or `sum`, `for`, `where`), so the scan admits only ten,
    // a tree within the depth limit that a later check rejects (`t` is
    // unused, `?v` is outside a macro); an eleventh is a scan error.
    let parens = DEFAULT_MAX_DEPTH - 3;
    let block = |body: &str| {
        let block = format!("temporal {{ {body} }}");
        policy(&format!(
            "{}{block}{}",
            "(".repeat(parens),
            ")".repeat(parens)
        ))
    };
    let exists = format!(
        "{}{READ}",
        "exists (t: Long). ".repeat(DEFAULT_MAX_DEPTH - 1)
    );
    assert!(
        temporal_scan(&exists).is_none(),
        "the scan admits `{exists}`"
    );
    // The 31-binder condition itself is within the limit, so it survives to
    // the semantic checks, which reject the unused binder; what matters here
    // is that pest recursed through all 31 binders on the small stack first.
    assert_rejected(block(&exists), "parse", "is not range-restricted");
    let aggregates = (DEFAULT_MAX_DEPTH - 2) / 3;
    for binder in [
        "count for (t: Long). where ",
        "sum ?v for (t: Long). where ",
    ] {
        let body = |n| format!("{}{READ}{}", binder.repeat(n), " >= 1".repeat(n));
        assert!(
            temporal_scan(&body(aggregates)).is_none(),
            "the scan admits {aggregates}"
        );
        parse_on_small_stack(block(&body(aggregates))).expect_err(binder);
        assert!(temporal_scan(&body(aggregates + 1)).is_some(), "{binder}");
    }
    // The condition braces are one level.
    let ifs = DEFAULT_MAX_DEPTH - 1 - parens;
    let src = policy(&format!(
        "{}{}true{}{}",
        "(".repeat(parens),
        "if ".repeat(ifs),
        " then true else true".repeat(ifs),
        ")".repeat(parens)
    ));
    parse_on_small_stack(src).expect("within both limits");
}

#[test]
fn a_comma_in_a_binder_list_releases_no_keyword() {
    // A `for` list puts a `,` at the same bracket level as the open `exists`
    // and `where`. A scan that released keywords at a `,` saw this as two
    // levels deep for any `n`, and the generated parser overflowed a 2 MiB
    // stack at `n` = 3000.
    let n = 3_000;
    let body = format!(
        "{}{READ}{}",
        "exists (t: Long). count for (a: Long), (b: Long). where ".repeat(n),
        " >= 1".repeat(n)
    );
    let error = temporal_scan(&body).expect("the scan refuses it");
    assert!(error.to_string().contains(NESTING), "{error}");
    assert_rejected(temporal_policy(&body), "parse", NESTING);
}

#[test]
fn a_block_at_the_scan_limit_under_cedar_at_the_depth_limit_is_an_error() {
    // The temporal parser runs inside the Cedar builder, and the temporal scan
    // does not count the enclosing depth, so a block at the end of a tree at
    // the depth limit still makes the generated parser recurse through all 31
    // binders the scan admits (a 32nd `exists` is a scan error). The builders
    // fold `!` runs and `&&` chains in loops, so these shapes are deep
    // trees, not deep builder stacks; the
    // deep-stack shape, brackets around the block, is
    // `the_deepest_text_the_scans_admit_is_an_error_on_a_small_stack`.
    let binders = DEFAULT_MAX_DEPTH - 1;
    let body = format!("{}{READ}", "exists (t: Long). ".repeat(binders));
    assert!(temporal_scan(&body).is_none(), "the scan admits the body");
    let block = format!("temporal {{ {body} }}");

    // 31 `!`s put the marker at depth 32. The block's own tree is within the
    // limit, so the error is the semantic binding check's; the property under
    // test is that the temporal parse under the deep Cedar text fits the
    // small stack.
    let bangs = format!("{}{block}", "!".repeat(DEFAULT_MAX_DEPTH - 1));
    assert_rejected(policy(&bangs), "parse", "is not range-restricted");

    // 31 `true` terms and the block, which is first or last of the chain.
    let mut terms = vec!["true".to_string(); DEFAULT_MAX_DEPTH];
    terms[DEFAULT_MAX_DEPTH - 1] = block.clone();
    assert_rejected(policy(&terms.join(" && ")), "parse", "is not range-restricted");
    terms.swap(0, DEFAULT_MAX_DEPTH - 1);
    assert_rejected(policy(&terms.join(" && ")), "parse", "is not range-restricted");
}

#[test]
fn both_limits_together_are_accepted_on_a_small_stack() {
    // A chain at the depth limit inside the deepest brackets.
    let n = DEFAULT_MAX_DEPTH - 1;
    let chain = vec!["true"; DEFAULT_MAX_DEPTH].join(" && ");
    assert_accepted(policy(&format!(
        "{}{chain}{}",
        "(".repeat(n),
        ")".repeat(n)
    )));
}

// ── A caller-set limit ──────────────────────────────────────────────────

/// A stack large enough for the raised limit's shapes in a debug build.
const LARGE_STACK: usize = 8 << 20;

fn limited(max_depth: usize) -> ParseOptions {
    ParseOptions::default().max_depth(max_depth)
}

/// Parse and macro-expand `src` under `options` on a thread with `stack`
/// bytes of stack.
fn parse_with_on(src: String, options: ParseOptions, stack: usize) -> Result<(), String> {
    std::thread::Builder::new()
        .stack_size(stack)
        .spawn(move || {
            ParsedPolicySet::parse_with(&src, &ServiceSchema::defaults(), &options)
                .map(drop)
                .map_err(describe)
        })
        .expect("spawn")
        .join()
        .expect("must not panic")
}

/// Parse, expand, lower, and validate `src` under `options` on a thread with
/// `stack` bytes of stack, through the fused `from_str_with`.
#[track_caller]
fn assert_accepted_with(src: String, options: ParseOptions, stack: usize) {
    let outcome = std::thread::Builder::new()
        .stack_size(stack)
        .spawn(move || {
            let policy_schema = PolicySchema::from_cedarschema_str(&action_schema())
                .map_err(|e| format!("schema: {e}"))?;
            let lowered = LoweredPolicySet::from_str_with(
                &src,
                &ServiceSchema::defaults(),
                &policy_schema,
                &options,
            )
            .map_err(describe)?;
            let result = Validator::new().validate(&lowered);
            if !result.validation_passed() {
                let errors: Vec<_> = result.validation_errors().map(|e| e.to_string()).collect();
                return Err(format!("validate: {errors:?}"));
            }
            Ok(())
        })
        .expect("spawn")
        .join()
        .expect("must not panic");
    if let Err(error) = outcome {
        panic!("expected the policy to be accepted, got {error}");
    }
}

#[track_caller]
fn assert_rejected_with(src: String, options: ParseOptions, phase: &str, message: &str) {
    let error = parse_with_on(src, options, LARGE_STACK).expect_err("must be rejected");
    assert!(
        error.starts_with(phase) && error.contains(message),
        "expected a {phase} error mentioning {message:?}, got: {error}"
    );
}

fn parens(n: usize) -> String {
    policy(&format!("{}true{}", "(".repeat(n), ")".repeat(n)))
}

fn and_chain(n: usize) -> String {
    policy(&vec!["true"; n].join(" && "))
}

/// `n` sibling `formerly`s in one block: the first conjunct's predicate is at
/// depth `n + 2`, and the scan counts `n` keywords and the last braces.
fn formerly_chain(n: usize) -> String {
    temporal_policy(&vec![format!("formerly within 1h {READ}"); n].join(" && "))
}

/// A `def cedar` whose `?x` sits at depth 3 of its body, called with an
/// `n`-term chain: the expansion is `n + 2` deep, the call site `n + 1`.
fn expanded(n: usize) -> String {
    let call = format!("m({})", vec!["true"; n].join(" && "));
    format!(
        "def cedar m(?x) {{ ?x && true && true }};\n{}",
        policy(&call)
    )
}

#[test]
fn the_default_options_are_the_default_limit() {
    assert_eq!(ParseOptions::default().max_depth, DEFAULT_MAX_DEPTH);
    assert_eq!(limited(DEFAULT_MAX_DEPTH), ParseOptions::default());
}

#[test]
fn a_lowered_limit_rejects_one_past_it_what_the_default_admits() {
    let limit = 8;
    let options = limited(limit);
    let nesting = format!("nesting exceeds the maximum depth of {limit}");
    let expr = format!("expression nested deeper than the limit of {limit}");
    let expansion = format!("macro expansion nested deeper than the limit of {limit}");

    // The condition braces are the first level of nesting.
    parse_with_on(parens(limit - 1), options, STACK).expect("at the limit");
    assert_rejected_with(parens(limit), options, "parse", &nesting);
    parse_on_small_stack(parens(limit)).expect("the default admits it");

    parse_with_on(and_chain(limit), options, STACK).expect("at the limit");
    assert_rejected_with(and_chain(limit + 1), options, "parse", &expr);
    parse_on_small_stack(and_chain(limit + 1)).expect("the default admits it");

    parse_with_on(formerly_chain(limit - 2), options, STACK).expect("at the limit");
    assert_rejected_with(formerly_chain(limit - 1), options, "parse", &expr);
    parse_on_small_stack(formerly_chain(limit - 1)).expect("the default admits it");

    parse_with_on(expanded(limit - 2), options, STACK).expect("at the limit");
    assert_rejected_with(expanded(limit - 1), options, "macro", &expansion);
    parse_on_small_stack(expanded(limit - 1)).expect("the default admits it");

    // The fused entry points take the same options.
    let policy_schema = PolicySchema::from_cedarschema_str(&action_schema()).expect("schema");
    let error = LoweredPolicySet::from_str_with(
        &and_chain(limit + 1),
        &ServiceSchema::defaults(),
        &policy_schema,
        &options,
    )
    .expect_err("one past the limit");
    assert!(error.to_string().contains(&expr), "{error}");
    let entries = [(
        and_chain(limit + 1),
        "a".parse::<dogwood_language::Distincter>()
            .expect("a distincter"),
    )];
    let entries: Vec<_> = entries
        .iter()
        .map(|(s, d)| (s.as_str(), d.clone()))
        .collect();
    let error = LoweredPolicySet::from_many_str_with(
        &entries,
        &ServiceSchema::defaults(),
        &policy_schema,
        &options,
    )
    .expect_err("one past the limit");
    assert!(error.to_string().contains(&expr), "{error}");
}

#[test]
fn a_raised_limit_admits_what_the_default_refuses_on_a_large_stack() {
    let limit = 64;
    let options = limited(limit);
    let n = 40;

    // 39 parentheses inside the condition braces are 40 levels of nesting.
    assert_rejected(parens(n - 1), "parse", NESTING);
    assert_accepted_with(parens(n - 1), options, LARGE_STACK);
    assert_rejected(and_chain(n), "parse", EXPR);
    assert_accepted_with(and_chain(n), options, LARGE_STACK);
    assert_rejected(formerly_chain(n), "parse", NESTING);
    assert_accepted_with(formerly_chain(n), options, LARGE_STACK);

    // One past the raised limit is refused, with the raised limit named.
    assert_accepted_with(parens(limit - 1), options, LARGE_STACK);
    assert_rejected_with(
        parens(limit),
        options,
        "parse",
        &format!("nesting exceeds the maximum depth of {limit}"),
    );
    assert_accepted_with(and_chain(limit), options, LARGE_STACK);
    assert_rejected_with(
        and_chain(limit + 1),
        options,
        "parse",
        &format!("expression nested deeper than the limit of {limit}"),
    );
}

// ── Flat text that lowers deeper than it parses ─────────────────────────
//
// A `has` path is flat in the surface tree but deep once lowered: on Cedar
// 4.11 every multi-segment `e has a.b.c` becomes a left-nested `&&` of `has`
// tests, reserved-word segments or not. The measure counts what lowering builds, so it is bounded by the
// same `max_depth`. (A policy's clauses used to be the other such shape;
// they now lower to a balanced tree, see tests/clause_fold.rs.)

/// `context has input.x.x…`, `segments` long: a real path through `L29`.
fn has_path(segments: usize) -> String {
    policy(&format!("context has input{}", ".x".repeat(segments - 1)))
}

#[test]
fn a_has_path_is_measured_at_its_lowered_depth() {
    // `k` segments lower to exactly `k + 1` levels below the `&&` root, so 30
    // reach 32. Cedar 4.11 desugars this plain-identifier path too, so 30 is
    // the deepest path that lowers, not an over-count.
    assert_accepted(has_path(DEFAULT_MAX_DEPTH - 2));
    assert_rejected(has_path(DEFAULT_MAX_DEPTH - 1), "parse", EXPR);
}

#[test]
fn a_long_reserved_word_has_path_is_a_parse_error() {
    // The finding's shape, which aborted in lowering at about 300 segments.
    // On Cedar 4.11 a plain-identifier path desugars to the same `&&` chain,
    // so it is covered too.
    for n in [300, 400_000] {
        for head in ["if", "a"] {
            let body = format!("context has {head}{}", ".a".repeat(n - 1));
            assert_rejected(policy(&body), "parse", EXPR);
        }
    }
}

// ── Action schema ───────────────────────────────────────────────────────

/// An action schema whose `context.input` is `n` nested `Set<…>`s.
fn set_schema(n: usize) -> String {
    format!(
        "namespace Ns {{ entity User; entity Res; action \"Read\" appliesTo {{ \
         principal: [User], resource: [Res], context: {{ input: {}String{} }} }}; }}",
        "Set<".repeat(n),
        ">".repeat(n)
    )
}

#[test]
fn a_deep_action_schema_is_refused_before_cedar_parses_it() {
    for n in [2 * DEFAULT_MAX_DEPTH, 1_000, 100_000] {
        let schema = set_schema(n);
        let outcome = on_small_stack(move || PolicySchema::from_cedarschema_str(&schema).map(drop));
        match outcome {
            Err(Error::ActionSchema(m)) => assert!(m.contains("nested too deeply"), "{n}: {m}"),
            other => panic!("{n}: expected an action-schema error, got {other:?}"),
        }
    }
    // The schema these tests lower against nests about 30 records deep.
    PolicySchema::from_cedarschema_str(&set_schema(2)).expect("a shallow schema loads");
    PolicySchema::from_cedarschema_str(&action_schema()).expect("the test schema loads");
}
