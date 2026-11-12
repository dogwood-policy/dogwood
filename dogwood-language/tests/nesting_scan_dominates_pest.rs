//! The lexical nesting scan over-approximates the generated parsers'
//! recursion: for every policy text and every temporal block body,
//! `nesting_estimate(text) >= reentries(text)`, where the re-entries are
//! counted on the pest pair tree (see `dogwood_language::policy_reentries`
//! and `dogwood_language::temporal_reentries` for the rules counted).
//!
//! Checked over every `.dw` file under `tests/` and over the generated shapes
//! of `parser_nesting_depth.rs`. Only the direction scan >= re-entries is
//! asserted; the margin is printed, not pinned.

use dogwood_language::{TEMPORAL_NESTING_KEYWORDS, policy_reentries, temporal_reentries};
use dogwood_syntax::{POLICY_NESTING_KEYWORDS, Pair, ParseOptions, Rule, nesting_estimate};

/// The helpers parse with no depth limit, so the generated parsers recurse as
/// deep as the text nests; a large stack keeps that off the 2 MiB default.
const STACK: usize = 8 << 20;

/// The corpus includes fuzz inputs; give the unlimited parse ample room.
const CORPUS_STACK: usize = 256 << 20;

const SCOPE: &str = r#"(principal, action == Ns::Action::"Read", resource)"#;
const READ: &str = r#"Ns::Action::"Read"::request{}"#;

fn policy(body: &str) -> String {
    format!("@id(\"p\") permit {SCOPE} when {{ {body} }};")
}

fn temporal_policy(body: &str) -> String {
    format!("@id(\"p\") permit {SCOPE} when temporal {{ {body} }};")
}

fn on_stack<T: Send + 'static>(stack: usize, f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(stack)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("must not panic")
}

/// The temporal bodies in a policy text, as the parser hands them to the
/// temporal grammar: each `temporal { … }` block's `block_inner`, and each
/// `def temporal` body.
fn temporal_bodies(source: &str) -> Vec<&str> {
    let unlimited = ParseOptions::default().max_depth(usize::MAX);
    let (_, source) = dogwood_syntax::split_bom(source);
    let Ok(pairs) = dogwood_syntax::parse_with(Rule::policies, source, &unlimited) else {
        return Vec::new();
    };
    let mut bodies = Vec::new();
    let mut stack: Vec<Pair<'_>> = pairs.collect();
    while let Some(pair) = stack.pop() {
        match pair.as_rule() {
            Rule::extension_marker => bodies.extend(block(&pair).map(|body| body.as_str())),
            Rule::def_decl => {
                let temporal = pair.clone().into_inner().any(|child| {
                    child.as_rule() == Rule::def_kind
                        && child
                            .into_inner()
                            .any(|kind| kind.as_rule() == Rule::kw_def_temporal)
                });
                if temporal {
                    bodies.extend(block(&pair).map(|body| body.as_str()));
                }
            }
            _ => {}
        }
        stack.extend(pair.into_inner());
    }
    bodies
}

fn block<'source>(pair: &Pair<'source>) -> Option<Pair<'source>> {
    pair.clone()
        .into_inner()
        .find(|child| child.as_rule() == Rule::block_inner)
}

#[derive(Debug, Default)]
struct Tally {
    parsed: usize,
    skipped: usize,
    max_estimate: usize,
    max_reentries: usize,
    /// The smallest `estimate - reentries` seen.
    min_margin: Option<usize>,
    violations: Vec<String>,
}

impl Tally {
    fn record(&mut self, what: &str, estimate: usize, reentries: Result<usize, String>) {
        let Ok(reentries) = reentries else {
            self.skipped += 1;
            return;
        };
        self.parsed += 1;
        self.max_estimate = self.max_estimate.max(estimate);
        self.max_reentries = self.max_reentries.max(reentries);
        match estimate.checked_sub(reentries) {
            Some(margin) => {
                self.min_margin = Some(self.min_margin.map_or(margin, |m| m.min(margin)));
            }
            None => self.violations.push(format!(
                "{what}: estimate {estimate} < reentries {reentries}"
            )),
        }
    }

    fn report(&self, label: &str) {
        eprintln!(
            "{label}: parsed {} / skipped {} / max estimate {} / max reentries {} / min margin {:?}",
            self.parsed, self.skipped, self.max_estimate, self.max_reentries, self.min_margin
        );
    }
}

/// Check a policy text and every temporal body in it.
fn check_policy(what: &str, text: &str, policies: &mut Tally, bodies: &mut Tally) {
    policies.record(
        what,
        nesting_estimate(text, POLICY_NESTING_KEYWORDS),
        policy_reentries(text),
    );
    for (index, body) in temporal_bodies(text).into_iter().enumerate() {
        bodies.record(
            &format!("{what} (temporal body {index})"),
            nesting_estimate(body, TEMPORAL_NESTING_KEYWORDS),
            temporal_reentries(body),
        );
    }
}

fn dw_files(dir: &std::path::Path) -> Vec<std::path::PathBuf> {
    let mut files = Vec::new();
    let mut dirs = vec![dir.to_path_buf()];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir).expect("readable test directory") {
            let path = entry.expect("directory entry").path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|ext| ext == "dw") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

#[track_caller]
fn assert_no_violations(label: &str, tally: &Tally) {
    tally.report(label);
    assert!(
        tally.violations.is_empty(),
        "{label}: the scan under-counts pest's recursion:\n{}",
        tally.violations.join("\n")
    );
}

#[test]
fn the_scan_dominates_pest_over_every_policy_in_the_tests() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let (policies, bodies) = on_stack(CORPUS_STACK, move || {
        let mut policies = Tally::default();
        let mut bodies = Tally::default();
        let files = dw_files(&dir);
        assert!(files.len() > 1000, "found only {} `.dw` files", files.len());
        for path in files {
            let text = std::fs::read_to_string(&path).expect("readable policy");
            let name = path
                .strip_prefix(&dir)
                .unwrap_or(&path)
                .display()
                .to_string();
            check_policy(&name, &text, &mut policies, &mut bodies);
        }
        (policies, bodies)
    });
    assert_no_violations("policy files", &policies);
    assert_no_violations("temporal bodies in policy files", &bodies);
    assert!(policies.parsed > 1000, "{policies:?}");
    assert!(bodies.parsed > 100, "{bodies:?}");
}

/// The shapes of `parser_nesting_depth.rs`, as policy texts, at size `n`.
fn generated_policies(n: usize) -> Vec<(&'static str, String)> {
    let comma = "exists (t: Long). count for (a: Long), (b: Long). where ";
    vec![
        (
            "parens",
            policy(&format!(
                "{}context.input.x == 1{}",
                "(".repeat(n),
                ")".repeat(n)
            )),
        ),
        (
            "sets",
            policy(&format!("{}1{} == [1]", "[".repeat(n), "]".repeat(n))),
        ),
        (
            "records",
            policy(&format!("{}1{} == {{}}", "{a: ".repeat(n), "}".repeat(n))),
        ),
        (
            "nested if",
            policy(&format!(
                "{}true{}",
                "if ".repeat(n),
                " then true else true".repeat(n)
            )),
        ),
        (
            "else-if chain",
            policy(&format!("{}true", "if true then true else ".repeat(n))),
        ),
        (
            "macro call arguments",
            format!(
                "def cedar m(?x) {{ ?x }};\n{}",
                policy(&format!("{}true{}", "m(".repeat(n), ")".repeat(n)))
            ),
        ),
        ("and chain", policy(&vec!["true"; n].join(" && "))),
        ("bang run", policy(&format!("{}true", "!".repeat(n)))),
        (
            "member chain",
            policy(&format!("context{} == 1", ".x".repeat(n))),
        ),
        (
            "def cedar body",
            format!(
                "def cedar m() {{ {} }};\n{}",
                vec!["(true"; n].join(" && ") + ")".repeat(n).as_str(),
                policy("m()")
            ),
        ),
        (
            "block in parens",
            policy(&format!(
                "{}temporal {{ formerly within 1h {READ} }}{}",
                "(".repeat(n),
                ")".repeat(n)
            )),
        ),
        (
            "if around a block",
            policy(&format!(
                "{}temporal {{ {READ} }}{}",
                "if ".repeat(n),
                " then true else true".repeat(n)
            )),
        ),
        (
            "nested formerly",
            temporal_policy(&format!(
                "{}{READ}{}",
                "formerly within 1h (".repeat(n),
                ")".repeat(n)
            )),
        ),
        (
            "exists run",
            temporal_policy(&format!("{}{READ}", "exists (t: Long). ".repeat(n))),
        ),
        (
            "count run",
            temporal_policy(&format!(
                "{}{READ}{}",
                "count for (t: Long). where ".repeat(n),
                " >= 1".repeat(n)
            )),
        ),
        (
            "sum run",
            temporal_policy(&format!(
                "{}{READ}{}",
                "sum ?v for (t: Long). where ".repeat(n),
                " >= 1".repeat(n)
            )),
        ),
        (
            "exists run, no space after the binder dot",
            temporal_policy(&format!("{}{READ}", "exists (t: Long).".repeat(n))),
        ),
        (
            "count run, no space after the binder dot",
            temporal_policy(&format!(
                "{}{READ}{}",
                "count for (t: Long).where ".repeat(n),
                " >= 1".repeat(n)
            )),
        ),
        (
            "sibling formerly",
            temporal_policy(&vec![format!("formerly within 1h {READ}"); n].join(" && ")),
        ),
        (
            "negated formerly",
            temporal_policy(&format!(
                "{}formerly within 1h {READ}{}",
                "!(".repeat(n),
                ")".repeat(n)
            )),
        ),
        ("since chain", {
            let since = format!(" since within 1h ({READ}");
            temporal_policy(&format!("{READ}{}{}", since.repeat(n), ")".repeat(n)))
        }),
        (
            "previous of previous",
            temporal_policy(&format!(
                "{}{READ}{}",
                "previous within 1h (".repeat(n),
                ")".repeat(n)
            )),
        ),
        (
            "nested arrays",
            temporal_policy(&format!(
                "formerly within 1h Ns::Action::\"Read\"::request{{ a: {}1{} }}",
                "[".repeat(n),
                "]".repeat(n)
            )),
        ),
        (
            "nested arithmetic",
            temporal_policy(&format!("{}1{} > 0", "(1 + ".repeat(n), ")".repeat(n))),
        ),
        ("bound binders", {
            let names: Vec<_> = (0..n).map(|i| format!("t{i}")).collect();
            let open: String = names
                .iter()
                .map(|t| format!("exists ({t}: Timepoint). "))
                .collect();
            let uses: Vec<_> = names.iter().map(|t| format!("tp({t})")).collect();
            temporal_policy(&format!("{open}({})", uses.join(" && ")))
        }),
        (
            "compared aggregate",
            temporal_policy(&format!(
                "{}(count for (t: Timepoint). where tp(t)) >= 1{}",
                "!(".repeat(n),
                ")".repeat(n)
            )),
        ),
        (
            "binder list",
            temporal_policy(&format!("{}{READ}{}", comma.repeat(n), " >= 1".repeat(n))),
        ),
        (
            "def temporal exists run",
            format!(
                "def temporal m() {{ {}{READ} }};\n{}",
                "exists (t: Long). ".repeat(n),
                temporal_policy("m()")
            ),
        ),
    ]
}

#[test]
fn the_scan_dominates_pest_over_the_generated_shapes() {
    let (policies, bodies) = on_stack(STACK, || {
        let mut policies = Tally::default();
        let mut bodies = Tally::default();
        // Nested temporal calls take pest time exponential in their nesting
        // (backtracking between `call` as a condition and as a term), so
        // that shape stops at 12: 16 already takes seconds.
        let calls = |n: usize| {
            let text = temporal_policy(&format!("{}{READ}{}", "m(".repeat(n), ")".repeat(n)));
            ("nested calls", text)
        };
        for n in [1, 6, 12, 31, 32, 33, 200] {
            let small_calls = [1, 6, 12].contains(&n).then(|| calls(n));
            for (shape, text) in generated_policies(n).into_iter().chain(small_calls) {
                let what = format!("{shape} at {n}");
                // Every shape is grammatical; a parse failure is a broken
                // generator, not a skip.
                if let Err(error) = policy_reentries(&text) {
                    panic!("{what} does not parse: {error}");
                }
                check_policy(&what, &text, &mut policies, &mut bodies);
            }
        }
        (policies, bodies)
    });
    assert_no_violations("generated policies", &policies);
    assert_no_violations("generated temporal bodies", &bodies);
    assert_eq!(policies.skipped, 0, "{policies:?}");
    assert_eq!(bodies.skipped, 0, "{bodies:?}");
}

#[test]
fn the_scan_dominates_pest_over_a_binder_list() {
    // A `for` list puts a `,` at the bracket level of the open `exists` and
    // `where`. The first revision of the scan released keywords at a `,`, saw
    // this as two levels deep, and under-counted it.
    let n = 50;
    let body = format!(
        "{}{READ}{}",
        "exists (t: Long). count for (a: Long), (b: Long). where ".repeat(n),
        " >= 1".repeat(n)
    );
    let (estimate, reentries) = on_stack(STACK, move || {
        let reentries = temporal_reentries(&body).expect("parses");
        (
            nesting_estimate(&body, TEMPORAL_NESTING_KEYWORDS),
            reentries,
        )
    });
    eprintln!("binder list at {n}: estimate {estimate}, reentries {reentries}");
    assert!(reentries >= 3 * n, "each repetition re-enters: {reentries}");
    assert!(estimate >= reentries, "{estimate} < {reentries}");
}
