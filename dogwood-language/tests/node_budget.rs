//! Trees whose size grows exponentially in their depth are an ordinary error,
//! never an out-of-memory kill, and real policies lower unchanged.
//!
//! Nesting depth does not bound size. A macro whose body mentions its
//! parameter twice, called on its own result, doubles the tree at every level
//! (2^30 nodes at depth 31), and lowering does the same to a nested `previous`
//! (2^n) and a right-nested `since` (3^n) when the schema has a universal pin,
//! as the default does. `ParseOptions::max_nodes`, by default
//! `dogwood_language::DEFAULT_MAX_NODES` (1,000,000), bounds the nodes macro
//! expansion creates for one parsed set and the nodes lowering creates for
//! that set's temporal leaves; it is one budget per set, not per condition or
//! leaf. Each test runs on a 2 MiB thread, and the big shapes must be refused
//! without allocating the excess: the refusals are bounded by the bytes the
//! parsing thread allocates, never by wall-clock time.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

use dogwood_language::{
    DEFAULT_MAX_NODES, Error, LoweredPolicySet, ParseOptions, ParsedPolicySet, PolicySchema,
    ServiceSchema,
};

/// `System`, counting each thread's live and peak heap bytes.
///
/// The counters are thread-local, so tests running in parallel under the
/// default harness do not mix: a measurement sees only the allocations of
/// the thread it runs on. (Bytes freed on a thread other than the one that
/// allocated them only lower that thread's count, which a peak ignores.)
struct Counting;

thread_local! {
    static CURRENT: Cell<isize> = const { Cell::new(0) };
    static PEAK: Cell<isize> = const { Cell::new(0) };
}

fn record(delta: isize) {
    // `try_with`: an allocation during thread teardown must not panic.
    let _ = CURRENT.try_with(|current| {
        let now = current.get() + delta;
        current.set(now);
        let _ = PEAK.try_with(|peak| peak.set(peak.get().max(now)));
    });
}

// SAFETY: every call is forwarded unchanged to `System`; the wrapper only
// updates thread-local counters, which neither allocate nor unwind.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            record(layout.size() as isize);
        }
        ptr
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if !ptr.is_null() {
            record(layout.size() as isize);
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) };
        record(-(layout.size() as isize));
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let new = unsafe { System.realloc(ptr, layout, new_size) };
        if !new.is_null() {
            record(new_size as isize - layout.size() as isize);
        }
        new
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

/// Run `f` and return its result with the most heap bytes the calling thread
/// held during it, beyond what it held before.
fn peak_bytes_during<T>(f: impl FnOnce() -> T) -> (T, usize) {
    let before = CURRENT.with(Cell::get);
    PEAK.with(|peak| peak.set(before));
    let value = f();
    let peak = PEAK.with(Cell::get);
    (value, usize::try_from(peak - before).unwrap_or(0))
}

const MIB: usize = 1 << 20;

/// Rust's default stack size for spawned threads.
const STACK: usize = 2 << 20;

const MACRO_BUDGET: &str = "macro expansion exceeds the node budget of 1000000";
const LOWERING_BUDGET: &str = "lowering exceeds the node budget of 1000000";

const SCHEMA: &str = "namespace Ns {\n  entity User;\n  entity Res;\n  \
                      action \"Read\" appliesTo { principal: [User], resource: [Res], context: {} };\n}\n";
const SCOPE: &str = r#"(principal, action == Ns::Action::"Read", resource)"#;
const READ: &str = r#"Ns::Action::"Read"::request{}"#;

fn policy(body: &str) -> String {
    format!("@id(\"p\") permit {SCOPE} when {{ {body} }};")
}

fn temporal_policy(body: &str) -> String {
    format!("@id(\"p\") permit {SCOPE} when temporal {{ {body} }};")
}

/// `wrap` applied `n` times to `inner`.
fn nest(n: usize, inner: &str, wrap: impl Fn(&str) -> String) -> String {
    (0..n).fold(inner.to_string(), |body, _| wrap(&body))
}

fn previous(n: usize) -> String {
    nest(n, READ, |b| format!("previous within 1h ({b})"))
}

fn since_right(n: usize) -> String {
    nest(n, READ, |b| format!("{READ} since within 1h ({b})"))
}

fn since_left(n: usize) -> String {
    nest(n, READ, |b| format!("({b}) since within 1h {READ}"))
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
        Error::Cedarify(_) => format!("lower: {error}"),
        other => format!("other: {other}"),
    }
}

/// Parse `src` under `options` and lower it against [`SCHEMA`] with the
/// default service schema (which pins `callerPrincipal`), on a 2 MiB thread.
fn lower_with(src: String, options: ParseOptions) -> Result<LoweredPolicySet, String> {
    on_small_stack(move || {
        let schema = PolicySchema::from_cedarschema_str(SCHEMA).map_err(|e| format!("{e}"))?;
        ParsedPolicySet::parse_with(&src, &ServiceSchema::defaults(), &options)
            .map_err(describe)?
            .lower(&schema)
            .map_err(describe)
    })
}

fn lower(src: String) -> Result<LoweredPolicySet, String> {
    lower_with(src, ParseOptions::default())
}

/// The rewritten leaves, as text.
fn leaves(lowered: &LoweredPolicySet) -> String {
    format!("{:?}", lowered.temporal_fields().collect::<Vec<_>>())
}

/// Require `src` to be rejected in `phase` with `message` (parsed and lowered
/// as [`lower`] does, on a 2 MiB thread) while that thread allocates at most
/// `max_bytes` beyond what it held before.
#[track_caller]
fn assert_rejected_within_bytes(src: String, phase: &str, message: &str, max_bytes: usize) {
    let (result, peak) = on_small_stack(move || {
        peak_bytes_during(|| {
            let schema = PolicySchema::from_cedarschema_str(SCHEMA).map_err(|e| format!("{e}"))?;
            ParsedPolicySet::parse_with(&src, &ServiceSchema::defaults(), &ParseOptions::default())
                .map_err(describe)?
                .lower(&schema)
                .map_err(describe)
                .map(drop)
        })
    });
    let error = result.expect_err("must be rejected");
    assert!(
        error.starts_with(phase) && error.contains(message),
        "expected a {phase} error mentioning {message:?}, got: {error}"
    );
    assert!(
        peak <= max_bytes,
        "allocated {peak} bytes at peak, more than {max_bytes}"
    );
}

// ── Macro expansion ─────────────────────────────────────────────────────

fn doubling_cedar(n: usize) -> String {
    let call = nest(n, "context.flag", |b| format!("d({b})"));
    format!("def cedar d(?x) {{ ?x && ?x }};\n{}", policy(&call))
}

#[test]
fn a_doubling_cedar_macro_is_a_macro_error() {
    // 2^30 nodes at depth 31: shallow, far over the budget. Unbounded, at
    // about 1.6 KB per copy (measured at depth 18), that is some 1.7 TB.
    // Refused at a measured peak of 95,184,290 bytes (91 MiB).
    assert_rejected_within_bytes(doubling_cedar(30), "macro:", MACRO_BUDGET, 384 * MIB);
}

#[test]
fn a_shallow_doubling_cedar_macro_expands() {
    let src = doubling_cedar(4);
    on_small_stack(move || ParsedPolicySet::parse(&src, &ServiceSchema::defaults()).map(drop))
        .expect("2^4 copies fit the default budget");
}

#[test]
fn a_body_with_many_mentions_is_a_macro_error() {
    // 50 mentions nested 4 deep is 50^4 = 6,250,000 copies of the argument.
    let body = format!("[{}]", vec!["?x"; 50].join(", "));
    let call = nest(4, "context.flag", |b| format!("m({b})"));
    let src = format!("def cedar m(?x) {{ {body} }};\n{}", policy(&call));
    // Unbounded, at about 1.2 KB per copy (measured at 50^3), that is some
    // 7.4 GB. Refused at a measured peak of 122,773,672 bytes (117 MiB).
    assert_rejected_within_bytes(src, "macro:", MACRO_BUDGET, 512 * MIB);
}

#[test]
fn a_widening_temporal_macro_is_a_macro_error() {
    // The same growth through sigil substitution in a temporal block: sixteen
    // mentions, balanced, nested 6 deep is 16^6 = 16,777,216 copies. (Width
    // rather than depth: parsing nested temporal macro calls takes time
    // exponential in their nesting, whatever the body.)
    let pair = "(?c && ?c)";
    let quad = format!("({pair} && {pair})");
    let oct = format!("({quad} && {quad})");
    let call = nest(6, READ, |b| format!("w({b})"));
    let src = format!(
        "def temporal w(?c) {{ {oct} && {oct} }};\n{}",
        temporal_policy(&call)
    );
    // Unbounded, at about 1.9 KB per copy (measured at 16^4), that is some
    // 31 GB. Refused at a measured peak of 148,200,197 bytes (141 MiB).
    assert_rejected_within_bytes(src, "macro:", MACRO_BUDGET, 512 * MIB);
}

// ── Lowering (pin relativization) ───────────────────────────────────────

#[test]
fn relativization_runs_under_the_default_pin() {
    let lowered = lower(temporal_policy(&previous(2))).expect("lowers");
    let leaves = leaves(&lowered);
    assert!(leaves.contains("callerPrincipal"), "{leaves}");
    assert!(leaves.contains("__pin_ti"), "not relativized: {leaves}");
}

#[test]
fn nested_previous_is_a_lowering_error() {
    // 2^15 copies: the deepest nesting the parser's depth limit of 32 admits,
    // so only about twice the budget. Unbounded it allocates a measured
    // 202,328,365 bytes (193 MiB); refused at a measured peak of 101,149,168
    // bytes (96 MiB). The bound sits between the two, not at four times the
    // peak, so that it still fails if the budget stops refusing early.
    assert_rejected_within_bytes(
        temporal_policy(&previous(15)),
        "lower:",
        LOWERING_BUDGET,
        128 * MIB,
    );
}

#[test]
fn right_nested_since_is_a_lowering_error() {
    // 3^12 copies. Unbounded, depth 11 allocates a measured 1,259,124,078
    // bytes, so depth 12 needs some 3.8 GB; refused at a measured peak of
    // 70,012,150 bytes (67 MiB).
    assert_rejected_within_bytes(
        temporal_policy(&since_right(12)),
        "lower:",
        LOWERING_BUDGET,
        256 * MIB,
    );
}

#[test]
fn left_nested_since_lowers() {
    // The left of a `since` is copied once, so left nesting grows linearly.
    let lowered = lower(temporal_policy(&since_left(12))).expect("linear in n");
    assert!(leaves(&lowered).contains("__pin_ti"));
}

// ── The budget is the caller's ──────────────────────────────────────────

#[test]
fn a_small_budget_rejects_a_real_policy() {
    let src = temporal_policy(&format!("previous within 1h {READ}"));
    lower(src.clone()).expect("lowers at the default");
    let error = lower_with(src, ParseOptions::default().max_nodes(20)).expect_err("over 20");
    assert!(
        error.starts_with("lower:") && error.contains("lowering exceeds the node budget of 20"),
        "{error}"
    );
}

#[test]
fn a_small_budget_rejects_a_macro_expansion() {
    let error =
        lower_with(doubling_cedar(4), ParseOptions::default().max_nodes(20)).expect_err("over 20");
    assert!(
        error.contains("macro expansion exceeds the node budget of 20"),
        "{error}"
    );
}

#[test]
fn a_raised_budget_admits_what_the_default_refuses() {
    // Nested `previous` 8 deep needs more than 10,000 nodes and fewer than
    // the default.
    let src = temporal_policy(&previous(8));
    let error = lower_with(src.clone(), ParseOptions::default().max_nodes(10_000))
        .expect_err("over 10,000");
    assert!(error.contains("node budget of 10000"), "{error}");
    let raised = lower_with(
        src.clone(),
        ParseOptions::default().max_nodes(DEFAULT_MAX_NODES),
    )
    .expect("admitted when raised");
    let unbounded =
        lower_with(src, ParseOptions::default().max_nodes(usize::MAX)).expect("admitted unbounded");
    assert_eq!(leaves(&raised), leaves(&unbounded));
}

#[test]
fn lower_many_keeps_each_sets_budget() {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema");
    let service = ServiceSchema::defaults();
    let src = temporal_policy(&previous(8));
    let tight =
        ParsedPolicySet::parse_with(&src, &service, &ParseOptions::default().max_nodes(10_000))
            .expect("parses");
    let roomy = ParsedPolicySet::parse(&src, &service).expect("parses");
    let a: dogwood_language::Distincter = "a".parse().expect("distincter");
    let b: dogwood_language::Distincter = "b".parse().expect("distincter");
    dogwood_language::lower_many(&[(&roomy, a.clone())], &schema).expect("default budget");
    let error = dogwood_language::lower_many(&[(&roomy, a), (&tight, b)], &schema)
        .expect_err("the tight set keeps its budget");
    assert!(
        error.to_string().contains("node budget of 10000"),
        "{error}"
    );
}

// ── In-budget output is unchanged ───────────────────────────────────────

/// Lower `src` against `schema` at the default budget and with no budget, and
/// require identical Cedar, schema, and leaves.
#[track_caller]
fn assert_identical(src: &str, schema: &str) {
    let schema = PolicySchema::from_cedarschema_str(schema).expect("schema");
    let service = ServiceSchema::defaults();
    let render = |options: ParseOptions| {
        let lowered = ParsedPolicySet::parse_with(src, &service, &options)
            .and_then(|p| p.lower(&schema))
            .expect("lowers");
        (
            lowered.as_cedar().to_string(),
            lowered.cedar_schema_str().expect("schema text"),
            leaves(&lowered),
            format!(
                "{:?}",
                lowered.nonrelativized_temporal_fields().collect::<Vec<_>>()
            ),
        )
    };
    let bounded = render(ParseOptions::default());
    let unbounded = render(ParseOptions::default().max_nodes(usize::MAX));
    assert_eq!(bounded, unbounded);
}

#[test]
fn corpus_policies_lower_identically_under_the_default_budget() {
    let corpus = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing");
    for case in [
        "temporal_only/corpus/0746_parens_around_top_conjuncts_individually",
        "temporal_only/corpus/0302_since_dimension_gaps",
        "macros/corpus/0036_semver_rfc0061",
        "macros/corpus/0022_condition_macro_with_body_arg",
        "macros/corpus/mcagg_0294_count_containing_since",
        "mixed/corpus/0012_all_three_multi_action",
    ] {
        let dir = corpus.join(case);
        let schema = std::fs::read_to_string(dir.join("schema.cedarschema")).expect(case);
        let mut found = 0;
        for entry in std::fs::read_dir(&dir).expect(case) {
            let path = entry.expect("entry").path();
            if path.extension().is_some_and(|ext| ext == "dw") {
                let src = std::fs::read_to_string(&path).expect("policy");
                assert_identical(&src, &schema);
                found += 1;
            }
        }
        assert!(found > 0, "no policies in {case}");
    }
    assert_identical(&temporal_policy(&since_right(3)), SCHEMA);
    assert_identical(&temporal_policy(&previous(4)), SCHEMA);
}

#[test]
fn the_backstop_refuses_a_large_lowered_expression() {
    // No macro and no temporal block: only the final size check sees this.
    let src = policy("[1, 2, 3, 4, 5, 6].contains(1)");
    lower(src.clone()).expect("lowers at the default");
    let error = lower_with(src, ParseOptions::default().max_nodes(5)).expect_err("over 5");
    assert!(
        error.starts_with("lower:") && error.contains("lowering exceeds the node budget of 5"),
        "{error}"
    );
}

// ── One budget per set ──────────────────────────────────────────────────

/// One policy with `clauses` `when` clauses, each `clause`.
fn many_clauses(clauses: usize, clause: &str) -> String {
    let whens = vec![format!("when {{ {clause} }}"); clauses].join(" ");
    format!("@id(\"p\") permit {SCOPE} {whens};")
}

#[test]
fn many_small_macro_bombs_in_one_set_are_a_macro_error() {
    // `d(` nested 12 deep is about 2^13 nodes: alone it fits the default
    // budget, but 200 of them in one policy share one budget and exceed it.
    let clause = nest(12, "context.flag", |b| format!("d({b})"));
    let def = "def cedar d(?x) { ?x && ?x };\n";
    let one = format!("{def}{}", many_clauses(1, &clause));
    on_small_stack(move || ParsedPolicySet::parse(&one, &ServiceSchema::defaults()).map(drop))
        .expect("one clause fits the default budget");
    // Unbounded, the 200 clauses allocate a measured 1,317,701,853 bytes
    // (1.2 GiB); refused at a measured peak of 82,108,102 bytes (78 MiB).
    assert_rejected_within_bytes(
        format!("{def}{}", many_clauses(200, &clause)),
        "macro:",
        MACRO_BUDGET,
        320 * MIB,
    );
}

#[test]
fn the_same_clauses_in_separate_sets_each_get_a_budget() {
    // The budget is per set, with no total across sets: 200 sets of one
    // clause each lower although one set of 200 clauses does not.
    let clause = nest(12, "context.flag", |b| format!("d({b})"));
    let src = format!("def cedar d(?x) {{ ?x && ?x }};\n{}", policy(&clause));
    on_small_stack(move || {
        let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema");
        let entries: Vec<(&str, dogwood_language::Distincter)> = (0..200)
            .map(|i| (src.as_str(), format!("s{i}").parse().expect("distincter")))
            .collect();
        LoweredPolicySet::from_many_str(&entries, &ServiceSchema::defaults(), &schema).map(drop)
    })
    .expect("each set has its own budget");
}

/// The smallest node budget under which `src` parses and lowers against
/// [`SCHEMA`], found by bisection.
fn least_budget(src: &str) -> usize {
    let (mut lo, mut hi) = (0, DEFAULT_MAX_NODES);
    assert!(lower_with(src.to_string(), ParseOptions::default().max_nodes(hi)).is_ok());
    while lo + 1 < hi {
        let mid = lo + (hi - lo) / 2;
        match lower_with(src.to_string(), ParseOptions::default().max_nodes(mid)) {
            Ok(_) => hi = mid,
            Err(_) => lo = mid,
        }
    }
    hi
}

#[test]
fn a_sets_macro_expansions_share_one_budget() {
    let clause = nest(3, "context.flag", |b| format!("d({b})"));
    let def = "def cedar d(?x) { ?x && ?x };\n";
    let one = format!("{def}{}", many_clauses(1, &clause));
    let two = format!("{def}{}", many_clauses(2, &clause));
    let need = least_budget(&one);
    let error = lower_with(two.clone(), ParseOptions::default().max_nodes(need))
        .expect_err("two clauses need more than one");
    assert!(
        error.starts_with("macro:")
            && error.contains(&format!(
                "macro expansion exceeds the node budget of {need}"
            )),
        "{error}"
    );
    lower_with(two, ParseOptions::default().max_nodes(2 * need)).expect("twice fits two");
}

#[test]
fn a_sets_temporal_leaves_share_one_budget() {
    let clause = format!("temporal {{ {} }}", previous(3));
    let one = many_clauses(1, &clause);
    let two = many_clauses(2, &clause);
    let need = least_budget(&one);
    let error = lower_with(two.clone(), ParseOptions::default().max_nodes(need))
        .expect_err("two leaves need more than one");
    assert!(
        error.starts_with("lower:")
            && error.contains(&format!("lowering exceeds the node budget of {need}")),
        "{error}"
    );
    lower_with(two, ParseOptions::default().max_nodes(2 * need)).expect("twice fits two");
}

#[test]
fn the_budget_error_is_at_the_leaf_that_exhausted_it() {
    // The first leaf fits; the second exhausts the set's budget, and the
    // error points at it, not at the first.
    let first = format!("temporal {{ {} }}", previous(3));
    let second = format!("temporal {{ {} }}", previous(4));
    let src = format!("@id(\"p\") permit {SCOPE} when {{ {first} }} when {{ {second} }};");
    let need = least_budget(&many_clauses(1, &first));
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema");
    let error = ParsedPolicySet::parse_with(
        &src,
        &ServiceSchema::defaults(),
        &ParseOptions::default().max_nodes(need + 1),
    )
    .expect("parses")
    .lower(&schema)
    .expect_err("the second leaf exhausts the budget");
    assert!(matches!(error, Error::Cedarify(_)), "{error}");
    let label = miette::Diagnostic::labels(&error)
        .and_then(|mut labels| labels.next())
        .expect("located");
    let second_at = src.rfind("temporal {").expect("second leaf");
    assert!(
        label.offset() >= second_at,
        "error at {label:?}, before the second leaf at {second_at}: {error}"
    );
}

// ── The corpus fits the default ─────────────────────────────────────────

#[test]
fn the_largest_corpus_set_lowers_identically_at_the_default() {
    // The largest `.dw` set in the passing corpus whose case needs no
    // providers, lowered under its own event schema, if it has one.
    let corpus = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passing");
    let mut largest: Option<(u64, std::path::PathBuf)> = None;
    let mut stack = vec![corpus];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).expect("dir") {
            let path = entry.expect("entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|ext| ext == "dw")
                && dir.join("schema.cedarschema").exists()
                && !dir.join("providers.json").exists()
            {
                let len = path.metadata().expect("metadata").len();
                if largest.as_ref().is_none_or(|(l, _)| len > *l) {
                    largest = Some((len, path));
                }
            }
        }
    }
    let (_, path) = largest.expect("a corpus policy");
    let dir = path.parent().expect("case dir");
    let src = std::fs::read_to_string(&path).expect("policy");
    let schema = std::fs::read_to_string(dir.join("schema.cedarschema")).expect("schema");
    let schema = PolicySchema::from_cedarschema_str(&schema).expect("schema");
    let mut service = ServiceSchema::builder();
    if let Ok(events) = std::fs::read_to_string(dir.join("event.dwschema")) {
        service = service.event_schema_str(&events);
    }
    let service = service.build().expect("service schema");
    let render = |options: ParseOptions| {
        let lowered = ParsedPolicySet::parse_with(&src, &service, &options)
            .and_then(|p| p.lower(&schema))
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        (lowered.as_cedar().to_string(), leaves(&lowered))
    };
    assert_eq!(
        render(ParseOptions::default()),
        render(ParseOptions::default().max_nodes(usize::MAX))
    );
}
