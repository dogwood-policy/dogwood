//! Per-construct unit gates for [`ParsedPolicy::expanded_source`].
//!
//! The sibling suite `expanded_source_roundtrip.rs` runs the renderer over the
//! whole embedded corpus: exhaustive, but all-or-nothing. When the renderer is
//! half-built it reports "N cases failed", not *which surface construct* the
//! offending render arm belongs to. These tests are the complementary layer —
//! tiny, hand-authored policies that each exercise **one** construct, so a red
//! test points straight at the arm to fix, and the loop stays tight
//! construct-by-construct.
//!
//! They are also cheaper to run: hand-written, so no `corpus` feature and no
//! ~13MB of embedded data — plain `cargo test --test expanded_source_units`.
//!
//! # What each case asserts
//!
//! The contract is semantic, not textual (formatting/comments are not
//! preserved), so every case checks:
//!
//! - **Re-lower (L0):** the rendered form parses and lowers without error.
//! - **Idempotence:** rendering the rendered form again is byte-identical — a
//!   stable fixed point, so no arm emits something it cannot itself re-consume.
//! - **Decision equivalence (L2):** the rendered form decides identically to
//!   the original at every timepoint of a small trace. This is the format-
//!   insensitive correctness bar.
//!
//! For the Cedar surface constructs we know Cedar's semantics exactly, so each
//! case *also* pins the absolute decision and picks operands so an operator
//! swap flips it (e.g. `amount == 5` Permits but a swap to `!=` Denies) — a
//! silent semantic drift a bare equivalence check could miss. For the temporal
//! constructs (whose exact per-operator truth over a trace is the corpus gate's
//! job) each case instead requires the original to Permit *somewhere* on the
//! trace, so the construct provably fires and a bug that flattens it is caught
//! by the stream comparison.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, ParsedPolicySet, PolicySchema, ProviderDeclarations,
    ServiceSchema, parse_trace,
};

// ─── shared schema / event schema ────────────────────────────────────────

/// One namespace, one context shape, three actions. `Info` carries a field of
/// every scalar family a construct might touch (a `Long`, a `String`, a `Bool`,
/// a `Set`, and one optional field for `has`); the principal is a `User` that
/// declares an attribute and a group membership, so `is` / `in` / attribute
/// access all have something to bind against.
const SCHEMA: &str = r#"namespace T {
  type Info = {
    user:   String,
    amount: Long,
    tag:    String,
    flag:   Bool,
    tags:   Set<String>,
    note?:  String
  };

  entity Team;
  entity User in [Team] = { id: String, dept: String };
  entity Doc;

  action "Login" appliesTo {
    principal: [User], resource: [Doc], context: { input: Info }
  };
  action "Read" appliesTo {
    principal: [User], resource: [Doc], context: { input: Info }
  };
  action "Write" appliesTo {
    principal: [User], resource: [Doc], context: { input: Info }
  };
}"#;

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

// ─── harness ──────────────────────────────────────────────────────────────

/// The default service (event schema only, no macros/providers) — the common
/// case, and the *macro-free* service the no-residue check re-lowers against.
fn service() -> ServiceSchema {
    ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("service schema builds")
}

fn schema() -> PolicySchema {
    PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds")
}

/// One trace event: a decision-point `<action>::request` for `user`, carrying a
/// fixed context (`amount`, `tag = "gold"`, `flag = true`, `tags = ["a","b"]`)
/// and a principal that is a member of `T::Team::"tm"` and declares `dept`.
fn ev(ts: i64, action: &str, user: &str, amount: i64) -> String {
    format!(
        "@{ts} scope(principal: T::User::\"{user}\", resource: T::Doc::\"d1\") \
         entities(T::User::\"{user}\": {{ id: \"{user}\", dept: \"eng\" }} in [T::Team::\"tm\"]) \
         request_context(input: {{ user: \"{user}\", amount: {amount}, tag: \"gold\", \
         flag: true, tags: [\"a\", \"b\"] }}) \
         T::Action::\"{action}\"::request(input: {{ user: \"{user}\", amount: {amount}, \
         tag: \"gold\", flag: true, tags: [\"a\", \"b\"] }}, callerPrincipal: T::User::\"{user}\", \
         callerResource: T::Doc::\"d1\", requestId: \"r{ts}\")"
    )
}

/// A single `Read` request — enough for a stateless Cedar clause.
fn cedar_trace() -> String {
    ev(0, "Read", "alice", 5)
}

/// A short history ending in a `Read`, so `formerly`/`since`/`count` over the
/// window have prior `Login`s to see when the `Read` is decided.
fn temporal_trace() -> String {
    [
        ev(0, "Login", "alice", 5),
        ev(5, "Login", "alice", 5),
        ev(10, "Read", "alice", 5),
        ev(20, "Write", "alice", 5),
    ]
    .join("\n")
}

/// Render every policy in `src` (parsed against `svc`) back to its expanded
/// source, concatenated — the form a per-policy store would keep and re-lower.
fn expanded_document(src: &str, svc: &ServiceSchema) -> String {
    let parsed = ParsedPolicySet::parse(src, svc).expect("source parses");
    parsed
        .policies()
        .map(|p| p.expanded_source())
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// The per-timepoint decision stream `doc` produces over `trace`.
fn decisions(doc: &str, svc: &ServiceSchema, trace: &str) -> Vec<Option<Decision>> {
    let lowered = LoweredPolicySet::from_str(doc, svc, &schema()).expect("document lowers");
    let events = parse_trace(trace).expect("trace parses");
    let mut authorizer = Authorizer::new(lowered);
    events
        .iter()
        .map(|e| authorizer.is_authorized(e).map(|r| r.decision()))
        .collect()
}

/// The core round-trip assertion, shared by every case.
///
/// `svc_orig` parses/renders the original (it holds any macros the source
/// references); `svc_relower` re-lowers and decides the rendered form (the
/// macro-free service for the residue check, else the same service).
fn assert_roundtrip(
    label: &str,
    svc_orig: &ServiceSchema,
    svc_relower: &ServiceSchema,
    policy: &str,
    trace: &str,
) {
    let orig = decisions(policy, svc_orig, trace);

    let rendered = expanded_document(policy, svc_orig);

    // L0 — the rendered form must re-lower (against the macro-free service for
    // macro cases: a surviving macro reference would fail here).
    assert!(
        LoweredPolicySet::from_str(&rendered, svc_relower, &schema()).is_ok(),
        "[{label}] rendered form does not re-lower:\n{rendered}"
    );

    // Idempotence — rendering the rendered form changes nothing.
    let twice = expanded_document(&rendered, svc_orig);
    assert_eq!(
        rendered, twice,
        "[{label}] expanded_source is not idempotent:\n--- once ---\n{rendered}\n--- twice ---\n{twice}"
    );

    // L2 — identical decisions at every timepoint.
    let got = decisions(&rendered, svc_relower, trace);
    assert_eq!(
        got, orig,
        "[{label}] rendered decision stream differs from original:\n{rendered}"
    );
}

/// A Cedar-surface case: the shared service, the single `Read` trace, and an
/// exact expected decision (chosen so an operator swap would flip it).
fn cedar_case(label: &str, policy: &str, expect: Decision) {
    let svc = service();
    let last = decisions(policy, &svc, &cedar_trace())
        .into_iter()
        .flatten()
        .last();
    assert_eq!(
        last,
        Some(expect),
        "[{label}] original decision is not the expected {expect:?} \
         (trace not discriminating / body wrong):\n{policy}"
    );
    assert_roundtrip(label, &svc, &svc, policy, &cedar_trace());
}

/// A temporal case: the shared service and the history trace. The exact
/// per-timepoint truth is the corpus gate's job; here we only require the
/// original to Permit *somewhere*, so the construct provably fires.
fn temporal_case(label: &str, policy: &str) {
    let svc = service();
    let stream = decisions(policy, &svc, &temporal_trace());
    assert!(
        stream.iter().flatten().any(|d| *d == Decision::Allow),
        "[{label}] original never Permits on the trace — construct did not fire, \
         so the round-trip would not be discriminating:\n{policy}"
    );
    assert_roundtrip(label, &svc, &svc, policy, &temporal_trace());
}

/// Wrap a Cedar `when` body in a `permit … action == Read` rule.
fn cedar_when(body: &str) -> String {
    format!("permit (principal, action == T::Action::\"Read\", resource)\nwhen {{ {body} }};")
}

/// Wrap a temporal body in a `permit … action == Read` rule.
fn temporal_when(body: &str) -> String {
    format!(
        "permit (principal, action == T::Action::\"Read\", resource)\nwhen temporal {{ {body} }};"
    )
}

// ══════════════════════════════════════════════════════════════════════════
// Cedar surface — scope / effect / clauses
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn effect_forbid() {
    // A forbid over the same scope denies the matching request.
    cedar_case(
        "forbid",
        "forbid (principal, action == T::Action::\"Read\", resource)\nwhen { true };",
        Decision::Deny,
    );
}

#[test]
fn scope_action_in_set() {
    cedar_case(
        "scope-action-in",
        "permit (principal, action in [T::Action::\"Read\", T::Action::\"Write\"], resource)\nwhen { true };",
        Decision::Allow,
    );
}

#[test]
fn scope_principal_is_and_resource_eq() {
    cedar_case(
        "scope-is-eq",
        "permit (principal is T::User, action == T::Action::\"Read\", resource == T::Doc::\"d1\")\nwhen { true };",
        Decision::Allow,
    );
}

#[test]
fn annotations_are_carried() {
    // An @id annotation is metadata; it must survive the round-trip.
    cedar_case(
        "annotation",
        "@id(\"rule-a\")\npermit (principal, action == T::Action::\"Read\", resource)\nwhen { true };",
        Decision::Allow,
    );
}

#[test]
fn clause_when_and_unless() {
    // A rule fires only when every `when` holds and every `unless` fails.
    cedar_case(
        "when-unless",
        "permit (principal, action == T::Action::\"Read\", resource)\n\
         when { context.input.amount == 5 }\nunless { context.input.tag == \"blocked\" };",
        Decision::Allow,
    );
}

// ══════════════════════════════════════════════════════════════════════════
// Cedar surface — expression constructs (one arm each)
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn comparison_operators() {
    // amount == 5, so each op below is TRUE and any swap to its opposite flips
    // the decision to Deny.
    for (op, rhs) in [
        ("==", 5),
        ("!=", 3),
        ("<", 10),
        ("<=", 5),
        (">", 3),
        (">=", 5),
    ] {
        cedar_case(
            &format!("cmp {op}"),
            &cedar_when(&format!("context.input.amount {op} {rhs}")),
            Decision::Allow,
        );
    }
}

#[test]
fn arithmetic_operators() {
    // amount == 5; each result is chosen TRUE so a swapped operator flips it.
    for (expr, rhs) in [
        ("context.input.amount + 1", 6),
        ("context.input.amount - 2", 3),
        ("context.input.amount * 2", 10),
    ] {
        cedar_case(
            &format!("arith {expr}"),
            &cedar_when(&format!("{expr} == {rhs}")),
            Decision::Allow,
        );
    }
}

#[test]
fn boolean_and() {
    // false && true = false; rendered as `||` it would be true → Deny discriminates.
    cedar_case(
        "and",
        &cedar_when("context.input.amount > 100 && context.input.flag"),
        Decision::Deny,
    );
}

#[test]
fn boolean_or() {
    // false || true = true; rendered as `&&` it would be false → Permit discriminates.
    cedar_case(
        "or",
        &cedar_when("context.input.amount > 100 || context.input.flag"),
        Decision::Allow,
    );
}

#[test]
fn boolean_not() {
    // !(false) = true; a dropped `!` → Deny discriminates.
    cedar_case(
        "not",
        &cedar_when("!(context.input.amount > 100)"),
        Decision::Allow,
    );
}

#[test]
fn has_attribute() {
    cedar_case("has", &cedar_when("context.input has tag"), Decision::Allow);
}

#[test]
fn like_pattern() {
    // "gold" like "go*" is true; a mangled pattern → Deny discriminates.
    cedar_case(
        "like",
        &cedar_when("context.input.tag like \"go*\""),
        Decision::Allow,
    );
}

#[test]
fn is_entity_type() {
    cedar_case("is", &cedar_when("principal is T::User"), Decision::Allow);
}

#[test]
fn in_entity_hierarchy() {
    cedar_case(
        "in",
        &cedar_when("principal in T::Team::\"tm\""),
        Decision::Allow,
    );
}

#[test]
fn get_attr_on_entity() {
    cedar_case(
        "get-attr",
        &cedar_when("principal.dept == \"eng\""),
        Decision::Allow,
    );
}

#[test]
fn if_then_else() {
    cedar_case(
        "if",
        &cedar_when("if context.input.flag then context.input.amount == 5 else false"),
        Decision::Allow,
    );
}

#[test]
fn set_literal_and_method_call() {
    // A set literal plus a `.contains(…)` method call; 5 ∈ {3,5,7}.
    cedar_case(
        "set+method",
        &cedar_when("[3, 5, 7].contains(context.input.amount)"),
        Decision::Allow,
    );
}

#[test]
fn record_literal_and_get_attr() {
    cedar_case(
        "record",
        &cedar_when("{ v: context.input.amount, w: 1 }.v == 5"),
        Decision::Allow,
    );
}

#[test]
fn extension_decimal() {
    // A `decimal(…)` extension call, compared for equality.
    cedar_case(
        "extension-decimal",
        &cedar_when("decimal(\"2.5\") == decimal(\"2.5\")"),
        Decision::Allow,
    );
}

// ══════════════════════════════════════════════════════════════════════════
// Temporal surface — one construct each
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn temporal_formerly() {
    temporal_case(
        "formerly",
        &temporal_when(
            "formerly within 1h T::Action::\"Login\"::request{ input.user: context.input.user }",
        ),
    );
}

#[test]
fn temporal_previous() {
    temporal_case(
        "previous",
        &temporal_when(
            "previous within 1h T::Action::\"Login\"::request{ input.user: context.input.user }",
        ),
    );
}

#[test]
fn temporal_since() {
    // `A since within w B`: `B` (a prior Login) held in the window and `A` (a
    // scalar comparison, true at every timepoint) has held since.
    temporal_case(
        "since",
        &temporal_when(
            "context.input.amount >= 0 \
             since within 1h T::Action::\"Login\"::request{ input.user: context.input.user }",
        ),
    );
}

#[test]
fn temporal_and_with_comparison() {
    // `And` of a `formerly` predicate with a scalar `Comparison`.
    temporal_case(
        "temporal-and-cmp",
        &temporal_when(
            "formerly within 1h T::Action::\"Login\"::request{ input.user: context.input.user } \
             && context.input.amount > 0",
        ),
    );
}

#[test]
fn temporal_not() {
    // No prior `Write`, so `!(formerly … Write)` holds.
    temporal_case(
        "temporal-not",
        &temporal_when(
            "!(formerly within 1h T::Action::\"Write\"::request{ input.user: context.input.user })",
        ),
    );
}

#[test]
fn temporal_exists_count_tp() {
    // `exists` binder + `count for (Timepoint)` aggregation + `tp($t)` +
    // `Comparison` — several temporal arms in one small policy.
    temporal_case(
        "exists-count-tp",
        &temporal_when(
            "exists (d: Long). ( \
               (count for (t: Timepoint). where ( \
                  formerly within 1h ( \
                     T::Action::\"Login\"::request{ input.user: context.input.user } && tp(t)))) == d \
               && d > 0 )",
        ),
    );
}

#[test]
fn temporal_sum() {
    // `sum` aggregation binding a numeric event field over the window.
    temporal_case(
        "sum",
        &temporal_when(
            "exists (s: Long). ( \
               (sum a for (a: Long), (t: Timepoint). where ( \
                  formerly within 1h ( \
                     T::Action::\"Login\"::request{ input.user: context.input.user, input.amount: a } && tp(t)))) == s \
               && s > 0 )",
        ),
    );
}

// ══════════════════════════════════════════════════════════════════════════
// Macro inlining — the expanded form must carry no macro residue
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn macro_def_cedar_is_inlined() {
    // The `def cedar` is top-level, not part of the policy; the rendered
    // per-policy form must inline the call and re-lower with no macro named.
    let svc = service();
    let policy = "def cedar amount_is(?n) { context.input.amount == ?n };\n\
                  permit (principal, action == T::Action::\"Read\", resource)\n\
                  when { amount_is(5) };";
    // Sanity: it Permits (amount == 5) before we check the round-trip.
    let last = decisions(policy, &svc, &cedar_trace())
        .into_iter()
        .flatten()
        .last();
    assert_eq!(
        last,
        Some(Decision::Allow),
        "def-cedar policy should Permit"
    );
    assert_roundtrip("macro-def-cedar", &svc, &svc, policy, &cedar_trace());
}

#[test]
fn macro_def_temporal_is_inlined() {
    let policy = "def temporal recent_login(?u) { \
                    formerly within 1h T::Action::\"Login\"::request{ input.user: ?u } };\n\
                  permit (principal, action == T::Action::\"Read\", resource)\n\
                  when temporal { recent_login(context.input.user) };";
    temporal_case("macro-def-temporal", policy);
}

// ══════════════════════════════════════════════════════════════════════════
// Escaping / non-identifier edge cases (each pins a distinct rendering path)
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn get_attr_non_identifier_uses_index_form() {
    // A non-identifier attribute cannot follow `.` (dot access requires an
    // identifier); it must render as index syntax `["a b"]`, which re-parses to
    // the same `GetAttr`. A record literal with a space-bearing key exercises
    // both the record-key and the index-key rendering paths.
    cedar_case(
        "get-attr-index",
        &cedar_when("{ \"a b\": 5 }[\"a b\"] == 5"),
        Decision::Allow,
    );
}

#[test]
fn annotation_value_with_backslash_roundtrips() {
    // Annotation values are decoded with Cedar's unescaper, so a literal
    // backslash is written escaped (`\\`, which decodes to one `\`) and must be
    // re-encoded as `\\` on render — otherwise the value changes and rendering
    // is not idempotent.
    cedar_case(
        "annotation-backslash",
        "@note(\"a\\\\b\")\npermit (principal, action == T::Action::\"Read\", resource)\nwhen { true };",
        Decision::Allow,
    );
}

#[test]
fn temporal_string_with_backslash_roundtrips() {
    // The temporal string decoder now unescapes with Cedar's rules, so a literal
    // backslash is written escaped (`\\`) and must be re-encoded as `\\` on
    // render; re-parsing the rendered form must recover the same value. No
    // matching event is needed — `assert_roundtrip`'s re-lower + idempotence +
    // decision-equivalence checks catch any corruption.
    let svc = service();
    let policy =
        temporal_when("formerly within 1h T::Action::\"Login\"::request{ input.user: \"a\\\\b\" }");
    assert_roundtrip("temporal-backslash", &svc, &svc, &policy, &temporal_trace());
}

#[test]
fn like_pattern_with_quote_roundtrips() {
    // A `like` pattern containing a `"` must stay escaped through the render →
    // re-parse cycle (the pattern is decoded on parse and re-encoded on render).
    // No match is needed; re-lower + idempotence carry the check.
    let svc = service();
    let policy = cedar_when("context.input.tag like \"go\\\"*\"");
    assert_roundtrip("like-quote", &svc, &svc, &policy, &cedar_trace());
}

// ══════════════════════════════════════════════════════════════════════════
// Additional operator / scope coverage (method-form ops, neg, scope IsIn)
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn decimal_comparison_method() {
    // `.lessThan(…)` (a method-form `BinOp`); 2.5 < 3.0, so a swap to
    // `greaterThan` flips it.
    cedar_case(
        "decimal-lessThan",
        &cedar_when("decimal(\"2.5\").lessThan(decimal(\"3.0\"))"),
        Decision::Allow,
    );
}

#[test]
fn set_contains_all_and_any() {
    cedar_case(
        "containsAll",
        &cedar_when("[1, 2, 3].containsAll([1, 2])"),
        Decision::Allow,
    );
    cedar_case(
        "containsAny",
        &cedar_when("[1, 2].containsAny([2, 9])"),
        Decision::Allow,
    );
}

#[test]
fn unary_negation() {
    // `-e` (prefix `Neg`); -5 == -5, so dropping the negation flips it.
    cedar_case(
        "neg",
        &cedar_when("-context.input.amount == -5"),
        Decision::Allow,
    );
}

#[test]
fn scope_principal_is_in_group() {
    // The `principal is T in <uid>` scope form (`IsIn`). alice is a `User` and a
    // member of `T::Team::"tm"`.
    cedar_case(
        "scope-is-in",
        "permit (principal is T::User in T::Team::\"tm\", action == T::Action::\"Read\", resource)\nwhen { true };",
        Decision::Allow,
    );
}

// ══════════════════════════════════════════════════════════════════════════
// Provider invocation — a plain `Ns::Fn(...)` call plus attribute access
// ══════════════════════════════════════════════════════════════════════════

/// A pure (hermetic) provider returning `{ value: <arg> }`, so a decision can be
/// driven with no network or `net` feature.
const PROVIDERS: &str = r#"{
  "availableProviders": {
    "Ext::Score": {
      "argumentTypes": [ { "paramType": "long" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "value": { "paramType": "long" } },
        "required": ["value"]
      },
      "implementation": { "kind": "rhai", "script": "fn evaluate(x) { #{ value: x } }" }
    }
  }
}"#;

fn provider_service() -> ServiceSchema {
    ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .providers(ProviderDeclarations::from_json(PROVIDERS).expect("providers parse"))
        .build()
        .expect("service schema builds")
}

#[test]
fn provider_invocation_call_and_attr() {
    // `Ext::Score(context.input.amount).value > 3` — an `ExprKind::Call`
    // (the provider invocation) whose result is projected and compared.
    // Score(5) = { value: 5 }, so 5 > 3 permits; the declaration is needed both
    // to render and to re-lower, so the same service is used on both sides.
    let svc = provider_service();
    let policy = &cedar_when("Ext::Score(context.input.amount).value > 3");
    let last = decisions(policy, &svc, &cedar_trace())
        .into_iter()
        .flatten()
        .last();
    assert_eq!(last, Some(Decision::Allow), "provider policy should Permit");
    assert_roundtrip("provider-call", &svc, &svc, policy, &cedar_trace());
}

// ══════════════════════════════════════════════════════════════════════════
// Adversarial leaf matrix — a battery of nasty string values at every leaf
// position, driven by the self-validating round-trip oracles (re-lower +
// idempotence + decision-equivalence). This is the layer that catches lexical-
// corner bugs the per-construct cases and the (curated) corpus miss: an
// attribute name with a space, a backslash inside a temporal/annotation value,
// etc. Each distinct rendering path is represented — Cedar `Display`, the
// `quote` (Cedar-decoded) path used for record/index keys, annotation values,
// and temporal terms, and `like`.
// ══════════════════════════════════════════════════════════════════════════

/// Values legal in a **Cedar-decoded** string position (they survive escape →
/// decode). Every string-valued position now decodes — Cedar literals, record /
/// index keys, `like` patterns, annotation values, and temporal terms — so
/// `quote`/`Display`/`Pattern` must round-trip each.
const NASTY_DECODED: &[&str] = &[
    "", " ", "a b", "o'brien", "a\\b", "a\"b", "a\tb", "café", "π", "1x", "is",
];

/// Cedar decodes strings with the **Rust** escaper (`rustc_literal_escaper`), so
/// these are all valid *source* escapes: `\x41` (hex byte, ≤ 0x7F) and `\u{…}`
/// with underscore digit separators, astral, and control code points. Each is
/// the raw text placed *between the quotes* in `.dw` source. Every string
/// position decodes, so the renderer must round-trip the decoded code point
/// (choosing its own escape form). These forms have historically tripped up
/// naive escapers, so they get their own pass.
const ESCAPE_FORMS: &[(&str, &str)] = &[
    ("hex-A", "\\x41"),                  // → 'A'
    ("hex-del", "\\x7f"),                // → U+007F (DEL, control)
    ("uni-underscores", "\\u{1_2_3_4}"), // → U+1234
    ("uni-astral", "\\u{1F512}"),        // → U+1F512 (🔒)
    ("uni-control", "\\u{7f}"),          // → U+007F (DEL)
    ("uni-null", "\\u{0}"),              // → U+0000 (NUL)
];

/// Escape `v` into the inner text of a Cedar-decoded string literal (matches the
/// crate-private renderer's `quote`), so `"<dw_escape(v)>"` decodes back to `v`.
fn dw_escape(v: &str) -> String {
    let mut s = String::new();
    for c in v.chars() {
        match c {
            '"' => s.push_str("\\\""),
            '\\' => s.push_str("\\\\"),
            '\n' => s.push_str("\\n"),
            '\r' => s.push_str("\\r"),
            '\t' => s.push_str("\\t"),
            c if c.is_control() => s.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => s.push(c),
        }
    }
    s
}

/// Run the round-trip check on `policy` **iff** it parses and lowers — the
/// renderer's contract is to round-trip a valid policy, not to make an invalid
/// one lower, so an input illegal in a given position is skipped, not failed.
/// Returns whether the case actually ran (for the vacuity floor).
fn matrix_case(label: &str, svc: &ServiceSchema, policy: &str, trace: &str) -> bool {
    if LoweredPolicySet::from_str(policy, svc, &schema()).is_err() {
        return false;
    }
    assert_roundtrip(label, svc, svc, policy, trace);
    true
}

#[test]
fn adversarial_leaf_matrix() {
    let svc = service();
    let ct = cedar_trace();
    let tt = temporal_trace();
    let mut ran = 0usize;

    for v in NASTY_DECODED {
        let e = dw_escape(v);
        // Cedar string literal — rendered via Cedar `Display`.
        ran += matrix_case(
            &format!("cedar-string[{v:?}]"),
            &svc,
            &cedar_when(&format!("context.input.tag == \"{e}\"")),
            &ct,
        ) as usize;
        // Entity id in scope — entity-uid `Display`.
        ran += matrix_case(
            &format!("scope-entity[{v:?}]"),
            &svc,
            &format!(
                "permit (principal == T::User::\"{e}\", action == T::Action::\"Read\", resource)\nwhen {{ true }};"
            ),
            &ct,
        ) as usize;
        // Record key + index access — the `quote` path (member and index key).
        ran += matrix_case(
            &format!("record-index[{v:?}]"),
            &svc,
            &cedar_when(&format!("{{ \"{e}\": 1 }}[\"{e}\"] == 1")),
            &ct,
        ) as usize;
        // `like` pattern — Cedar `Pattern` Display / build_pattern decode.
        ran += matrix_case(
            &format!("like[{v:?}]"),
            &svc,
            &cedar_when(&format!("context.input.tag like \"{e}\"")),
            &ct,
        ) as usize;
        // Annotation value — decoded with Cedar's unescaper → the `quote` path.
        ran += matrix_case(
            &format!("annotation[{v:?}]"),
            &svc,
            &format!(
                "@note(\"{e}\")\npermit (principal, action == T::Action::\"Read\", resource)\nwhen {{ true }};"
            ),
            &ct,
        ) as usize;
        // Temporal predicate string arg — decoded with Cedar's unescaper → `quote`.
        ran += matrix_case(
            &format!("temporal-string[{v:?}]"),
            &svc,
            &temporal_when(&format!(
                "formerly within 1h T::Action::\"Login\"::request{{ input.user: \"{e}\" }}"
            )),
            &tt,
        ) as usize;
    }

    // Cedar / Rust escape forms — hex and underscore-separated / astral /
    // control unicode escapes, injected raw at each position.
    for (name, inner) in ESCAPE_FORMS {
        // Decoded positions — the escape decodes to a code point that must
        // round-trip through the renderer's own escape choice.
        ran += matrix_case(
            &format!("esc-cedar-string[{name}]"),
            &svc,
            &cedar_when(&format!("context.input.tag == \"{inner}\"")),
            &ct,
        ) as usize;
        ran += matrix_case(
            &format!("esc-record-index[{name}]"),
            &svc,
            &cedar_when(&format!("{{ \"{inner}\": 1 }}[\"{inner}\"] == 1")),
            &ct,
        ) as usize;
        ran += matrix_case(
            &format!("esc-like[{name}]"),
            &svc,
            &cedar_when(&format!("context.input.tag like \"{inner}\"")),
            &ct,
        ) as usize;
        // Annotation and temporal positions — decoded like the Cedar positions
        // above, so the escape decodes to a code point the renderer re-encodes.
        ran += matrix_case(
            &format!("esc-annotation[{name}]"),
            &svc,
            &format!(
                "@note(\"{inner}\")\npermit (principal, action == T::Action::\"Read\", resource)\nwhen {{ true }};"
            ),
            &ct,
        ) as usize;
        ran += matrix_case(
            &format!("esc-temporal[{name}]"),
            &svc,
            &temporal_when(&format!(
                "formerly within 1h T::Action::\"Login\"::request{{ input.user: \"{inner}\" }}"
            )),
            &tt,
        ) as usize;
    }

    // Vacuity floor: if a template were malformed, everything would skip and the
    // test would pass having checked nothing. The floor is above the count
    // reachable without the escape-form battery (66 = 11 values × 6 positions),
    // so it also guarantees those escape cases participate. All 96 combinations
    // currently run.
    assert!(
        ran >= 80,
        "adversarial matrix ran only {ran} cases — a template is likely malformed"
    );
}

// --- review round 2: characterizing tests (expected RED before the fix) ---

#[test]
fn has_keyword_attribute_roundtrips() {
    // `resource has "true"` — attribute name is a reserved keyword. It must
    // render quoted; bare `has true` is parsed as a boolean literal and rejected.
    let svc = service();
    let policy = cedar_when("resource has \"true\"");
    assert_roundtrip("has-true", &svc, &svc, &policy, &cedar_trace());
}

#[test]
fn record_key_keyword_roundtrips() {
    // A record key that is a reserved keyword must render quoted.
    cedar_case(
        "record-key-true",
        &cedar_when("{ \"true\": 1 }[\"true\"] == 1"),
        Decision::Allow,
    );
}
