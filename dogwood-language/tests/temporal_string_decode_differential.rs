//! **Invariant:** a Cedar string literal and the **same** literal in a temporal
//! clause denote the same value, so — matched against the same request field —
//! they must reach the same verdict.
//!
//! This suite **guards** that invariant. It once failed: Cedar decoded string
//! escapes (`\"`, `\n`, `\t`, `\\`, `\'`) via the Rust escaper, but the temporal
//! sub-language parser stripped the quotes *without* decoding, so an escape-
//! bearing literal meant a different string in a temporal clause than in a
//! Cedar clause — matched in Cedar, missed in temporal (fail-open for a temporal
//! `forbid`). The temporal parser now decodes via the same
//! `to_unescaped_string` the Cedar-clause path uses, so the two agree; a
//! regression to no-decode turns the escape-bearing cases red again.
//!
//! # Why the divergence was real (not cosmetic)
//!
//! Both clauses read the **same** field, `context.input.doc`, from the same
//! request — the trace parser decodes that field once, identically for both. So
//! the only variable is how each clause decodes its own literal, and a verdict
//! difference isolates the defect to literal decoding alone. For an escape-
//! bearing literal the Cedar clause matches (both sides decoded) and permits,
//! while the temporal clause compares the decoded field against its *un-decoded*
//! literal, fails to match, and denies. That temporal clause is often a
//! `forbid`/`unless` guard, so the silent non-match is **fail-open**.
//!
//! # Why the existing corpus never caught it
//!
//! The controls (`plain`, `bare-apostrophe`) need no decoding on either side (a
//! bare `'` is not an escape), so they agree and pass even now. The corpus's
//! single-quote cases are exactly this bare-apostrophe shape — which is why they
//! pass and the divergence went unseen. Only a literal with an actual backslash
//! escape exposes it.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ServiceSchema, parse_trace,
};

const SCHEMA: &str = r#"namespace T {
  type Info = { doc: String };
  entity User;
  entity Doc;
  action "Read" appliesTo { principal: [User], resource: [Doc], context: { input: Info } };
  action "Log"  appliesTo { principal: [User], resource: [Doc], context: { input: Info } };
}"#;

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

fn service() -> ServiceSchema {
    ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("service schema builds")
}
fn schema() -> PolicySchema {
    PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds")
}

/// One event; `doc_src` is placed verbatim between the quotes in the trace, so
/// the trace parser decodes the field exactly as it decodes a policy literal.
fn ev(ts: i64, action: &str, doc_src: &str) -> String {
    format!(
        "@{ts} scope(principal: T::User::\"u\", resource: T::Doc::\"d\") \
         request_context(input: {{ doc: \"{doc_src}\" }}) \
         T::Action::\"{action}\"::request(input: {{ doc: \"{doc_src}\" }}, \
         callerPrincipal: T::User::\"u\", callerResource: T::Doc::\"d\", requestId: \"r{ts}\")"
    )
}

/// The verdict at the final `Read` timepoint, over a `Log` then `Read` trace
/// whose `doc` field carries `doc_src` (same spelling as the policy literal).
fn verdict(policy: &str, doc_src: &str) -> Option<Decision> {
    let svc = service();
    let lowered = LoweredPolicySet::from_str(policy, &svc, &schema())
        .unwrap_or_else(|e| panic!("policy failed to lower:\n{policy}\n  -> {e:?}"));
    let trace = format!("{}\n{}", ev(0, "Log", doc_src), ev(10, "Read", doc_src));
    let mut auth = Authorizer::new(lowered);
    let mut last = None;
    for e in &parse_trace(&trace).expect("trace parses") {
        if let Some(r) = auth.is_authorized(e) {
            last = Some(r.decision());
        }
    }
    last
}

/// `permit … when { context.input.doc == "<lit>" }` — a plain Cedar clause.
fn cedar_policy(lit: &str) -> String {
    format!(
        "permit (principal, action == T::Action::\"Read\", resource)\n\
         when {{ context.input.doc == \"{lit}\" }};"
    )
}

/// The same equality, inside a `temporal { … }` clause.
fn temporal_policy(lit: &str) -> String {
    format!(
        "permit (principal, action == T::Action::\"Read\", resource)\n\
         when temporal {{ context.input.doc == \"{lit}\" }};"
    )
}

/// `(label, .dw-source inner text)`. Controls (no escape) already agree; the
/// escape-bearing literals are the ones that expose the bug.
const CASES: &[(&str, &str)] = &[
    // Controls — no escape, so both sides agree (this is the corpus's shape).
    ("plain", "obrien"),
    ("bare-apostrophe", "o'brien"),
    // Escape-bearing literals — Cedar decodes, temporal does not.
    ("escaped-quote", "o\\\"brien"),
    ("escaped-backslash", "a\\\\b"),
    ("newline", "a\\nb"),
    ("tab", "a\\tb"),
    ("escaped-apostrophe", "o\\'brien"),
];

/// The invariant: the same literal decides the same way in a Cedar clause and a
/// temporal clause. Currently **fails** (red) on the escape-bearing literals —
/// see the module docs; it is meant to stay red until the temporal parser
/// decodes string escapes like Cedar.
#[test]
fn same_string_literal_decides_the_same_in_cedar_and_temporal() {
    let mut divergences = Vec::new();
    for (label, lit) in CASES {
        let cedar = verdict(&cedar_policy(lit), lit);
        let temporal = verdict(&temporal_policy(lit), lit);
        if cedar != temporal {
            divergences.push(format!(
                "  [{label}] lit={lit:?}: cedar={cedar:?} but temporal={temporal:?}"
            ));
        }
    }
    assert!(
        divergences.is_empty(),
        "the same string literal decides differently in a Cedar vs a temporal \
         clause — the temporal parser does not decode escapes (fix the parser, \
         not this test):\n{}",
        divergences.join("\n")
    );
}

/// The strictness half of the fix: an *invalid* escape in a temporal literal is
/// rejected at parse. `validate_string_escapes` runs `to_unescaped_string` at
/// the parse entry points precisely so the infallible builder never has to,
/// so decoding it there is sound; the passing cases above only use *valid*
/// escapes, so this pins the reject path they never reach.
#[test]
fn temporal_invalid_escape_is_rejected() {
    let svc = service();
    // `\z` is not a valid Cedar/Rust string escape.
    let policy = temporal_policy("a\\zb");
    let result = LoweredPolicySet::from_str(&policy, &svc, &schema());
    assert!(
        result.is_err(),
        "an invalid escape in a temporal literal must be rejected at parse, got: {result:?}"
    );
}
