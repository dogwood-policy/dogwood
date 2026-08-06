//! End-to-end proof that a temporal predicate can match a **nested logged
//! field** whose nesting comes from the *action schema's input type*.
//!
//! Background (the "validator asymmetry"): when an action's `input` type has a
//! record-typed member (`ReadInput = { meta: Meta }`), the event-schema
//! derivation used to splice that member as a single opaque leaf `input.meta`,
//! so a deep predicate arg `Read::request{ input.meta.region: … }` failed the
//! names check — even though the deep *comparison* path `context.input.meta.
//! region` validated (it reads Cedar's typed context, which descends records).
//! Yet the runtime evaluator was always general-depth (`field_path` descends
//! `Value::Object`s to any depth). So validation was strictly stricter than
//! evaluation: the derivation was the sole thing rejecting the deep predicate
//! arg. The fix makes the spread recurse into record-typed members.
//!
//! These tests pin the whole pipeline agreeing — **validate + lower + replay**
//! — for a deep predicate arg AND for the equivalent deep context-comparison
//! form, and prove the match is real (a wrong nested value does NOT fire the
//! guard) rather than a validation-only concession.

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema, Validator, Value,
};
use std::collections::BTreeMap;

/// An action whose `input` type nests a record-typed member (`meta: Meta`)
/// with a string leaf (`region`) and an int leaf (`level`).
const SCHEMA: &str = r#"
namespace Drupe {
  type Meta = { region: String, level: Long };
  type ReadInput = { user: String, meta: Meta };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
  action "Audit" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

// A history-gated PERMIT: allow a Read only if an Audit whose nested
// `input.meta.region` equals the decision's `context.input.meta.region` was
// formerly seen within the hour. The predicate arg addresses a DEEP nested
// leaf — the shape the fix enables.
const PERMIT_DEEP_PREDICATE_ARG: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Audit"::request{
        input.meta.region: context.input.meta.region
    }
};
"#;

// The equivalent guard written as a deep context comparison (the form that
// validated even before the fix). Both must produce identical verdicts.
const PERMIT_DEEP_CONTEXT_CMP: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h (
        Drupe::Action::"Audit"::request{}
        && context.input.meta.region == "us"
    )
};
"#;

/// Lower `policy` against an explicit action schema + service schema — the
/// general form the output / injected-field cases need (a custom event schema,
/// a different action schema).
fn lower_ex(policy: &str, action_schema: &str, service: &ServiceSchema) -> LoweredPolicySet {
    let policy_schema =
        PolicySchema::from_cedarschema_str(action_schema).expect("action schema builds");
    LoweredPolicySet::from_str(policy, service, &policy_schema).expect("policy lowers")
}

fn lower(policy: &str) -> LoweredPolicySet {
    lower_ex(policy, SCHEMA, &ServiceSchema::defaults())
}

fn validate_ex(policy: &str, action_schema: &str, service: &ServiceSchema) {
    let lowered = lower_ex(policy, action_schema, service);
    let result = Validator::new().validate(&lowered);
    assert!(
        result.validation_passed(),
        "policy must validate (deep nested field is a declared leaf):\n{policy}"
    );
}

fn validate(policy: &str) {
    validate_ex(policy, SCHEMA, &ServiceSchema::defaults());
}

/// A `Value::Object` holding a `meta` sub-record `{ region, level }`.
fn meta(region: &str, level: i64) -> Value {
    let mut m = BTreeMap::new();
    m.insert("region".to_string(), Value::String(region.to_string()));
    m.insert("level".to_string(), Value::Int(level));
    Value::Object(m)
}

/// The decision Read event. Its guard's RHS reads `context.input.meta.region`,
/// a request-context reference, so the nested value is set in the request
/// context (the bag the Cedar decision is built from).
fn read_event(ts: i64, region: &str) -> Event {
    Event::builder("Drupe::Action::Read", "request")
        .timestamp(ts)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .request_context("input", "user", Value::String("alice".to_string()))
        .request_context("input", "meta", meta(region, 1))
        .build()
}

/// The history Audit event. The predicate `…::Audit::request{ input.meta.region:
/// … }` matches against the *logged* record, so the nested value goes in
/// `logged` via `.field("input", "meta", …)`. The same value rides in the
/// request context so the event is a well-formed decision-kind event.
fn audit_event(ts: i64, region: &str) -> Event {
    Event::builder("Drupe::Action::Audit", "request")
        .timestamp(ts)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .field("input", "meta", meta(region, 1))
        .request_context("input", "user", Value::String("alice".to_string()))
        .request_context("input", "meta", meta(region, 1))
        .build()
}

#[test]
fn deep_predicate_arg_validates() {
    validate(PERMIT_DEEP_PREDICATE_ARG);
}

#[test]
fn deep_context_comparison_validates() {
    validate(PERMIT_DEEP_CONTEXT_CMP);
}

#[test]
fn deep_predicate_arg_matches_when_nested_values_agree() {
    // The Audit's nested region matches the Read's → guard fires → permit.
    let mut auth = Authorizer::new(lower(PERMIT_DEEP_PREDICATE_ARG));
    auth.is_authorized(&audit_event(100, "us"));
    let resp = auth
        .is_authorized(&read_event(200, "us"))
        .expect("request is a decision point");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "a Read whose nested input.meta.region matches a formerly-Audited region \
         must be allowed — the deep predicate arg genuinely matched"
    );
}

#[test]
fn deep_predicate_arg_does_not_match_when_nested_values_differ() {
    // The Audit's nested region differs from the Read's → guard does NOT fire
    // → the sole permit's temporal guard is false → default deny. This proves
    // the match reads the real nested leaf, not a vacuous always-true.
    let mut auth = Authorizer::new(lower(PERMIT_DEEP_PREDICATE_ARG));
    auth.is_authorized(&audit_event(100, "eu"));
    let resp = auth
        .is_authorized(&read_event(200, "us"))
        .expect("request is a decision point");
    assert_eq!(
        resp.decision(),
        Decision::Deny,
        "a mismatched nested region must NOT fire the guard (the deep leaf is \
         genuinely compared, not treated as a wildcard)"
    );
}

// ─── (1) Deep predicate arg from a nested OUTPUT record ─────────────────
//
// The same recursion applies to `...outputs(A)`. A `response` event carries
// output fields; a record-typed output member (`detail: Detail`) must nest so
// `output.detail.code` is a matchable predicate-arg leaf. A `response` is a
// history event (not a decision point), so we gate a later `Read` decision on
// a formerly-seen `Review::response` whose deep output leaf matches.

const OUTPUT_SCHEMA: &str = r#"
namespace Drupe {
  type Meta = { region: String, level: Long };
  type ReadInput = { user: String, meta: Meta };
  type ReviewInput  = { user: String };
  type Detail = { code: Long, note: String };
  type ReviewOutput = { verdict: String, detail: Detail };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
  action "Review" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: ReviewInput, output?: ReviewOutput }
  };
}
"#;

// Permit a Read only if a Review response with a formerly-seen nested output
// code == 7 exists in the last hour. The predicate arg pins a DEEP OUTPUT leaf.
const PERMIT_DEEP_OUTPUT_ARG: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Review"::response{
        output.detail.code: 7
    }
};
"#;

/// A `Value::Object` output-detail sub-record `{ code, note }`.
fn detail(code: i64) -> Value {
    let mut m = BTreeMap::new();
    m.insert("code".to_string(), Value::Int(code));
    m.insert("note".to_string(), Value::String("n".to_string()));
    Value::Object(m)
}

/// A Review response (history) event carrying a nested output `detail.code`.
fn review_response(ts: i64, code: i64) -> Event {
    let mut output = BTreeMap::new();
    output.insert("verdict".to_string(), Value::String("ok".to_string()));
    output.insert("detail".to_string(), detail(code));
    Event::builder("Drupe::Action::Review", "response")
        .timestamp(ts)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .field("output", "verdict", Value::String("ok".to_string()))
        .field("output", "detail", detail(code))
        .request_context("input", "user", Value::String("alice".to_string()))
        .request_context("output", "verdict", Value::String("ok".to_string()))
        .request_context("output", "detail", detail(code))
        .build()
}

/// A Read decision event under the OUTPUT_SCHEMA (no deep guard of its own).
fn output_read_event(ts: i64) -> Event {
    Event::builder("Drupe::Action::Read", "request")
        .timestamp(ts)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .request_context("input", "user", Value::String("alice".to_string()))
        .request_context("input", "meta", meta("us", 1))
        .build()
}

#[test]
fn deep_output_predicate_arg_validates() {
    validate_ex(
        PERMIT_DEEP_OUTPUT_ARG,
        OUTPUT_SCHEMA,
        &ServiceSchema::defaults(),
    );
}

#[test]
fn deep_output_predicate_arg_matches_when_nested_value_agrees() {
    let service = ServiceSchema::defaults();
    let mut auth = Authorizer::new(lower_ex(PERMIT_DEEP_OUTPUT_ARG, OUTPUT_SCHEMA, &service));
    auth.is_authorized(&review_response(100, 7)); // history: code == 7
    let resp = auth
        .is_authorized(&output_read_event(200))
        .expect("request is a decision point");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "a formerly-seen Review response with output.detail.code == 7 must \
         fire the guard — the deep OUTPUT predicate arg genuinely matched"
    );
}

#[test]
fn deep_output_predicate_arg_does_not_match_when_nested_value_differs() {
    let service = ServiceSchema::defaults();
    let mut auth = Authorizer::new(lower_ex(PERMIT_DEEP_OUTPUT_ARG, OUTPUT_SCHEMA, &service));
    auth.is_authorized(&review_response(100, 9)); // history: code == 9 (≠ 7)
    let resp = auth
        .is_authorized(&output_read_event(200))
        .expect("request is a decision point");
    assert_eq!(
        resp.decision(),
        Decision::Deny,
        "a Review response whose output.detail.code != 7 must NOT fire the \
         guard (the deep output leaf is genuinely compared)"
    );
}

// ─── (2) Deep predicate arg from an event-schema-INJECTED nested field ──
//
// This nesting comes from the event-schema DSL itself (`meta: { session: { id
// } }`), NOT from the action-schema input type — a *different* derivation path
// (`derive_fields`'s `TypeExpr::Record` arm) that the input/output fix did not
// touch. Its derivation + names-check nesting were already unit-tested, but the
// end-to-end validate+lower+replay agreement was never proven; this closes that.

// A custom event schema that injects a depth-3 nested field on the request
// event, alongside the stock inputs/reserved fields.
const INJECTED_EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    meta: { session: { id: String } },
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
event <A>::response {
    ...inputs(A),
    ...outputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

// A plain action schema (no nested input); the deep field is purely injected.
const INJECTED_ACTION_SCHEMA: &str = r#"
namespace Drupe {
  type ReadInput = { user: String };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
  action "Audit" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
}
"#;

// Permit a Read only if an Audit whose injected `meta.session.id` == "s1" was
// formerly seen. The predicate arg pins a DEEP INJECTED leaf.
const PERMIT_DEEP_INJECTED_ARG: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Audit"::request{
        meta.session.id: "s1"
    }
};
"#;

fn injected_service() -> ServiceSchema {
    ServiceSchema::builder()
        .event_schema_str(INJECTED_EVENT_SCHEMA)
        .build()
        .expect("injected event schema parses")
}

/// The `session` sub-record `{ id }` — the value of the injected group
/// `meta`'s `session` member. The builder's `.field("meta", "session", v)`
/// sets `logged["meta"]["session"] = v`, so this is `meta.session`, and its
/// `id` member is the depth-3 leaf `meta.session.id`.
fn session(id: &str) -> Value {
    let mut sess = BTreeMap::new();
    sess.insert("id".to_string(), Value::String(id.to_string()));
    Value::Object(sess)
}

/// An Audit request event carrying the injected `meta.session.id` in its
/// logged record (predicate args read `logged`).
fn injected_audit(ts: i64, id: &str) -> Event {
    Event::builder("Drupe::Action::Audit", "request")
        .timestamp(ts)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .field("meta", "session", session(id))
        .request_context("input", "user", Value::String("alice".to_string()))
        .build()
}

/// A Read decision under the injected schema.
fn injected_read(ts: i64) -> Event {
    Event::builder("Drupe::Action::Read", "request")
        .timestamp(ts)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .request_context("input", "user", Value::String("alice".to_string()))
        .build()
}

#[test]
fn deep_injected_predicate_arg_validates() {
    validate_ex(
        PERMIT_DEEP_INJECTED_ARG,
        INJECTED_ACTION_SCHEMA,
        &injected_service(),
    );
}

#[test]
fn deep_injected_predicate_arg_matches_when_nested_value_agrees() {
    let service = injected_service();
    let mut auth = Authorizer::new(lower_ex(
        PERMIT_DEEP_INJECTED_ARG,
        INJECTED_ACTION_SCHEMA,
        &service,
    ));
    auth.is_authorized(&injected_audit(100, "s1"));
    let resp = auth
        .is_authorized(&injected_read(200))
        .expect("request is a decision point");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "a formerly-seen Audit with injected meta.session.id == \"s1\" must fire \
         the guard — the deep INJECTED predicate arg genuinely matched"
    );
}

#[test]
fn deep_injected_predicate_arg_does_not_match_when_nested_value_differs() {
    let service = injected_service();
    let mut auth = Authorizer::new(lower_ex(
        PERMIT_DEEP_INJECTED_ARG,
        INJECTED_ACTION_SCHEMA,
        &service,
    ));
    auth.is_authorized(&injected_audit(100, "other"));
    let resp = auth
        .is_authorized(&injected_read(200))
        .expect("request is a decision point");
    assert_eq!(
        resp.decision(),
        Decision::Deny,
        "an Audit whose injected meta.session.id != \"s1\" must NOT fire the guard"
    );
}

#[test]
fn deep_context_comparison_matches_the_decision_region_at_runtime() {
    // The deep CONTEXT-path form (`context.input.meta.region == "us"`) reads
    // the *decision* event's request context — a different datum than the
    // predicate arg (which reads the historical logged event). This pins that
    // the deep context path also resolves + matches at replay, and that it
    // reads the DECISION's nested region: an Audit exists in both runs, so the
    // verdict tracks the Read's own region.
    // Read region "us" → guard true → allow.
    let mut a = Authorizer::new(lower(PERMIT_DEEP_CONTEXT_CMP));
    a.is_authorized(&audit_event(100, "ignored"));
    assert_eq!(
        a.is_authorized(&read_event(200, "us"))
            .expect("decision point")
            .decision(),
        Decision::Allow,
        "decision region us must satisfy context.input.meta.region == \"us\""
    );
    // Read region "eu" → guard false → default deny.
    let mut b = Authorizer::new(lower(PERMIT_DEEP_CONTEXT_CMP));
    b.is_authorized(&audit_event(100, "ignored"));
    assert_eq!(
        b.is_authorized(&read_event(200, "eu"))
            .expect("decision point")
            .decision(),
        Decision::Deny,
        "decision region eu must NOT satisfy context.input.meta.region == \"us\""
    );
}
