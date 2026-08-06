//! The Cedar entity store `decide()` authorizes against.
//!
//! **Stage 1** — `decide()` prepopulates the store with the request's scope
//! entities (principal + resource) as bare, attribute-less entities (replacing
//! `Entities::empty()`), so an attribute read reaches "does not have the
//! attribute X" (entity present, attribute absent) rather than "entity does
//! not exist", still fail-closed.
//!
//! **Stage 2** — callers supply entity attributes via
//! [`EventBuilder::entity`]; those attributes are validated against the
//! augmented schema and made available to both pure-Cedar attribute reads
//! (`principal.dept`) and provider arguments. Supplied attributes that don't
//! conform (wrong type, or a missing `required` attribute on an entity opted
//! into the attribute channel) fail closed with a diagnostic.
//!
//! The schema declares `Svc::User = { id, dept }` so these attribute reads
//! validate cleanly — the only variable under test is the runtime store.

use std::sync::Mutex;

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ProviderDeclarations,
    ProviderRequest, ProviderResolver, ServiceSchema, Value, parse_trace, replay_log,
};

fn service() -> ServiceSchema {
    ServiceSchema::defaults()
}

fn schema_src() -> String {
    std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/entity_store_probe.cedarschema"
    ))
    .expect("schema")
}

fn lower(policy: &str) -> LoweredPolicySet {
    LoweredPolicySet::from_str(
        policy,
        &service(),
        &PolicySchema::from_cedarschema_str(&schema_src()).expect("policy schema"),
    )
    .expect("lower")
}

/// A `Svc::Read` request by `User::"alice"` on `Gateway::"gw1"`, with the
/// `input.doc` context field the schema declares. Supplied via
/// `request_context` (what the Cedar request reads) — and also `input` (the
/// logged record) so the event is well-formed for temporal too; the two
/// datasets are deliberately separate, so a field the request reads must be in
/// `request_context`.
fn read_event() -> Event {
    Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("hello".to_string()))
        .request_context("input", "doc", Value::String("hello".to_string()))
        .build()
}

/// (decision, joined runtime-error text) for authorizing `policy` on `event`.
fn decide_on(policy: &str, event: &Event) -> (Decision, String) {
    let mut authorizer = Authorizer::new(lower(policy));
    let resp = authorizer
        .is_authorized(event)
        .expect("request kind is a decision point");
    let errs = resp.diagnostics().errors().collect::<Vec<_>>().join(" | ");
    (resp.decision(), errs)
}

/// The common case: authorize `policy` on the bare read event (no supplied
/// entity attributes).
fn decide(policy: &str) -> (Decision, String) {
    decide_on(policy, &read_event())
}

#[test]
fn scope_identity_read_is_unaffected() {
    // Matching the principal uid in scope needs no entity attributes; the
    // scope-prepopulated store does not change this — still Allow.
    let (decision, errs) = decide(
        r#"permit ( principal == Svc::User::"alice", action == Svc::Action::"Read", resource );"#,
    );
    assert_eq!(decision, Decision::Allow);
    assert_eq!(errs, "", "no evaluation errors");
}

#[test]
fn context_read_is_unaffected() {
    // Reading a context field is orthogonal to the entity store — still Allow.
    let (decision, errs) = decide(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { context.input.doc == "hello" };"#,
    );
    assert_eq!(decision, Decision::Allow);
    assert_eq!(errs, "", "no evaluation errors");
}

#[test]
fn entity_attribute_read_denies_with_attribute_absent_not_entity_absent() {
    // The scope entity IS now present (stage-1 prepopulation), so reading an
    // attribute it doesn't carry fails with "does not have the attribute",
    // NOT "does not exist". Verdict is fail-closed Deny either way; the message
    // distinguishes present-but-bare (this) from absent (pre-stage-1).
    let (decision, errs) = decide(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { principal.dept == "eng" };"#,
    );
    assert_eq!(
        decision,
        Decision::Deny,
        "unresolved attribute fails closed"
    );
    assert!(
        errs.contains("does not have the attribute") && errs.contains("dept"),
        "expected present-entity/attribute-absent error, got: {errs}"
    );
    assert!(
        !errs.contains("does not exist"),
        "entity must be present (not the empty-store 'does not exist' error): {errs}"
    );
}

#[test]
fn even_a_declared_id_attribute_is_absent_on_a_bare_scope_entity() {
    // Guards the corrected design premise: Cedar has no `.id`/`.type` builtin —
    // `principal.id` is an ordinary attribute access. A bare scope entity has
    // no `id` attribute, so this ALSO denies with "does not have the attribute
    // `id`". (I.e. scope-prepopulation does NOT make `principal.id` "work";
    // that needs a supplied `id`, which stage 2 delivers below.)
    let (decision, errs) = decide(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { principal.id == "alice" };"#,
    );
    assert_eq!(decision, Decision::Deny);
    assert!(
        errs.contains("does not have the attribute") && errs.contains("id"),
        "expected `id` attribute-absent error, got: {errs}"
    );
}

// ─── stage 2: supplied entity attributes ─────────────────────────────

/// The read event, plus `dept: "eng"` supplied for the principal via the
/// entity channel. `id` is required by the schema, so supply it too (opting an
/// entity into the attribute channel opts into its required attributes).
fn read_event_with_principal_attrs() -> Event {
    Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("hello".to_string()))
        .entity(
            "Svc::User::\"alice\"",
            [
                ("id", Value::String("alice".to_string())),
                ("dept", Value::String("eng".to_string())),
            ],
        )
        .build()
}

#[test]
fn supplied_attribute_makes_a_pure_cedar_read_evaluate() {
    // With `dept` supplied, `principal.dept == "eng"` now evaluates true and
    // the permit fires — the core capability stage 2 delivers.
    let (decision, errs) = decide_on(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { principal.dept == "eng" };"#,
        &read_event_with_principal_attrs(),
    );
    assert_eq!(
        decision,
        Decision::Allow,
        "supplied attribute resolves; got errs: {errs}"
    );
    assert_eq!(errs, "");
}

#[test]
fn supplied_attribute_that_does_not_match_denies_cleanly() {
    // `dept` is "eng"; a guard requiring "sales" simply does not hold — a
    // normal Deny with no evaluation error (the attribute resolved, it just
    // compared false).
    let (decision, errs) = decide_on(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { principal.dept == "sales" };"#,
        &read_event_with_principal_attrs(),
    );
    assert_eq!(decision, Decision::Deny);
    assert_eq!(
        errs, "",
        "attribute resolved and compared false — not an error"
    );
}

#[test]
fn wrong_typed_supplied_attribute_fails_conformance_closed() {
    // Schema declares `dept: String`. Supplying an Int violates conformance;
    // `from_entities(_, Some(schema))` rejects it at store build, folded into a
    // fail-closed Deny with the error in diagnostics (not a silent mis-decide).
    let event = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("hello".to_string()))
        .entity(
            "Svc::User::\"alice\"",
            [
                ("id", Value::String("alice".to_string())),
                ("dept", Value::Int(42)), // wrong type
            ],
        )
        .build();
    let (decision, errs) = decide_on(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { principal.dept == "eng" };"#,
        &event,
    );
    assert_eq!(decision, Decision::Deny, "conformance failure fails closed");
    assert!(
        errs.contains("conformance") || errs.contains("dept") || errs.contains("type"),
        "expected a conformance/type diagnostic, got: {errs}"
    );
}

#[test]
fn missing_required_attribute_on_a_supplied_entity_fails_conformance() {
    // The schema marks `id` required. Supplying *only* `dept` for the principal
    // opts it into the attribute channel but omits a required attribute, so
    // conformance rejects it — fail-closed, per the design (a caller supplying
    // an entity's attributes must supply its required ones).
    let event = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("hello".to_string()))
        .entity(
            "Svc::User::\"alice\"",
            [("dept", Value::String("eng".to_string()))],
        )
        .build();
    let (decision, errs) = decide_on(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { principal.dept == "eng" };"#,
        &event,
    );
    assert_eq!(decision, Decision::Deny);
    assert!(
        errs.contains("conformance") || errs.contains("id"),
        "expected a missing-required-attr diagnostic, got: {errs}"
    );
}

#[test]
fn null_supplied_for_a_string_attribute_is_not_coerced_to_empty_string() {
    // A caller-supplied `Value::Null` for a schema-declared String attribute
    // must NOT be silently coerced to `""`. It is either rejected (a diagnostic)
    // or treated as attribute-absent (a missing *required* attribute here, so a
    // conformance failure) — either way fail-closed, never a value that a policy
    // could match with `principal.dept == ""`.
    //
    // Supply `id` so the *only* problematic attribute is the `Null` `dept`; if
    // `Null` were coerced to `""`, conformance would pass (empty string is a
    // valid String) and `principal.dept == ""` would evaluate true -> Allow.
    let event = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("hello".to_string()))
        .entity(
            "Svc::User::\"alice\"",
            [
                ("id", Value::String("alice".to_string())),
                ("dept", Value::Null),
            ],
        )
        .build();
    let (decision, errs) = decide_on(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { principal.dept == "" };"#,
        &event,
    );
    assert_eq!(
        decision,
        Decision::Deny,
        "a Null String attribute must not coerce to \"\" and match the guard; got errs: {errs}"
    );
}

/// Skip-on-error / forbid-weakening (design section 5.4), pinned deliberately.
///
/// A `forbid` guarded by an entity attribute that is NOT supplied errors, and
/// Cedar *skips* the erroring policy rather than denying. So with a satisfied
/// `permit` present, an unsupplied attribute a `forbid` depends on lets the
/// request through: the decision is **Allow**, with the forbid's error in
/// diagnostics. This is Cedar-consistent behavior we adopt deliberately (we do
/// not override it); the test exists so it can never change silently.
#[test]
fn erroring_forbid_is_skipped_weakening_the_deny() {
    let policy = r#"
        permit ( principal, action == Svc::Action::"Read", resource );
        forbid ( principal, action == Svc::Action::"Read", resource )
        when { principal.dept == "banned" };
    "#;
    // `dept` is NOT supplied -> the forbid's guard errors -> forbid skipped ->
    // the unconditional permit stands -> Allow, with the error surfaced.
    let (decision, errs) = decide(policy);
    assert_eq!(
        decision,
        Decision::Allow,
        "erroring forbid is skipped (Cedar skip-on-error), so the permit stands"
    );
    assert!(
        errs.contains("does not have the attribute") && errs.contains("dept"),
        "the skipped forbid's evaluation error must still surface: {errs}"
    );
}

// ─── stage 2: provider arguments resolve supplied entity attributes ──

/// A resolver that records the argument value it was handed and returns a
/// fixed output, so a test can assert *what the provider received* for a
/// `principal.<attr>` argument — the direct check that `resolve_scope_path`
/// now reads the supplied attribute rather than yielding `Null`. The capture
/// buffer is shared via `Arc` so the test can read it after the resolver is
/// moved into the authorizer.
struct CapturingResolver {
    seen: std::sync::Arc<Mutex<Vec<Value>>>,
}

impl ProviderResolver for CapturingResolver {
    fn resolve(&self, request: ProviderRequest<'_>) -> Option<Result<Value, String>> {
        self.seen.lock().unwrap().push(request.args[0].clone());
        // Return a record matching the declared output type `{ ok: Bool }`.
        Some(Ok(Value::Object(std::collections::BTreeMap::from([(
            "ok".to_string(),
            Value::Bool(true),
        )]))))
    }
}

#[test]
fn provider_argument_resolves_a_supplied_principal_attribute() {
    // Schema: principal `User` has a `dept` attribute; the `Check::Dept`
    // provider takes a String and returns `{ ok: Bool }`.
    let schema = r#"
        namespace Svc {
          entity Gateway;
          entity User = { dept: String };
          action "Read" appliesTo {
            principal: [User], resource: [Gateway],
            context: { input: { doc: String } }
          };
        }
    "#;
    let providers = ProviderDeclarations::from_json(
        r#"{ "availableProviders": { "Check::Dept": {
              "argumentTypes": [ { "paramType": "string" } ],
              "outputType": { "paramType": "record",
                              "fields": { "ok": { "paramType": "bool" } },
                              "required": ["ok"] } } } }"#,
    )
    .expect("providers json");
    let service = ServiceSchema::builder()
        .providers(providers)
        .build()
        .expect("service schema");
    let policy = r#"
        permit ( principal, action == Svc::Action::"Read", resource )
        when guardrails { Check::Dept(principal.dept).ok == true };
    "#;
    let policies = LoweredPolicySet::from_str(
        policy,
        &service,
        &PolicySchema::from_cedarschema_str(schema).expect("policy schema"),
    )
    .expect("lower");

    let seen = std::sync::Arc::new(Mutex::new(Vec::new()));
    let event = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("hi".to_string()))
        .entity(
            "Svc::User::\"alice\"",
            [("dept", Value::String("eng".to_string()))],
        )
        .build();

    let mut authorizer = Authorizer::builder(policies)
        .provider_resolver(CapturingResolver { seen: seen.clone() })
        .build()
        .expect("authorizer builds");
    let resp = authorizer.is_authorized(&event).expect("decision point");

    // The provider was handed the *supplied* dept value, not Null.
    assert_eq!(
        seen.lock().unwrap().as_slice(),
        &[Value::String("eng".to_string())],
        "provider must receive the supplied principal.dept, not Null"
    );
    assert_eq!(resp.decision(), Decision::Allow);
}

#[test]
fn external_resolver_receives_null_for_absent_argument() {
    // The provider-contract side of the ProviderResolver seam: execution is
    // unconditional, so a resolver can be invoked with an argument that does
    // not resolve on the event — it must arrive as Value::Null (not error,
    // not be skipped), and the resolver's returned value must govern as
    // usual. Here the event supplies NO `dept` attribute for alice, so the
    // resolver sees Null and returns { ok: false } -> Deny by this policy.
    let schema = r#"
        namespace Svc {
          entity Gateway;
          entity User = { dept: String };
          action "Read" appliesTo {
            principal: [User], resource: [Gateway],
            context: { input: { doc: String } }
          };
        }
    "#;
    let providers = ProviderDeclarations::from_json(
        r#"{ "availableProviders": { "Check::Dept": {
              "argumentTypes": [ { "paramType": "string" } ],
              "outputType": { "paramType": "record",
                              "fields": { "ok": { "paramType": "bool" } },
                              "required": ["ok"] } } } }"#,
    )
    .expect("providers json");
    let service = ServiceSchema::builder()
        .providers(providers)
        .build()
        .expect("service schema");
    let policy = r#"
        permit ( principal, action == Svc::Action::"Read", resource )
        when guardrails { Check::Dept(principal.dept).ok == true };
    "#;
    let policies = LoweredPolicySet::from_str(
        policy,
        &service,
        &PolicySchema::from_cedarschema_str(schema).expect("policy schema"),
    )
    .expect("lower");

    /// Returns `{ ok: <arg is not Null> }` — so the verdict itself reports
    /// whether the resolver saw a real value.
    struct NullAwareResolver {
        seen: std::sync::Arc<Mutex<Vec<Value>>>,
    }
    impl ProviderResolver for NullAwareResolver {
        fn resolve(&self, request: ProviderRequest<'_>) -> Option<Result<Value, String>> {
            let arg = request.args[0].clone();
            let ok = !matches!(arg, Value::Null);
            self.seen.lock().unwrap().push(arg);
            Some(Ok(Value::Object(std::collections::BTreeMap::from([(
                "ok".to_string(),
                Value::Bool(ok),
            )]))))
        }
    }

    let seen = std::sync::Arc::new(Mutex::new(Vec::new()));
    // No `.entity(...)` supplying dept: the argument is absent on this event.
    let event = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("hi".to_string()))
        .build();

    let mut authorizer = Authorizer::builder(policies)
        .provider_resolver(NullAwareResolver { seen: seen.clone() })
        .build()
        .expect("authorizer builds");
    let resp = authorizer.is_authorized(&event).expect("decision point");

    assert_eq!(
        seen.lock().unwrap().as_slice(),
        &[Value::Null],
        "an absent argument must reach the external resolver as Value::Null"
    );
    // The resolver ran (no error, no skip) and its { ok: false } governed.
    assert_eq!(resp.decision(), Decision::Deny);
    assert_eq!(
        resp.diagnostics().errors().count(),
        0,
        "a Null argument is an expected input, not an evaluation error"
    );
}

// ─── stage 3: end-to-end `.log` entities(...) envelope ───────────────

/// A `.log` trace whose `entities(...)` envelope supplies the principal's
/// attributes drives a real decision end to end (parse -> store -> authorize).
/// Two timepoints on the same policy: one supplies `dept: "eng"` (permit
/// fires, Allow), one supplies `dept: "sales"` (guard false, Deny) — proving
/// the parsed per-event store actually reaches evaluation and that attribute
/// values differ per line.
#[test]
fn log_entities_envelope_drives_a_decision() {
    let policy = r#"permit ( principal, action == Svc::Action::"Read", resource )
                    when { principal.dept == "eng" };"#;
    let log = r#"
@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::User::"alice": { id: "alice", dept: "eng" }) Svc::Action::"Read"::request(input: { doc: "x" })
@1 scope(principal: Svc::User::"bob", resource: Svc::Gateway::"gw1") entities(Svc::User::"bob": { id: "bob", dept: "sales" }) Svc::Action::"Read"::request(input: { doc: "y" })
"#;
    let out = replay_log(lower(policy), log).expect("replay");
    let verdicts: Vec<bool> = out.lines().map(|l| l.ends_with("true")).collect();
    assert_eq!(
        verdicts,
        vec![true, false],
        "eng -> Allow, sales -> Deny (per-line supplied attributes reach evaluation): {out}"
    );
}

/// A `.log` trace with NO `entities(...)` envelope: a policy reading an entity
/// attribute denies (present-but-bare scope entity), exactly the stage-1
/// behavior — confirming existing envelope-free traces are unaffected end to
/// end.
#[test]
fn log_without_entities_envelope_denies_attribute_read() {
    let policy = r#"permit ( principal, action == Svc::Action::"Read", resource )
                    when { principal.dept == "eng" };"#;
    let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") Svc::Action::"Read"::request(input: { doc: "x" })"#;
    let out = replay_log(lower(policy), log).expect("replay");
    assert!(
        out.ends_with("false"),
        "no attributes supplied -> Deny: {out}"
    );
}

// ─── nested (multi-segment) attribute paths ──────────────────────────

/// Schema with a nested record-valued principal attribute
/// (`address: { city: String }`), for the nested-path tests below.
const NESTED_SCHEMA: &str = r#"
    namespace Svc {
      entity Gateway;
      entity User = { address: { city: String } };
      action "Read" appliesTo {
        principal: [User], resource: [Gateway],
        context: { input: { doc: String } }
      };
    }
"#;

/// An event supplying the principal's nested `address` record.
fn nested_event() -> Event {
    Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .entity(
            "Svc::User::\"alice\"",
            [(
                "address",
                Value::Object(std::collections::BTreeMap::from([(
                    "city".to_string(),
                    Value::String("sea".to_string()),
                )])),
            )],
        )
        .build()
}

/// Baseline: a **pure-Cedar** read of a nested attribute path
/// (`principal.address.city`) descends the supplied record and evaluates —
/// Cedar resolves it against the entity store. (Contrast the provider path
/// below, which must be brought into line with this.)
#[test]
fn pure_cedar_reads_a_nested_attribute_path() {
    let policy = r#"
        permit ( principal, action == Svc::Action::"Read", resource )
        when { principal.address.city == "sea" };
    "#;
    let policies = LoweredPolicySet::from_str(
        policy,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(NESTED_SCHEMA).expect("policy schema"),
    )
    .expect("lower");
    let mut authorizer = Authorizer::new(policies);
    let resp = authorizer.is_authorized(&nested_event()).expect("decision");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "pure Cedar descends the supplied nested record"
    );
}

/// A **provider argument** that is a nested attribute path
/// (`principal.address.city`) must resolve to the supplied value, exactly as
/// the pure-Cedar path does. Before the fix, `resolve_scope_path` returned
/// `Null` for any path deeper than one segment (a silent-`Null` asymmetry with
/// pure Cedar); this pins that the provider now receives `"sea"`.
#[test]
fn provider_argument_resolves_a_nested_attribute_path() {
    let schema = r#"
        namespace Svc {
          entity Gateway;
          entity User = { address: { city: String } };
          action "Read" appliesTo {
            principal: [User], resource: [Gateway],
            context: { input: { doc: String } }
          };
        }
    "#;
    let providers = ProviderDeclarations::from_json(
        r#"{ "availableProviders": { "Check::City": {
              "argumentTypes": [ { "paramType": "string" } ],
              "outputType": { "paramType": "record",
                              "fields": { "ok": { "paramType": "bool" } },
                              "required": ["ok"] } } } }"#,
    )
    .expect("providers json");
    let service = ServiceSchema::builder()
        .providers(providers)
        .build()
        .expect("service schema");
    let policy = r#"
        permit ( principal, action == Svc::Action::"Read", resource )
        when guardrails { Check::City(principal.address.city).ok == true };
    "#;
    let policies = LoweredPolicySet::from_str(
        policy,
        &service,
        &PolicySchema::from_cedarschema_str(schema).expect("policy schema"),
    )
    .expect("lower");

    let seen = std::sync::Arc::new(Mutex::new(Vec::new()));
    let mut authorizer = Authorizer::builder(policies)
        .provider_resolver(CapturingResolver { seen: seen.clone() })
        .build()
        .expect("authorizer builds");
    authorizer.is_authorized(&nested_event()).expect("decision");

    assert_eq!(
        seen.lock().unwrap().as_slice(),
        &[Value::String("sea".to_string())],
        "provider must receive the supplied nested principal.address.city, not Null"
    );
}

// ─── the `has` operator on an optional attribute ─────────────────────
//
// `has` is the total, non-erroring counterpart to a bare attribute read.
// Cedar's evaluator returns `false` (never errors) when the attribute — or the
// whole entity — is absent, which is how a policy safely guards an optional
// read: `principal has x && principal.x == …`. These tests pin that behavior,
// which requires an *optional* schema attribute (a required one is always
// present after conformance, so `has` would be trivially true). Optional
// attributes are otherwise untested, so this also closes that conformance gap.

/// Schema with an **optional** principal attribute (`clearance?`).
const OPTIONAL_ATTR_SCHEMA: &str = r#"
    namespace Svc {
      entity Gateway;
      entity User = { name: String, clearance?: String };
      action "Read" appliesTo {
        principal: [User], resource: [Gateway],
        context: { input: { doc: String } }
      };
    }
"#;

fn decide_optional(policy: &str, event: &Event) -> (Decision, String) {
    let policies = LoweredPolicySet::from_str(
        policy,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(OPTIONAL_ATTR_SCHEMA).expect("policy schema"),
    )
    .expect("lower");
    let mut authorizer = Authorizer::new(policies);
    let resp = authorizer.is_authorized(event).expect("decision");
    let errs = resp.diagnostics().errors().collect::<Vec<_>>().join(" | ");
    (resp.decision(), errs)
}

/// The read event, supplying `name` and optionally `clearance`.
fn optional_attr_event(clearance: Option<&str>) -> Event {
    let mut attrs = vec![("name", Value::String("alice".to_string()))];
    if let Some(c) = clearance {
        attrs.push(("clearance", Value::String(c.to_string())));
    }
    Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .entity("Svc::User::\"alice\"", attrs)
        .build()
}

#[test]
fn has_is_true_when_optional_attribute_supplied() {
    let (decision, errs) = decide_optional(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { principal has clearance };"#,
        &optional_attr_event(Some("high")),
    );
    assert_eq!(decision, Decision::Allow);
    assert_eq!(errs, "");
}

#[test]
fn has_is_false_without_error_when_optional_attribute_absent() {
    // The defining property: `has` on an absent (optional) attribute is
    // `false` and does NOT error — unlike a bare `principal.clearance` read,
    // which would error "does not have the attribute". So this is a plain Deny
    // with no evaluation error.
    let (decision, errs) = decide_optional(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { principal has clearance };"#,
        &optional_attr_event(None),
    );
    assert_eq!(decision, Decision::Deny);
    assert_eq!(
        errs, "",
        "`has` on an absent attribute is false, not an error"
    );
}

#[test]
fn has_guards_a_read_that_would_otherwise_error() {
    // The idiomatic safe-read pattern. `clearance` is absent, so
    // `principal has clearance` is false and `&&` short-circuits before the
    // read — the whole clause is false with NO evaluation error, even though a
    // bare `principal.clearance == "high"` alone would have errored.
    let (decision, errs) = decide_optional(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { principal has clearance && principal.clearance == "high" };"#,
        &optional_attr_event(None),
    );
    assert_eq!(decision, Decision::Deny);
    assert_eq!(
        errs, "",
        "`has` short-circuits the read, so no evaluation error"
    );
}

#[test]
fn omitting_an_optional_attribute_conforms() {
    // Contrast `missing_required_attribute_on_a_supplied_entity_fails_conformance`:
    // omitting an *optional* attribute conforms fine (no fail-closed), so an
    // unconditional permit is simply allowed.
    let (decision, errs) = decide_optional(
        r#"permit ( principal, action == Svc::Action::"Read", resource );"#,
        &optional_attr_event(None),
    );
    assert_eq!(
        decision,
        Decision::Allow,
        "optional attr may be omitted: {errs}"
    );
    assert_eq!(errs, "");
}

// ─── logged ↔ request_context isolation (the stage-1+2 core invariant) ─
//
// `EventData` splits an event into two bags: `logged` (the durable temporal
// record, read by temporal predicate field-args via `field_path`) and
// `request_context` (the ephemeral per-decision context, read by the Cedar
// request via `build_context`). The two are fully separated — neither consumer
// reads the other's bag. The corpus dual-supplies `input` to *both*, so the
// isolation is only exercised incidentally there; these tests place a field in
// exactly one bag and confirm it is visible to that bag's consumer and
// invisible to the other, in both directions.

/// Schema with a two-group context (`input` + `sys`), so a test can supply one
/// group to only one bag. `sys.mode` is the discriminating field.
const TWO_GROUP_SCHEMA: &str = r#"
    namespace Svc {
      entity Gateway;
      entity User = { id: String };
      action "Read" appliesTo {
        principal: [User], resource: [Gateway],
        context: { input: { doc: String }, sys: { mode: String } }
      };
    }
"#;

fn lower_two_group(policy: &str) -> LoweredPolicySet {
    // The default request/response event schema derives a `Read::request`
    // event from the action's inputs, so a temporal predicate can name it.
    LoweredPolicySet::from_str(
        policy,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(TWO_GROUP_SCHEMA).expect("policy schema"),
    )
    .expect("lower")
}

#[test]
fn request_context_only_field_is_visible_to_cedar() {
    // `sys` is supplied ONLY in request_context (never in the logged group).
    // A pure-Cedar `when { context.sys.mode == … }` reads request_context, so
    // it resolves and the permit fires — the request sees a request-only field.
    let event = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        // logged: input only (a well-formed request needs `input`, dual-supplied).
        .field("input", "doc", Value::String("x".to_string()))
        // request_context: input + sys. `sys` lives ONLY here.
        .request_context("input", "doc", Value::String("x".to_string()))
        .request_context("sys", "mode", Value::String("admin".to_string()))
        .build();
    let mut authorizer = Authorizer::new(lower_two_group(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { context.sys.mode == "admin" };"#,
    ));
    let resp = authorizer.is_authorized(&event).expect("decision point");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "a request_context-only field must be visible to the Cedar request"
    );
}

#[test]
fn request_context_only_field_is_invisible_to_temporal_matching() {
    // Same `sys`-only-in-request_context event, but now a temporal predicate
    // field-arg names `sys.mode`. Temporal matching reads the matched event's
    // `logged` record (via `field_path`), where `sys` is absent — so the
    // predicate cannot match on it. With `sys` supplied ONLY to request_context,
    // the `formerly … Read{ sys.mode: "admin" }` finds no logged `sys.mode` and
    // fails to match -> the temporal leaf is false -> Deny. This is the reverse
    // direction of the isolation: a request-only field is invisible to
    // correlation.
    let event = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .request_context("input", "doc", Value::String("x".to_string()))
        .request_context("sys", "mode", Value::String("admin".to_string()))
        .build();
    let mut authorizer = Authorizer::new(lower_two_group(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when temporal {
               formerly within 1h Svc::Action::"Read"::request{ sys.mode: "admin" }
           };"#,
    ));
    let resp = authorizer.is_authorized(&event).expect("decision point");
    assert_eq!(
        resp.decision(),
        Decision::Deny,
        "a request_context-only field must be invisible to temporal field-args (they read logged)"
    );

    // Control: put `sys` in the LOGGED bag too, and the same predicate matches
    // -> Allow. This proves the Deny above is specifically the bag isolation,
    // not an unrelated failure to match.
    let logged_event = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .field("sys", "mode", Value::String("admin".to_string())) // logged bag
        .request_context("input", "doc", Value::String("x".to_string()))
        .request_context("sys", "mode", Value::String("admin".to_string()))
        .build();
    let mut authorizer = Authorizer::new(lower_two_group(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when temporal {
               formerly within 1h Svc::Action::"Read"::request{ sys.mode: "admin" }
           };"#,
    ));
    let resp = authorizer
        .is_authorized(&logged_event)
        .expect("decision point");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "with `sys` in the logged bag, the temporal predicate matches — confirming \
         the Deny above was the isolation, not a spurious miss"
    );
}

#[test]
fn logged_only_field_is_invisible_to_cedar() {
    // The other direction: `sys` supplied ONLY in the logged bag, absent from
    // request_context. A pure-Cedar `when { context.sys.mode == … }` reads
    // request_context (empty for `sys`), so the read is unresolved -> the clause
    // does not hold -> Deny. A logged-only field is invisible to the Cedar
    // request.
    let event = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .field("sys", "mode", Value::String("admin".to_string())) // logged ONLY
        // request_context: input only — no `sys`.
        .request_context("input", "doc", Value::String("x".to_string()))
        .build();
    let mut authorizer = Authorizer::new(lower_two_group(
        r#"permit ( principal, action == Svc::Action::"Read", resource )
           when { context.sys.mode == "admin" };"#,
    ));
    let resp = authorizer.is_authorized(&event).expect("decision point");
    assert_eq!(
        resp.decision(),
        Decision::Deny,
        "a logged-only field must be invisible to the Cedar request (reads request_context)"
    );
}

// ─── entity ids containing escape chars (`"` / `\`) ──────────────────
//
// The entity store is keyed by the Cedar uid *literal* (`Ns::Ty::"id"`, with
// `"`/`\` in the id escaped) — the form the `.log` `entities(...)` envelope and
// `EventBuilder::entity` write, and the form Cedar itself canonicalizes to. A
// lookup that reconstructs the key from a parsed `(ty, id)` must escape
// identically (`entity_uid_string`), or an id containing `"`/`\` misses the
// store: the provider argument / temporal read silently becomes `Null` while
// Cedar reads the attribute correctly — a Cedar-vs-extension asymmetry. These
// pin that every path agrees for an escaped id (`a"b`). Schema `Svc::User` has
// `{ id, dept }`.

/// A `Check::Dept(principal.dept)` guardrail policy over the two-clause
/// forbid/permit shape, for the provider-side escaped-id test.
const ESCAPED_ID_PROVIDER_POLICY: &str = r#"
    forbid ( principal, action == Svc::Action::"Read", resource )
    when guardrails { Check::Dept(principal.dept).blocked == true };
    permit ( principal, action == Svc::Action::"Read", resource );
"#;

fn dept_provider_service() -> ServiceSchema {
    let providers = ProviderDeclarations::from_json(
        r#"{ "availableProviders": { "Check::Dept": {
              "argumentTypes": [ { "paramType": "string" } ],
              "outputType": { "paramType": "record",
                              "fields": { "blocked": { "paramType": "bool" } },
                              "required": ["blocked"] } } } }"#,
    )
    .expect("providers json");
    ServiceSchema::builder()
        .providers(providers)
        .build()
        .expect("service schema")
}

#[test]
fn replay_escaped_entity_id_provider_arg_resolves_not_null() {
    // A `.log` line whose principal id contains an escaped quote (`a\"b`). The
    // provider argument `principal.dept` must resolve to the supplied `"banned"`
    // — before the canonical-key fix it was `Null` (store keyed by the escaped
    // slice, lookup reconstructed the key unescaped → miss).
    let policies = LoweredPolicySet::from_str(
        ESCAPED_ID_PROVIDER_POLICY,
        &dept_provider_service(),
        &PolicySchema::from_cedarschema_str(&schema_src()).expect("policy schema"),
    )
    .expect("lower");
    let log = r#"@0 scope(principal: Svc::User::"a\"b", resource: Svc::Gateway::"gw1") entities(Svc::User::"a\"b": { id: "a\"b", dept: "banned" }) Svc::Action::"Read"::request(input: { doc: "x" }, callerPrincipal: Svc::User::"a\"b", callerResource: Svc::Gateway::"gw1", requestId: "u1")"#;
    let trace = parse_trace(log).expect("parse");

    let seen = std::sync::Arc::new(Mutex::new(Vec::new()));
    let mut authorizer = Authorizer::builder(policies)
        .provider_resolver(CapturingResolver { seen: seen.clone() })
        .build()
        .expect("authorizer builds");
    authorizer.is_authorized(&trace[0]).expect("decision point");
    assert_eq!(
        seen.lock().unwrap().as_slice(),
        &[Value::String("banned".to_string())],
        "provider must receive the escaped-id principal's dept, not Null"
    );
}

#[test]
fn replay_escaped_entity_id_pure_cedar_reads_attribute() {
    // Parity control: pure Cedar reads the same escaped-id attribute (it always
    // did — Cedar canonicalizes the uid). This is the "correct" side the
    // provider path must now match.
    let policy = r#"permit ( principal, action == Svc::Action::"Read", resource )
                    when { principal.dept == "banned" };"#;
    let log = r#"@0 scope(principal: Svc::User::"a\"b", resource: Svc::Gateway::"gw1") entities(Svc::User::"a\"b": { id: "a\"b", dept: "banned" }) Svc::Action::"Read"::request(input: { doc: "x" }, callerPrincipal: Svc::User::"a\"b", callerResource: Svc::Gateway::"gw1", requestId: "u1")"#;
    let out = replay_log(lower(policy), log).expect("replay");
    assert!(
        out.trim().ends_with("true"),
        "pure Cedar reads the escaped-id attribute → permit: {out}"
    );
}

#[test]
fn production_escaped_entity_id_pure_cedar_reads_attribute() {
    // The `EventBuilder` production path (not just `.log` replay): an escaped
    // quote in the principal uid must round-trip so Cedar reads the attribute.
    // Before the fix, `uid_to_value` kept the backslash in `Value::Entity.id`,
    // which `value_to_uid_string` then re-escaped, building a mangled
    // `Svc::User::"a\\\"b"` — Cedar errored "does not have the attribute".
    let policy = r#"permit ( principal, action == Svc::Action::"Read", resource )
                    when { principal.dept == "banned" };"#;
    let uid = "Svc::User::\"a\\\"b\""; // Svc::User::"a\"b"
    let event = Event::builder("Svc::Action::Read", "request")
        .principal(uid)
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .entity(
            uid,
            [
                ("id", Value::String("a\"b".to_string())),
                ("dept", Value::String("banned".to_string())),
            ],
        )
        .build();
    let (decision, errs) = decide_on(policy, &event);
    assert_eq!(
        decision,
        Decision::Allow,
        "escaped-id principal attribute must resolve on the production path; errs: {errs}"
    );
    assert_eq!(errs, "", "no mangled-uid evaluation error");
}

#[test]
fn replay_backslash_entity_id_provider_arg_resolves() {
    // The other escape `entity_uid_string` handles: a literal backslash in the
    // id (`a\b`). Store-keyed and looked up through the same canonical form, so
    // the provider argument resolves rather than becoming `Null`.
    let policies = LoweredPolicySet::from_str(
        ESCAPED_ID_PROVIDER_POLICY,
        &dept_provider_service(),
        &PolicySchema::from_cedarschema_str(&schema_src()).expect("policy schema"),
    )
    .expect("lower");
    // `.log` literal for id `a\b`: Svc::User::"a\\b".
    let log = r#"@0 scope(principal: Svc::User::"a\\b", resource: Svc::Gateway::"gw1") entities(Svc::User::"a\\b": { id: "a\\b", dept: "banned" }) Svc::Action::"Read"::request(input: { doc: "x" }, callerPrincipal: Svc::User::"a\\b", callerResource: Svc::Gateway::"gw1", requestId: "u1")"#;
    let trace = parse_trace(log).expect("parse");
    let seen = std::sync::Arc::new(Mutex::new(Vec::new()));
    let mut authorizer = Authorizer::builder(policies)
        .provider_resolver(CapturingResolver { seen: seen.clone() })
        .build()
        .expect("authorizer builds");
    authorizer.is_authorized(&trace[0]).expect("decision point");
    assert_eq!(
        seen.lock().unwrap().as_slice(),
        &[Value::String("banned".to_string())],
        "backslash-id principal's dept must resolve, not Null"
    );
}

/// Schema whose `User` has an **entity-typed** attribute (`manager: User`), for
/// the escaped-id entity-value test below.
const MANAGER_SCHEMA: &str = r#"
    namespace Svc {
      entity Gateway;
      entity User = { manager: User };
      action "Read" appliesTo {
        principal: [User], resource: [Gateway],
        context: { input: { doc: String } }
      };
    }
"#;

#[test]
fn replay_escaped_id_entity_typed_attribute_value_resolves() {
    // An entity-typed *attribute value* whose id is escaped (`principal.manager
    // == Svc::User::"a\"b"`). `value_to_expr` builds the Cedar attribute value;
    // before routing it through `entity_uid_string` it hand-rolled an unescaped
    // literal (`Svc::User::"a"b"`), which `parse_uid` swallowed into the
    // `unknown` sentinel → the comparison silently mismatched. Now it resolves,
    // so the identity comparison holds.
    let policy = r#"permit ( principal, action == Svc::Action::"Read", resource )
                    when { principal.manager == Svc::User::"a\"b" };"#;
    let policies = LoweredPolicySet::from_str(
        policy,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(MANAGER_SCHEMA).expect("policy schema"),
    )
    .expect("lower");
    // The principal `boss` has `manager = Svc::User::"a\"b"` (escaped id).
    let log = r#"@0 scope(principal: Svc::User::"boss", resource: Svc::Gateway::"gw1") entities(Svc::User::"boss": { manager: Svc::User::"a\"b" }, Svc::User::"a\"b": { manager: Svc::User::"a\"b" }) Svc::Action::"Read"::request(input: { doc: "x" }, callerPrincipal: Svc::User::"boss", callerResource: Svc::Gateway::"gw1", requestId: "u1")"#;
    let out = replay_log(policies, log).expect("replay");
    assert!(
        out.trim().ends_with("true"),
        "escaped-id entity-typed attribute value must compare equal → permit: {out}"
    );
}

// ─── entity ids with control / whitespace chars (Cedar-canonical escaping) ──
//
// The Cedar fuzz corpus uses adversarial entity ids containing control chars
// and whitespace (e.g. `a::"=\u{e}"`, `a::"wDebian "`). Dogwood must render
// these in Cedar's canonical `\u{..}` form (via `entity_uid_string` =
// `escape_debug`) so the uid round-trips through `EntityUid::from_str` and its
// attributes resolve. Before the fix, escaping only `"`/`\` left control chars
// raw, so `EntityUid::from_str` rejected the literal → fail-closed Deny and a
// silently-unresolved attribute read.

#[test]
fn control_char_id_attribute_resolves_via_production_path() {
    // A principal whose id contains a control char (`\u{e}`). The uid is passed
    // in Cedar-canonical form (`\u{..}` escaped) — the form a caller building
    // from a Cedar `{type,id}` produces via the uid escaper, and the form
    // `EventBuilder::entity` keys on. Its `dept` attribute must resolve so the
    // permit fires — proving the canonical escape reaches the Cedar authorizer
    // through the `EventBuilder` production path.
    //
    // (The builder takes the uid as an already-canonical literal string; it does
    // not itself normalize a raw-control-char argument. A caller with a decoded
    // id should render it via the canonical escaper first — as the Cedar-corpus
    // probe does — rather than embedding raw control bytes in the string.)
    let policy = r#"permit ( principal, action == Svc::Action::"Read", resource )
                    when { principal.dept == "eng" };"#;
    // Canonical literal for id `a\u{e}b` (the `\u{e}` written as an escape).
    let uid = "Svc::User::\"a\\u{e}b\"";
    let event = Event::builder("Svc::Action::Read", "request")
        .principal(uid)
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .entity(
            uid,
            [
                ("id", Value::String("a\u{e}b".to_string())),
                ("dept", Value::String("eng".to_string())),
            ],
        )
        .build();
    let (decision, errs) = decide_on(policy, &event);
    assert_eq!(
        decision,
        Decision::Allow,
        "control-char-id principal attribute must resolve (canonical escaping); errs: {errs}"
    );
    assert_eq!(errs, "", "no non-normalized-uid evaluation error");
}

#[test]
fn control_char_id_via_log_envelope() {
    // Same, end to end through the `.log` `entities(...)` envelope: the id is
    // written in Cedar-canonical `\u{..}` form and must parse, key the store,
    // and resolve the attribute.
    let policy = r#"permit ( principal, action == Svc::Action::"Read", resource )
                    when { principal.dept == "eng" };"#;
    let log = "@0 scope(principal: Svc::User::\"a\\u{e}b\", resource: Svc::Gateway::\"gw1\") \
        entities(Svc::User::\"a\\u{e}b\": { id: \"a\\u{e}b\", dept: \"eng\" }) \
        Svc::Action::\"Read\"::request(input: { doc: \"x\" })";
    let out = replay_log(lower(policy), log).expect("replay");
    assert!(
        out.trim().ends_with("true"),
        "control-char id in the .log envelope must resolve its attribute → permit: {out}"
    );
}

#[test]
fn structured_setters_take_decoded_ids_verbatim() {
    // The structured `(ty, id)` setters — `principal_for` / `resource_for` /
    // `entity_for` — take the DECODED id and escape it canonically exactly once
    // at the Cedar boundary. So a caller with a raw id containing a control char
    // (`\u{e}`) supplies it verbatim, with NO hand-escaping and NO double-escape
    // risk (the footgun of the literal-taking `principal`/`entity`, which key on
    // an already-escaped string). Same decision as
    // `control_char_id_attribute_resolves_via_production_path`, but the id never
    // appears in escaped form in the caller's code.
    let policy = r#"permit ( principal == Svc::User::"a\u{e}b", action == Svc::Action::"Read", resource )
                    when { principal.dept == "eng" };"#;
    let raw_id = "a\u{e}b"; // decoded: a, U+000E, b — never hand-escaped below
    let event = Event::builder("Svc::Action::Read", "request")
        .principal_for("Svc::User", raw_id)
        .resource_for("Svc::Gateway", "gw1")
        .field("input", "doc", Value::String("x".to_string()))
        .entity_for(
            "Svc::User",
            raw_id,
            [
                ("id", Value::String(raw_id.to_string())),
                ("dept", Value::String("eng".to_string())),
            ],
        )
        .build();
    let (decision, errs) = decide_on(policy, &event);
    assert_eq!(
        decision,
        Decision::Allow,
        "structured setters must canonicalize a decoded control-char id and resolve \
         both identity scope and attribute; errs: {errs}"
    );
    assert_eq!(errs, "", "no non-normalized-uid evaluation error");
}

#[test]
fn control_char_action_id_renders_canonically() {
    // The decision event's ACTION id is rendered to a Cedar uid at decision time
    // (`qualified_action_uid`); it must be canonically escaped too, or a control-
    // char action id fails closed ("needs to be normalized") — the dominant
    // residual when replaying Cedar-corpus requests. The schema declares an
    // action whose id contains `\u{e}`; a policy scoping it must fire.
    let schema = r#"
        namespace Svc {
          entity Gateway;
          entity User;
          action "a\u{e}b" appliesTo {
            principal: [User], resource: [Gateway],
            context: { input: { doc: String } }
          };
        }
    "#;
    let policies = LoweredPolicySet::from_str(
        "permit ( principal, action == Svc::Action::\"a\\u{e}b\", resource );",
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(schema).expect("policy schema"),
    )
    .expect("lower");
    // A `.log` event for that action (canonical `\u{e}` id).
    let log = "@0 scope(principal: Svc::User::\"alice\", resource: Svc::Gateway::\"gw1\") \
        Svc::Action::\"a\\u{e}b\"::request(input: { doc: \"x\" })";
    let out = replay_log(policies, log).expect("replay");
    assert!(
        out.trim().ends_with("true"),
        "control-char action id must render canonically and match the action scope → permit: {out}"
    );
}

#[test]
fn structured_action_id_with_interior_colons_matches_scope() {
    // Cedar permits ANY string as an action id (an `EntityId` is opaque), so an
    // id may itself contain `::`. `Event::builder` recovers the id from a
    // combined `Ns::Action::id` string by splitting on the LAST `::`, so such an
    // id is mangled into the namespace before it is ever escaped. The structured
    // `Event::builder_for(namespace, id, kind)` (Cedar's `from_type_name_and_id`
    // shape) stores the id verbatim, so it round-trips. The schema declares an
    // action whose id is `a::b`; a policy scoping it must fire via `builder_for`
    // and (as the negative control) NOT via `builder`.
    let schema = r#"
        namespace Svc {
          entity Gateway;
          entity User;
          action "a::b" appliesTo {
            principal: [User], resource: [Gateway],
            context: { input: { doc: String } }
          };
        }
    "#;
    let lower = || {
        LoweredPolicySet::from_str(
            "permit ( principal, action == Svc::Action::\"a::b\", resource );",
            &ServiceSchema::defaults(),
            &PolicySchema::from_cedarschema_str(schema).expect("policy schema"),
        )
        .expect("lower")
    };
    let base = |b: Event| {
        let mut authorizer = Authorizer::new(lower());
        authorizer.is_authorized(&b).expect("decision").decision()
    };

    // Structured: the id `a::b` is a single verbatim component → renders to
    // `Svc::Action::"a::b"` and matches the action scope.
    let structured = Event::builder_for(&["Svc", "Action"], "a::b", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .request_context("input", "doc", Value::String("x".to_string()))
        .build();
    assert_eq!(
        base(structured),
        Decision::Allow,
        "builder_for must preserve an action id containing `::` and match its scope"
    );

    // Negative control: the same identity via the combined-string `builder`
    // splits on the last `::`, so the id becomes `b` (namespace absorbs `a`) and
    // the action scope does NOT match → Deny. This is exactly the residual the
    // structured constructor closes.
    let combined = Event::builder("Svc::Action::a::b", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .request_context("input", "doc", Value::String("x".to_string()))
        .build();
    assert_eq!(
        base(combined),
        Decision::Deny,
        "combined-string builder mangles an interior `::` id (negative control)"
    );
}

// ─── entity hierarchy (`in` / memberOf) via supplied parents ─────────
//
// An entity's DIRECT parents feed Cedar's hierarchy so `principal in Group`
// resolves (Cedar computes the transitive ancestor closure). Parents are
// supplied via `EventBuilder::entity_parents` or the `.log` `entities(...)`
// envelope's `{ … } in [ … ]` clause — orthogonal to attributes. These pin the
// end-to-end capability the Cedar-corpus conjunction fuzzer needs.

/// A schema whose `User` can be a member of a `Group` (`memberOf [Group]`),
/// enabling `principal in Group::"…"` policies.
const GROUP_SCHEMA: &str = r#"
    namespace Svc {
      entity Gateway;
      entity Group;
      entity User in [Group];
      action "Read" appliesTo {
        principal: [User], resource: [Gateway],
        context: { input: { doc: String } }
      };
    }
"#;

fn decide_group(policy: &str, event: &Event) -> (Decision, String) {
    let policies = LoweredPolicySet::from_str(
        policy,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(GROUP_SCHEMA).expect("policy schema"),
    )
    .expect("lower");
    let mut authorizer = Authorizer::new(policies);
    let resp = authorizer.is_authorized(event).expect("decision");
    let errs = resp.diagnostics().errors().collect::<Vec<_>>().join(" | ");
    (resp.decision(), errs)
}

/// A `Read` request by `alice`, optionally a direct member of the given groups.
fn membership_event(parents: &[&str]) -> Event {
    Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .entity_parents("Svc::User::\"alice\"", parents.iter().copied())
        .build()
}

#[test]
fn principal_in_group_allows_when_member() {
    // `alice in [admins]` → the `principal in Group::"admins"` scope matches.
    let (decision, errs) = decide_group(
        r#"permit ( principal in Svc::Group::"admins", action == Svc::Action::"Read", resource );"#,
        &membership_event(&["Svc::Group::\"admins\""]),
    );
    assert_eq!(
        decision,
        Decision::Allow,
        "member of admins → permit; errs: {errs}"
    );
    assert_eq!(errs, "");
}

#[test]
fn principal_in_group_denies_when_not_member() {
    // No parents supplied → `alice` is not in `admins` → the scope does not
    // match → deny-by-default. This is the discriminating control: same policy,
    // membership is the only variable.
    let (decision, errs) = decide_group(
        r#"permit ( principal in Svc::Group::"admins", action == Svc::Action::"Read", resource );"#,
        &membership_event(&[]),
    );
    assert_eq!(decision, Decision::Deny, "non-member → deny; errs: {errs}");
}

#[test]
fn principal_in_group_denies_when_member_of_other_group() {
    // Member of a DIFFERENT group → still not in `admins` → deny. Rules out a
    // "any parent matches" bug.
    let (decision, _errs) = decide_group(
        r#"permit ( principal in Svc::Group::"admins", action == Svc::Action::"Read", resource );"#,
        &membership_event(&["Svc::Group::\"eng\""]),
    );
    assert_eq!(decision, Decision::Deny, "member of eng, not admins → deny");
}

#[test]
fn membership_is_transitive_through_a_group_hierarchy() {
    // alice in [eng]; eng in [admins]. Cedar computes the transitive closure, so
    // `principal in admins` holds even though alice's DIRECT parent is only eng.
    // Supplied via the `.log` envelope's `in [ … ]` clause on each entity.
    // Needs a schema where a Group may be a member of a Group (`Group in [Group]`).
    let group_hierarchy_schema = r#"
        namespace Svc {
          entity Gateway;
          entity Group in [Group];
          entity User in [Group];
          action "Read" appliesTo {
            principal: [User], resource: [Gateway],
            context: { input: { doc: String } }
          };
        }
    "#;
    let policy =
        r#"permit ( principal in Svc::Group::"admins", action == Svc::Action::"Read", resource );"#;
    let policies = LoweredPolicySet::from_str(
        policy,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(group_hierarchy_schema).expect("policy schema"),
    )
    .expect("lower");
    let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::Group::"admins": {}, Svc::Group::"eng": {} in [Svc::Group::"admins"], Svc::User::"alice": {} in [Svc::Group::"eng"]) Svc::Action::"Read"::request(input: { doc: "x" })"#;
    let out = replay_log(policies, log).expect("replay");
    assert!(
        out.trim().ends_with("true"),
        "transitive membership (alice ∈ eng ∈ admins) must satisfy `in admins`: {out}"
    );
}

#[test]
fn log_envelope_membership_drives_decision_both_ways() {
    // End-to-end via the `.log` `in [ … ]` clause: tp0 supplies the membership
    // (Allow), tp1 omits it (Deny) — proving the parsed per-event hierarchy
    // reaches the Cedar authorizer and differs per line.
    let policy =
        r#"permit ( principal in Svc::Group::"admins", action == Svc::Action::"Read", resource );"#;
    let policies = LoweredPolicySet::from_str(
        policy,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(GROUP_SCHEMA).expect("policy schema"),
    )
    .expect("lower");
    let log = r#"
@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::Group::"admins": {}, Svc::User::"alice": {} in [Svc::Group::"admins"]) Svc::Action::"Read"::request(input: { doc: "x" })
@1 scope(principal: Svc::User::"bob", resource: Svc::Gateway::"gw1") entities(Svc::Group::"admins": {}, Svc::User::"bob": {}) Svc::Action::"Read"::request(input: { doc: "y" })
"#;
    let out = replay_log(policies, log).expect("replay");
    let verdicts: Vec<bool> = out.lines().map(|l| l.ends_with("true")).collect();
    assert_eq!(
        verdicts,
        vec![true, false],
        "member alice → Allow, non-member bob → Deny (per-line membership): {out}"
    );
}

#[test]
fn attributes_and_parents_compose_on_one_entity() {
    // An entity may carry both attributes and parents; both reach Cedar. Policy
    // requires membership AND an attribute — supply both via the builder.
    let schema = r#"
        namespace Svc {
          entity Gateway;
          entity Group;
          entity User in [Group] = { dept: String };
          action "Read" appliesTo {
            principal: [User], resource: [Gateway],
            context: { input: { doc: String } }
          };
        }
    "#;
    let policies = LoweredPolicySet::from_str(
        r#"permit ( principal in Svc::Group::"admins", action == Svc::Action::"Read", resource )
           when { principal.dept == "eng" };"#,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(schema).expect("policy schema"),
    )
    .expect("lower");
    let event = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "doc", Value::String("x".to_string()))
        .entity(
            "Svc::User::\"alice\"",
            [("dept", Value::String("eng".to_string()))],
        )
        .entity_parents("Svc::User::\"alice\"", ["Svc::Group::\"admins\""])
        .build();
    let mut authorizer = Authorizer::new(policies);
    let resp = authorizer.is_authorized(&event).expect("decision");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "attrs + parents on one entity both reach Cedar (member AND dept==eng)"
    );
}

#[test]
fn structured_attrs_and_parents_compose_via_setters() {
    // The structured analog of `attributes_and_parents_compose_on_one_entity`:
    // `entity_for` and `parents_for` key the SAME entity by `(ty, id)` (so both
    // land on one `EntityRecord`), and each parent is given as its own `(ty, id)`
    // pair — no uid literal is spelled out. Both attribute and membership must
    // still reach Cedar. This pins that the structured setters key the store
    // identically to the literal-taking ones (same canonical key) and that
    // parents built from components resolve.
    let schema = r#"
        namespace Svc {
          entity Gateway;
          entity Group;
          entity User in [Group] = { dept: String };
          action "Read" appliesTo {
            principal: [User], resource: [Gateway],
            context: { input: { doc: String } }
          };
        }
    "#;
    let policies = LoweredPolicySet::from_str(
        r#"permit ( principal in Svc::Group::"admins", action == Svc::Action::"Read", resource )
           when { principal.dept == "eng" };"#,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(schema).expect("policy schema"),
    )
    .expect("lower");
    let event = Event::builder("Svc::Action::Read", "request")
        .principal_for("Svc::User", "alice")
        .resource_for("Svc::Gateway", "gw1")
        .field("input", "doc", Value::String("x".to_string()))
        .entity_for(
            "Svc::User",
            "alice",
            [("dept", Value::String("eng".to_string()))],
        )
        .parents_for("Svc::User", "alice", [("Svc::Group", "admins")])
        .build();
    let mut authorizer = Authorizer::new(policies);
    let resp = authorizer.is_authorized(&event).expect("decision");
    let errs = resp.diagnostics().errors().collect::<Vec<_>>().join(" | ");
    assert_eq!(
        resp.decision(),
        Decision::Allow,
        "structured entity_for + parents_for must both reach Cedar (member AND dept==eng); errs: {errs}"
    );
    assert_eq!(errs, "");
}
