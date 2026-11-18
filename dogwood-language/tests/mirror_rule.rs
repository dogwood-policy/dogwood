//! The strict mirror rule (semantics review F1.2, critical; `dogwood-lean`,
//! `Dogwood.Spec.Conformance.Mirrored`).
//!
//! A logged field that mirrors the request (the field of a symmetric pin, which
//! is a pin to the request's principal, its resource, or a context attribute,
//! and an unpinned `callerPrincipal` or `callerResource`) must hold the
//! request's value when the event has one, and must be absent when it has none.
//! Every pinned field must be logged. An event that breaks the rule is not
//! ingested: a history event is rejected ([`Authorizer::submit`] returns the
//! [`Rejection`]), and a decision event's decision fails closed.
//!
//! Cases (a) to (d) are those of `Dogwood.Examples.MirrorRule` in `dogwood-lean`.
//! Each gives the verdicts of Dogwood_Language 1.1 (no check), of the earlier
//! rule ([`MirrorRule::Current`]) and of the strict rule (the default), and fails
//! on 1.1, unless it says it pins a verdict 1.1 already gave. The renamed-pin
//! cases give the verdicts they test.

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, MirrorRule, PolicySchema, Rejection, ServiceSchema,
    parse_trace,
};

const SCHEMA: &str = r#"
namespace Drupe {
  entity OAuthUser = { id: String };
  entity Gateway;
  type In = { doc: String };
  action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: In } };
  action "Login" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: In } };
}
"#;

/// The `request` kind carries the principal pin; the `response` kind declares
/// `callerPrincipal` without pinning it, so the pin is not universal (review Q1
/// (b), restated for a schema whose signatures are per kind: the grammar
/// declares every kind for every action).
const PARTIAL: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource: resourceType(A),
    requestId: String,
}
event <A>::response {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource: resourceType(A),
    requestId: String,
}
"#;

fn lower(events: &str, policy: &str) -> LoweredPolicySet {
    let service = ServiceSchema::builder()
        .event_schema_str(events)
        .build()
        .expect("service schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema parses");
    LoweredPolicySet::from_str(policy, &service, &schema).expect("policy lowers")
}

const A: Option<bool> = Some(true);
const D: Option<bool> = Some(false);
const N: Option<bool> = None;

/// The verdicts at each event of `log` under `rule`, global or partitioned.
fn run(
    events: &str,
    policy: &str,
    rule: Option<MirrorRule>,
    partitioned: bool,
    log: &str,
) -> Vec<Option<bool>> {
    let mut builder = Authorizer::builder(lower(events, policy));
    if let Some(rule) = rule {
        builder = builder.mirror_rule(rule);
    }
    if partitioned {
        builder = builder.partition_temporal();
    }
    let mut a = builder.build().expect("authorizer builds");
    parse_trace(log)
        .expect("trace parses")
        .iter()
        .map(|e| a.is_authorized(e).map(|r| r.decision() == Decision::Allow))
        .collect()
}

/// The default rule's verdicts, global and partitioned (they must agree).
fn strict(events: &str, policy: &str, log: &str) -> Vec<Option<bool>> {
    let global = run(events, policy, None, false, log);
    let partitioned = run(events, policy, None, true, log);
    assert_eq!(global, partitioned, "global and partitioned modes agree");
    global
}

fn read(ts: u32, who: &str) -> String {
    format!(
        r#"@{ts} scope(principal: Drupe::OAuthUser::"{who}", resource: Drupe::Gateway::"gw1") request_context(input: {{ doc: "d" }}) Drupe::Action::"Read"::request(input: {{ doc: "d" }}, callerPrincipal: Drupe::OAuthUser::"{who}", callerResource: Drupe::Gateway::"gw1", requestId: "r{ts}")"#
    )
}

/// A scope-less event that logs `victim` as its caller.
fn forged(ts: u32, action: &str, kind: &str, victim: &str) -> String {
    format!(
        r#"@{ts} Drupe::Action::"{action}"::{kind}(input: {{ doc: "d" }}, callerPrincipal: Drupe::OAuthUser::"{victim}", callerResource: Drupe::Gateway::"gw1", requestId: "f{ts}")"#
    )
}

/// `forbid Read when count(t) where formerly 1h (Read::request{} && tp(t)) > 3`.
const RATE_LIMIT: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource);
forbid (principal, action == Drupe::Action::"Read", resource)
when temporal { (count for (t: Timepoint). where formerly within 1h (Drupe::Action::"Read"::request{} && tp(t))) > 3 };
"#;

fn forged_rate_limit() -> String {
    [
        forged(1, "Read", "request", "alice"),
        forged(2, "Read", "request", "alice"),
        forged(3, "Read", "request", "alice"),
        forged(4, "Read", "response", "alice"),
        read(100, "alice"),
    ]
    .join("\n")
}

/// Q1 (a), the default schema (universal `callerPrincipal = principal`): Mallory's
/// scope-less requests logging `callerPrincipal: alice` fill Alice's rate limit.
/// 1.1 counted them (DENY); the strict rule rejects them (ALLOW). The forged
/// decision events fail closed either way.
#[test]
fn q1a_forged_history_under_the_default_schema_is_rejected() {
    let log = forged_rate_limit();
    let events = dogwood_language::DEFAULT_EVENT_SCHEMA;
    assert_eq!(strict(events, RATE_LIMIT, &log), vec![D, D, D, N, A]);
    assert_eq!(
        run(events, RATE_LIMIT, Some(MirrorRule::Current), false, &log),
        vec![D, D, D, N, D]
    );
    assert_eq!(
        run(events, RATE_LIMIT, Some(MirrorRule::Unchecked), false, &log),
        vec![D, D, D, N, D]
    );
}

/// Q1 (b), the critical case: the pin is declared on `request` only, so it is not
/// universal, and the earlier rule checked nothing for a scope-less event. Pin
/// injection still appends `callerPrincipal: principal` to the rate limit's
/// predicate, and the forged events match it: DENY under 1.1 and under the
/// earlier rule; ALLOW under the strict rule.
#[test]
fn q1b_forged_history_under_a_pin_that_is_not_universal_is_rejected() {
    let log = forged_rate_limit();
    assert!(
        lower(PARTIAL, RATE_LIMIT).partition_keys().is_empty(),
        "the pin is not universal"
    );
    assert_eq!(strict(PARTIAL, RATE_LIMIT, &log), vec![D, D, D, N, A]);
    assert_eq!(
        run(PARTIAL, RATE_LIMIT, Some(MirrorRule::Current), false, &log),
        vec![D, D, D, N, D]
    );
    assert_eq!(
        run(
            PARTIAL,
            RATE_LIMIT,
            Some(MirrorRule::Unchecked),
            false,
            &log
        ),
        vec![D, D, D, N, D]
    );
}

/// Q1 (c), the cost of the rule (semantics review F1.4): under a universal pin a
/// scope-less `Login::response` that logs Alice as its caller no longer counts
/// as Alice's login (ALLOW under 1.1, DENY now). With its scope attached it does
/// (ALLOW).
#[test]
fn q1c_scopeless_history_is_rejected_and_scoped_history_counts() {
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource)
        when temporal { formerly within 1h Drupe::Action::"Login"::response{} };"#;
    let events = dogwood_language::DEFAULT_EVENT_SCHEMA;
    let scopeless = [forged(1, "Login", "response", "alice"), read(100, "alice")].join("\n");
    assert_eq!(strict(events, policy, &scopeless), vec![N, D]);
    assert_eq!(
        run(events, policy, Some(MirrorRule::Current), false, &scopeless),
        vec![N, A]
    );
    assert_eq!(
        run(
            events,
            policy,
            Some(MirrorRule::Unchecked),
            false,
            &scopeless
        ),
        vec![N, A]
    );
    let scoped = [
        r#"@1 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") Drupe::Action::"Login"::response(input: { doc: "d" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw1", requestId: "l1")"#.to_string(),
        read(100, "alice"),
    ]
    .join("\n");
    assert_eq!(strict(events, policy, &scoped), vec![N, A]);
}

/// Q1 (d): a universal context pin `tenant = context.tenant` whose request path
/// is optional. Mallory's pings omit `context.tenant` but log `tenant`, so they
/// are rejected (each decision fails closed), where 1.1 never limited them.
#[test]
fn q1d_a_logged_pin_without_its_request_side_is_rejected() {
    let cedar = r#"
namespace Drupe {
  entity OAuthUser = { id: String };
  entity Gateway;
  type In = { doc: String };
  action "Ping" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: In, tenant?: String } };
}
"#;
    let events = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    pin tenant: String = context.tenant,
}
event <A>::response {
    ...inputs(A),
    callerPrincipal: principalType(A),
    pin tenant: String = context.tenant,
}
"#;
    let policy = r#"
permit (principal, action, resource);
forbid (principal, action, resource)
when temporal { (count for (t: Timepoint). where formerly within 1h tp(t)) > 3 };
"#;
    let ping = |ts: u32, ctx: &str| {
        format!(
            r#"@{ts} scope(principal: Drupe::OAuthUser::"mallory", resource: Drupe::Gateway::"gw1") request_context(input: {{ doc: "d" }}{ctx}) Drupe::Action::"Ping"::request(input: {{ doc: "d" }}, callerPrincipal: Drupe::OAuthUser::"mallory", tenant: "mallory-co")"#
        )
    };
    let lower = || {
        let service = ServiceSchema::builder()
            .event_schema_str(events)
            .build()
            .unwrap();
        LoweredPolicySet::from_str(
            policy,
            &service,
            &PolicySchema::from_cedarschema_str(cedar).unwrap(),
        )
        .unwrap()
    };
    let run = |rule: MirrorRule, ctx: &str| {
        let mut a = Authorizer::builder(lower())
            .mirror_rule(rule)
            .build()
            .unwrap();
        let log: Vec<String> = (1..=6).map(|i| ping(i, ctx)).collect();
        parse_trace(&log.join("\n"))
            .unwrap()
            .iter()
            .map(|e| a.is_authorized(e).map(|r| r.decision() == Decision::Allow))
            .collect::<Vec<_>>()
    };
    // With the tenant in the context, the limit counts the pings.
    assert_eq!(
        run(MirrorRule::Strict, r#", tenant: "mallory-co""#),
        vec![A, A, A, D, D, D]
    );
    // Without it: never limited under 1.1 and the earlier rule; rejected now.
    assert_eq!(run(MirrorRule::Unchecked, ""), vec![A; 6]);
    assert_eq!(run(MirrorRule::Current, ""), vec![A; 6]);
    assert_eq!(run(MirrorRule::Strict, ""), vec![D; 6]);
}

/// The specification's probe `runtime_caller_mismatch`: an event whose principal
/// is Bob but which logs Alice as its caller breaks both rules. Its history is
/// not Alice's, and as a decision it fails closed.
#[test]
fn a_caller_that_contradicts_the_principal_is_rejected_under_both_rules() {
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource)
        when temporal { formerly within 1h Drupe::Action::"Login"::response{} };"#;
    let mismatch = r#"@1 scope(principal: Drupe::OAuthUser::"bob", resource: Drupe::Gateway::"gw1") Drupe::Action::"Login"::response(input: { doc: "d" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw1", requestId: "l1")"#;
    let log = [mismatch.to_string(), read(100, "alice")].join("\n");
    let events = dogwood_language::DEFAULT_EVENT_SCHEMA;
    assert_eq!(strict(events, policy, &log), vec![N, D]);
    assert_eq!(
        run(events, policy, Some(MirrorRule::Current), false, &log),
        vec![N, D]
    );
    assert_eq!(
        run(events, policy, Some(MirrorRule::Unchecked), false, &log),
        vec![N, A]
    );
}

/// A principal pin under another name (`pin actor = principal` on every kind) is
/// a universal symmetric pin, whatever its field is called. It is a partition
/// key, and the mirror rule checks it. Mallory's requests that log `actor:
/// alice` fail closed and do not fill Alice's rate limit, in global and
/// partitioned evaluation.
#[test]
fn a_principal_pin_under_another_name_is_checked() {
    let events = r#"
decision event <A>::request {
    ...inputs(A),
    pin actor: principalType(A) = principal,
    requestId: String,
}
event <A>::response {
    ...inputs(A),
    pin actor: principalType(A) = principal,
    requestId: String,
}
"#;
    assert_eq!(lower(events, RATE_LIMIT).partition_keys().len(), 1);
    let read_as = |ts: u32, who: &str, actor: &str| {
        format!(
            r#"@{ts} scope(principal: Drupe::OAuthUser::"{who}", resource: Drupe::Gateway::"gw1") request_context(input: {{ doc: "d" }}) Drupe::Action::"Read"::request(input: {{ doc: "d" }}, actor: Drupe::OAuthUser::"{actor}", requestId: "r{ts}")"#
        )
    };
    let log = [
        read_as(1, "mallory", "alice"),
        read_as(2, "mallory", "alice"),
        read_as(3, "mallory", "alice"),
        read_as(4, "mallory", "alice"),
        read_as(100, "alice", "alice"),
    ]
    .join("\n");
    assert_eq!(strict(events, RATE_LIMIT, &log), vec![D, D, D, D, A]);
    assert_eq!(
        run(events, RATE_LIMIT, Some(MirrorRule::Unchecked), false, &log),
        vec![A, A, A, A, D]
    );
    let forged = parse_trace(&read_as(1, "mallory", "alice"))
        .unwrap()
        .remove(0);
    let err = lower(events, RATE_LIMIT)
        .check_event(&forged, MirrorRule::Strict)
        .expect_err("rejected");
    assert!(
        err.to_string().contains("logs `actor`"),
        "the rejection names the pinned field: {err}"
    );
}

/// A resource pin and a context pin under other names, `pin target = resource`
/// and `pin sid = context.sessionId`, are symmetric too. An event that logs
/// another value than its request's is rejected, and so is a history event that
/// logs `sid` without the context attribute. On this trace, which includes
/// rejected events, global and partitioned evaluation agree.
#[test]
fn resource_and_context_pins_under_other_names_are_checked() {
    let cedar = r#"
namespace Drupe {
  entity OAuthUser = { id: String };
  entity Gateway;
  type In = { doc: String };
  action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: In, sessionId?: String } };
  action "Login" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: In, sessionId?: String } };
}
"#;
    let events = r#"
decision event <A>::request {
    ...inputs(A),
    pin target: resourceType(A) = resource,
    pin sid: String = context.sessionId,
}
event <A>::response {
    ...inputs(A),
    pin target: resourceType(A) = resource,
    pin sid: String = context.sessionId,
}
"#;
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource)
        when temporal { formerly within 1h Drupe::Action::"Login"::response{} };"#;
    let lower = || {
        let service = ServiceSchema::builder()
            .event_schema_str(events)
            .build()
            .unwrap();
        LoweredPolicySet::from_str(
            policy,
            &service,
            &PolicySchema::from_cedarschema_str(cedar).unwrap(),
        )
        .unwrap()
    };
    assert_eq!(lower().partition_keys().len(), 2);
    // `ctx` is the request's `sessionId` (none when empty); `sid` and `target`
    // are the logged fields.
    let ev = |ts: u32, act: &str, kind: &str, ctx: &str, sid: &str, target: &str| {
        let ctx = if ctx.is_empty() {
            String::new()
        } else {
            format!(r#", sessionId: "{ctx}""#)
        };
        format!(
            r#"@{ts} scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: {{ doc: "d" }}{ctx}) Drupe::Action::"{act}"::{kind}(input: {{ doc: "d" }}, target: Drupe::Gateway::"{target}", sid: "{sid}")"#
        )
    };
    let check = |line: &str| {
        let e = parse_trace(line).unwrap().remove(0);
        lower()
            .check_event(&e, MirrorRule::Strict)
            .map_err(|r| r.to_string())
    };
    assert!(check(&ev(1, "Login", "response", "s1", "s1", "gw1")).is_ok());
    let wrong_sid = check(&ev(1, "Read", "request", "s1", "s2", "gw1")).unwrap_err();
    assert!(wrong_sid.contains("logs `sid`"), "{wrong_sid}");
    let wrong_target = check(&ev(1, "Read", "request", "s1", "s1", "gw2")).unwrap_err();
    assert!(wrong_target.contains("logs `target`"), "{wrong_target}");
    let no_context = check(&ev(1, "Login", "response", "", "s1", "gw1")).unwrap_err();
    assert!(no_context.contains("context.sessionId"), "{no_context}");

    let log = [
        ev(1, "Login", "response", "", "s1", "gw1"),
        ev(2, "Read", "request", "s1", "s1", "gw1"),
        ev(3, "Login", "response", "s1", "s1", "gw1"),
        ev(4, "Read", "request", "s1", "s2", "gw1"),
        ev(5, "Read", "request", "s1", "s1", "gw2"),
        ev(6, "Read", "request", "s1", "s1", "gw1"),
        ev(7, "Read", "request", "s2", "s2", "gw1"),
    ]
    .join("\n");
    let verdicts = |partitioned: bool| {
        let mut b = Authorizer::builder(lower());
        if partitioned {
            b = b.partition_temporal();
        }
        let mut a = b.build().unwrap();
        parse_trace(&log)
            .unwrap()
            .iter()
            .map(|e| a.is_authorized(e).map(|r| r.decision() == Decision::Allow))
            .collect::<Vec<_>>()
    };
    // The context-less login is rejected, so the first read is denied; the
    // mismatched reads fail closed; a read in session s2 sees no s2 login.
    assert_eq!(verdicts(false), vec![N, D, N, D, D, A, D]);
    assert_eq!(verdicts(true), verdicts(false));
}

/// A caller field follows its pin when a pin names it, and its namesake when
/// none does. Under `pin callerPrincipal = resource` the field must hold the
/// resource; under `pin callerPrincipal = principal.id`, an attribute pin, it
/// need only be logged; and an unpinned `callerPrincipal` next to a renamed
/// principal pin is still checked against the principal.
#[test]
fn a_caller_field_follows_its_pin_or_else_its_name() {
    let schema = |caller: &str| {
        format!(
            "decision event <A>::request {{ ...inputs(A), {caller}, requestId: String }}\n\
             event <A>::response {{ ...inputs(A), {caller}, requestId: String }}"
        )
    };
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource);"#;
    let event = |logged: &str| {
        let line = format!(
            r#"@1 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: {{ doc: "d" }}) Drupe::Action::"Read"::request(input: {{ doc: "d" }}{logged})"#
        );
        parse_trace(&line).unwrap().remove(0)
    };
    let check = |caller: &str, logged: &str| {
        lower(&schema(caller), policy)
            .check_event(&event(logged), MirrorRule::Strict)
            .map_err(|r| r.to_string())
    };

    let to_resource = "pin callerPrincipal: resourceType(A) = resource";
    assert!(check(to_resource, r#", callerPrincipal: Drupe::Gateway::"gw1""#).is_ok());
    let err = check(to_resource, r#", callerPrincipal: Drupe::Gateway::"gw2""#).unwrap_err();
    assert!(err.contains("the request's resource"), "{err}");

    let to_attribute = "pin callerPrincipal: String = principal.id";
    assert!(check(to_attribute, r#", callerPrincipal: "anyone""#).is_ok());
    let err = check(to_attribute, "").unwrap_err();
    assert!(err.contains("not logged"), "{err}");

    let renamed = "pin actor: principalType(A) = principal, callerPrincipal: principalType(A)";
    assert!(
        check(
            renamed,
            r#", actor: Drupe::OAuthUser::"alice", callerPrincipal: Drupe::OAuthUser::"alice""#
        )
        .is_ok()
    );
    let err = check(
        renamed,
        r#", actor: Drupe::OAuthUser::"alice", callerPrincipal: Drupe::OAuthUser::"bob""#,
    )
    .unwrap_err();
    assert!(err.contains("logs `callerPrincipal`"), "{err}");
}

/// `submit` reports each rejection; `is_authorized` returns `None` for a rejected
/// history event, and a fail-closed `Deny` naming the reason for a rejected
/// decision event. `check_event` gives the same answer without ingesting.
#[test]
fn rejections_are_reported() {
    let policy = r#"permit (principal, action == Drupe::Action::"Read", resource);"#;
    let events = dogwood_language::DEFAULT_EVENT_SCHEMA;
    let p = lower(events, policy);
    let history = parse_trace(&forged(1, "Login", "response", "alice"))
        .unwrap()
        .remove(0);
    let decision = parse_trace(&forged(2, "Read", "request", "alice"))
        .unwrap()
        .remove(0);
    let good = parse_trace(&read(3, "alice")).unwrap().remove(0);
    for (e, rule, ok) in [
        (&history, MirrorRule::Strict, false),
        (&history, MirrorRule::Current, true),
        (&history, MirrorRule::Unchecked, true),
        (&good, MirrorRule::Strict, true),
    ] {
        assert_eq!(p.check_event(e, rule).is_ok(), ok, "{rule}");
    }
    let mut a = Authorizer::new(lower(events, policy));
    assert_eq!(a.mirror_rule(), MirrorRule::Strict);
    let err = a.submit(&history).expect_err("rejected");
    let Rejection::Nonconforming { reason } = &err else {
        unreachable!()
    };
    assert!(
        reason.contains("callerPrincipal") && reason.contains("scope"),
        "{reason}"
    );
    let r = a
        .submit(&decision)
        .expect("a decision is answered")
        .expect("decided");
    assert_eq!(r.decision(), Decision::Deny);
    // The checks come in the specification's `decideWith` order: this forged
    // decision event has no scope, which is reported first; it does not conform
    // either, so it is not ingested.
    assert!(
        r.diagnostics()
            .errors()
            .any(|e| e == "decision event has no principal in scope"),
        "{r:?}"
    );
    assert!(a.submit(&good).unwrap().unwrap().allowed());
    // A history event that omits its pinned caller is rejected too: the
    // specification's every-pinned-field-is-logged rule.
    let bare = dogwood_language::Event::builder("Drupe::Action::Login", "response")
        .field("input", "doc", dogwood_language::Value::String("d".into()))
        .build();
    let err = a.submit(&bare).expect_err("rejected");
    assert!(
        err.to_string()
            .contains("pinned field `callerPrincipal` is not logged"),
        "{err}"
    );
}

/// The option names parse and print.
#[test]
fn mirror_rule_names() {
    for rule in [
        MirrorRule::Strict,
        MirrorRule::Current,
        MirrorRule::Unchecked,
    ] {
        assert_eq!(rule.as_str().parse::<MirrorRule>(), Ok(rule));
        assert_eq!(rule.to_string(), rule.as_str());
    }
    assert_eq!(MirrorRule::default(), MirrorRule::Strict);
    assert!("lenient".parse::<MirrorRule>().is_err());
}
