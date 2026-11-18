//! `LoweredPolicySet::decision_request`: the Cedar request and entity store a
//! decision is made with, before its temporal leaves and providers are bound.
//!
//! The hook exists so that an engine that partially evaluates the policies (the
//! DSQL engine's leaf masking) uses the crate's own construction rather than a
//! copy that can drift (a copy rendered a `null` as the empty string after the
//! crate stopped doing so). Each case compares the hook with what the
//! authorizer actually hands its policy engine.

use std::sync::{Arc, Mutex};

use dogwood_language::cedar::{Entities, PolicySet, Request, Schema};
use dogwood_language::{
    AuthorizationDecision, AuthorizationRequest, Authorizer, CedarPolicyEngine, Decision, Event,
    LoweredPolicySet, PolicyEngine, PolicySchema, ServiceSchema, parse_trace,
};

const SCHEMA: &str = r#"
namespace Svc {
  entity Group;
  entity User in [Group] = { dept?: String, level?: Long };
  entity Gateway;
  type In = { doc: String, tag?: String };
  action "Read" appliesTo { principal: [User], resource: [Gateway], context: { input: In, system?: { hour: Long } } };
}
"#;

const POLICY: &str = r#"
permit (principal, action == Svc::Action::"Read", resource)
when { principal.dept == "eng" }
when temporal { formerly within 1h Svc::Action::"Read"::request{} };
"#;

fn lower() -> LoweredPolicySet {
    LoweredPolicySet::from_str(
        POLICY,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(SCHEMA).unwrap(),
    )
    .unwrap()
}

/// A policy engine that records what it is asked, and decides as Cedar does.
struct Recorder {
    inner: CedarPolicyEngine,
    seen: Arc<Mutex<Vec<(Request, Entities)>>>,
}

impl PolicyEngine for Recorder {
    fn prepare(
        &mut self,
        policies: &PolicySet,
        schema: &Schema,
    ) -> Result<(), dogwood_language::Error> {
        self.inner.prepare(policies, schema)
    }

    fn is_authorized(&self, request: AuthorizationRequest<'_>) -> AuthorizationDecision {
        self.seen
            .lock()
            .unwrap()
            .push((request.request.clone(), request.entities.clone()));
        self.inner.is_authorized(request)
    }
}

const TRACE: &str = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::Group::"eng": {}, Svc::User::"alice": { dept: "eng", level: null } in [Svc::Group::"eng"]) request_context(input: { doc: "x", tag: null }, system: { hour: 9 }) Svc::Action::"Read"::request(input: { doc: "x", tag: null }, callerPrincipal: Svc::User::"alice", callerResource: Svc::Gateway::"gw1")
@1 scope(principal: Svc::User::"bob", resource: Svc::Gateway::"gw1") request_context(input: { doc: "y" }) Svc::Action::"Read"::request(input: { doc: "y" }, callerPrincipal: Svc::User::"bob", callerResource: Svc::Gateway::"gw1")"#;

/// The hook's request has the decision's principal, action, resource and request
/// context, without the hoisted leaves; its entity store is the decision's.
#[test]
fn the_hook_builds_what_the_authorizer_hands_its_policy_engine() {
    let seen = Arc::new(Mutex::new(Vec::new()));
    let mut a = Authorizer::builder(lower())
        .policy_engine(Recorder {
            inner: CedarPolicyEngine::new(),
            seen: seen.clone(),
        })
        .build()
        .unwrap();
    let events = parse_trace(TRACE).unwrap();
    let decisions: Vec<Decision> = events
        .iter()
        .map(|e| a.is_authorized(e).unwrap().decision())
        .collect();
    assert_eq!(decisions, vec![Decision::Allow, Decision::Deny]);

    let hook = lower();
    let seen = seen.lock().unwrap();
    assert_eq!(seen.len(), 2);
    for (event, (request, entities)) in events.iter().zip(seen.iter()) {
        let (r, e) = hook.decision_request(event).expect("the hook builds");
        assert_eq!(r.principal(), request.principal());
        assert_eq!(r.action(), request.action());
        assert_eq!(r.resource(), request.resource());
        assert_eq!(e, *entities, "the entity store is the decision's");
        let ctx = r.context().expect("a concrete context");
        let full = request.context().expect("a concrete context");
        // The hook's context is the decision's, without the hoisted leaves.
        let leaves: Vec<String> = hook.temporal_fields().map(|f| f.id.to_string()).collect();
        assert!(!leaves.is_empty());
        for leaf in &leaves {
            assert!(ctx.get(leaf).is_none(), "the hook binds no leaf ({leaf})");
            assert!(full.get(leaf).is_some(), "the decision binds {leaf}");
        }
        for group in ["input", "system"] {
            assert_eq!(
                ctx.get(group).map(|v| v.to_string()),
                full.get(group).map(|v| v.to_string()),
                "{group}"
            );
        }
    }
    // The free function, given the augmented schema, builds the same.
    for event in &events {
        let (r1, e1) = hook.decision_request(event).unwrap();
        let (r2, e2) = dogwood_language::decision_request(event, hook.cedar_schema()).unwrap();
        assert_eq!(
            (r1.principal(), r1.action(), r1.resource()),
            (r2.principal(), r2.action(), r2.resource())
        );
        assert_eq!(e1, e2);
    }
    // A `null` is absent in both: `context.input` has no `tag`.
    let (r, _) = hook.decision_request(&events[0]).unwrap();
    let input = r.context().unwrap().get("input").unwrap().to_string();
    assert!(!input.contains("tag"), "{input}");
}

/// The hook fails as the decision fails closed: a decision event with no
/// principal has no request.
#[test]
fn the_hook_fails_where_the_decision_fails_closed() {
    let event = Event::builder("Svc::Action::Read", "request")
        .resource("Svc::Gateway::\"gw1\"")
        .build();
    let err = lower().decision_request(&event).expect_err("no principal");
    assert!(err.contains("principal"), "{err}");
}
