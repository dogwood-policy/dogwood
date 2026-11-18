//! `TemporalEngine::try_observe`: an engine that cannot record an event says so,
//! and the authorizer reports it (the old compiler's defect B1, report gap: a
//! history event lost when the DSQL engine's retry budget ran out, with no
//! report, because `observe` has no error channel).
//!
//! A history event the engine could not record is `Rejection::Unavailable` from
//! `Authorizer::submit` (the specification's `Rejection.unavailable`); a decision
//! event fails closed, without evaluating its leaves.

use std::sync::{Arc, Mutex};

use dogwood_language::cedar::Schema;
use dogwood_language::{
    Authorizer, Decision, Error, Event, EventSignature, InMemoryTemporalEngine, LoweredPolicySet,
    PolicySchema, Rejection, ServiceSchema, TemporalBindings, TemporalEngine, TemporalField, Value,
};

const SCHEMA: &str = r#"
namespace Svc {
  entity User;
  entity Doc;
  type In = { doc: String };
  action "Login" appliesTo { principal: [User], resource: [Doc], context: { input: In } };
  action "Read" appliesTo { principal: [User], resource: [Doc], context: { input: In } };
}
"#;

const POLICY: &str = r#"permit (principal, action == Svc::Action::"Read", resource)
    when temporal { formerly within 1h Svc::Action::"Login"::response{} };"#;

fn lower() -> LoweredPolicySet {
    LoweredPolicySet::from_str(
        POLICY,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(SCHEMA).unwrap(),
    )
    .unwrap()
}

/// The in-memory engine, except that the writes listed in `fail` fail.
struct Flaky {
    inner: InMemoryTemporalEngine,
    fail: Arc<Mutex<Vec<bool>>>,
    evaluated: Arc<Mutex<usize>>,
}

impl TemporalEngine for Flaky {
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        schema: &Schema,
        events: &[EventSignature],
    ) -> Result<(), Error> {
        self.inner.prepare(leaves, schema, events)
    }

    fn observe(&mut self, event: &Event) {
        let _ = self.try_observe(event);
    }

    fn try_observe(&mut self, event: &Event) -> Result<(), Rejection> {
        let fail = {
            let mut f = self.fail.lock().unwrap();
            if f.is_empty() { false } else { f.remove(0) }
        };
        if fail {
            return Err(Rejection::Unavailable {
                reason: "the retry budget ran out".into(),
            });
        }
        self.inner.observe(event);
        Ok(())
    }

    fn evaluate(&mut self) -> Result<TemporalBindings, String> {
        *self.evaluated.lock().unwrap() += 1;
        self.inner.evaluate()
    }
}

fn event(action: &str, kind: &str) -> Event {
    Event::builder(&format!("Svc::Action::{action}"), kind)
        .principal("Svc::User::\"alice\"")
        .resource("Svc::Doc::\"d\"")
        .field("input", "doc", Value::String("d".into()))
        .request_context("input", "doc", Value::String("d".into()))
        .build()
}

#[test]
fn an_unrecorded_history_event_is_reported_and_an_unrecorded_decision_fails_closed() {
    let fail = Arc::new(Mutex::new(vec![true, false, true]));
    let evaluated = Arc::new(Mutex::new(0));
    let mut a = Authorizer::builder(lower())
        .temporal_engine(Flaky {
            inner: InMemoryTemporalEngine::new(),
            fail: fail.clone(),
            evaluated: evaluated.clone(),
        })
        .build()
        .unwrap();
    // 1. The login's write fails: reported, not lost.
    let err = a
        .submit(&event("Login", "response"))
        .expect_err("not recorded");
    assert!(
        matches!(&err, Rejection::Unavailable { reason } if reason.contains("budget")),
        "{err}"
    );
    // 2. The read is recorded and decided: no login in its history, so Deny.
    let r = a.submit(&event("Read", "request")).unwrap().unwrap();
    assert_eq!(r.decision(), Decision::Deny);
    assert_eq!(r.diagnostics().errors().count(), 0, "{r:?}");
    // 3. A read whose own write fails is not evaluated, and fails closed.
    let before = *evaluated.lock().unwrap();
    let r = a.submit(&event("Read", "request")).unwrap().unwrap();
    assert_eq!(r.decision(), Decision::Deny);
    assert!(
        r.diagnostics().errors().any(|e| e.contains("not recorded")),
        "{r:?}"
    );
    assert_eq!(
        *evaluated.lock().unwrap(),
        before,
        "no evaluation without the event"
    );
    // `is_authorized` keeps its answers: `None` for the history event.
    fail.lock().unwrap().push(true);
    assert!(a.is_authorized(&event("Login", "response")).is_none());
}

/// An engine that implements only `observe` (as engines written against 1.1 do)
/// keeps working: the default `try_observe` observes and reports success.
#[test]
fn the_default_try_observe_observes() {
    let mut a = Authorizer::new(lower());
    assert!(matches!(a.submit(&event("Login", "response")), Ok(None)));
    assert!(
        a.submit(&event("Read", "request"))
            .unwrap()
            .unwrap()
            .allowed()
    );
}
