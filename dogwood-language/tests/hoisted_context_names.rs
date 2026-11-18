//! A decision's request context must not name an attribute the crate binds
//! itself: a hoisted temporal leaf (`<rule_key>__temporal_<j>`) or the provider
//! record (`providers`). The lowered rules read their leaves there, so a request
//! that supplied one would decide with its own value wherever the temporal
//! engine binds none (an engine with sparse bindings binds only the leaves of
//! the rules that can apply), and would make the leaf look known to an engine's
//! leaf masker, which partially evaluates the rules over `decision_request`.
//!
//! The crate refuses such a request wherever it builds a decision's request and
//! context: the decision fails closed (a `Deny` naming the group), and
//! `decision_request` and `DecisionRequestCache::decision_request` return the
//! error. (`DogwoodCompilerProofs.Options.Sparse.NoLeafAttrs` is what the Lean
//! proofs of sparse bindings and of the masker's scope index ask of the request,
//! and `Options.SparseChecked` derives it from this check.)

use std::collections::BTreeMap;

use dogwood_language::cedar::Schema;
use dogwood_language::{
    Authorizer, Decision, DecisionRequestCache, Error, Event, EventSignature,
    InMemoryTemporalEngine, LoweredPolicySet, PolicySchema, ServiceSchema, TemporalBindings,
    TemporalEngine, TemporalField, Value, decision_request,
};

const SCHEMA: &str = r#"
namespace Svc {
  entity User;
  entity Doc;
  type In = { doc: String };
  action "Login" appliesTo { principal: [User], resource: [Doc], context: { input: In } };
  action "Read" appliesTo {
    principal: [User], resource: [Doc],
    // The control groups of `a_request_without_a_hoisted_name_decides`, declared so
    // that a request holding one conforms (the specification's request check).
    context: { input: In, system?: Bool, temporal_0?: Bool, x__temporal_?: Bool, x__temporal_1a?: Bool }
  };
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

/// The in-memory engine, except that it binds no leaf: what an engine with
/// sparse bindings answers for a decision none of whose rules' leaves it binds.
struct Unbound(InMemoryTemporalEngine);

impl TemporalEngine for Unbound {
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        schema: &Schema,
        events: &[EventSignature],
    ) -> Result<(), Error> {
        self.0.prepare(leaves, schema, events)
    }

    fn observe(&mut self, event: &Event) {
        self.0.observe(event);
    }

    fn evaluate(&mut self) -> Result<TemporalBindings, String> {
        self.0.evaluate()?;
        Ok(BTreeMap::new())
    }
}

/// A `Read` decision with no `Login` before it, whose request context also holds
/// the top-level group `group` = `true` (when given).
fn read(group: Option<&str>) -> Event {
    let b = Event::builder("Svc::Action::Read", "request")
        .timestamp(10)
        .principal("Svc::User::\"u\"")
        .resource("Svc::Doc::\"d\"")
        .field("input", "doc", Value::String("d".into()))
        .request_context("input", "doc", Value::String("d".into()));
    match group {
        Some(g) => b.request_context_field(g, Value::Bool(true)),
        None => b,
    }
    .build()
}

/// The hoisted leaf's attribute name (`policy_0__temporal_0`).
fn leaf_name(p: &LoweredPolicySet) -> String {
    let ids: Vec<String> = p.temporal_fields().map(|f| f.id.to_string()).collect();
    assert_eq!(ids.len(), 1, "{ids:?}");
    assert!(ids[0].contains("__temporal_"), "{ids:?}");
    ids[0].clone()
}

/// The fail-open this closes: with no `Login`, the leaf is false and the `Read`
/// is denied; a request that supplies `context.<leaf> = true` itself, decided by
/// an engine that binds no leaf, was allowed (the permit read the request's
/// value). It now fails closed, and says why.
#[test]
fn a_request_naming_a_hoisted_leaf_fails_closed() {
    let p = lower();
    let leaf = leaf_name(&p);
    let mut a = Authorizer::builder(p)
        .temporal_engine(Unbound(InMemoryTemporalEngine::new()))
        .build()
        .expect("prepares");
    let r = a.is_authorized(&read(Some(&leaf))).expect("a decision");
    assert_eq!(r.decision(), Decision::Deny, "{r:?}");
    let errors: Vec<&str> = r.diagnostics().errors().collect();
    // The specification's request check, which comes first, refuses the attribute
    // (the action's context type does not declare a hoisted attribute); the
    // refusal by name stands behind it, and is what `decision_request` answers.
    assert!(
        errors.iter().any(|e| e.contains(&format!("`{leaf}`"))
            && (e.contains("fails closed") || e.starts_with("nonconforming request:"))),
        "{errors:?}"
    );
}

/// The same with the in-memory engine, which binds every leaf: the context would
/// hold the leaf twice (Cedar refused it before too, as a duplicate key); it is
/// now refused by name.
#[test]
fn a_request_naming_a_hoisted_leaf_fails_closed_with_every_leaf_bound() {
    let p = lower();
    let leaf = leaf_name(&p);
    let mut a = Authorizer::builder(p)
        .temporal_engine(InMemoryTemporalEngine::new())
        .build()
        .expect("prepares");
    let r = a.is_authorized(&read(Some(&leaf))).expect("a decision");
    assert_eq!(r.decision(), Decision::Deny, "{r:?}");
    let errors: Vec<&str> = r.diagnostics().errors().collect();
    assert!(
        errors.iter().any(|e| e.contains(&format!("`{leaf}`"))),
        "{errors:?}"
    );
}

/// The control: without the group, the decision is the specification's (no
/// `Login`, so the permit's leaf is false: `Deny`, with no error), and a request
/// with an ordinary extra group decides as before.
#[test]
fn a_request_without_a_hoisted_name_decides() {
    for group in [
        None,
        Some("system"),
        Some("temporal_0"),
        Some("x__temporal_"),
        Some("x__temporal_1a"),
    ] {
        let mut a = Authorizer::builder(lower())
            .temporal_engine(InMemoryTemporalEngine::new())
            .build()
            .expect("prepares");
        let r = a.is_authorized(&read(group)).expect("a decision");
        assert_eq!(r.decision(), Decision::Deny, "{group:?}: {r:?}");
        assert_eq!(r.diagnostics().errors().count(), 0, "{group:?}: {r:?}");
    }
}

/// `decision_request` and `DecisionRequestCache::decision_request` (the requests
/// the engines' leaf maskers partially evaluate) refuse a request naming a
/// hoisted leaf, under this set's names or any of the same shape, or the provider
/// record; and build every other request as before.
#[test]
fn decision_requests_refuse_hoisted_names() {
    let p = lower();
    let leaf = leaf_name(&p);
    let schema = p.cedar_schema();
    let cache = DecisionRequestCache::new(schema).expect("the cache builds");
    for name in [
        leaf.as_str(),
        "providers",
        "dw__temporal_3",
        "__temporal_0",
        "usr_7__temporal_12",
    ] {
        let event = read(Some(name));
        let err = decision_request(&event, schema).expect_err(name);
        assert!(
            err.contains(&format!("`{name}`")) && err.contains("fails closed"),
            "{name}: {err}"
        );
        let err = cache.decision_request(&event).expect_err(name);
        assert!(err.contains(&format!("`{name}`")), "{name}: {err}");
        let err = p.decision_request(&event).expect_err(name);
        assert!(err.contains(&format!("`{name}`")), "{name}: {err}");
    }
    for group in [
        None,
        Some("system"),
        Some("x__temporal_"),
        Some("x__temporal_1a"),
        Some("providers_"),
    ] {
        let event = read(group);
        let (request, _) = decision_request(&event, schema).expect("builds");
        let (cached, _) = cache.decision_request(&event).expect("builds");
        assert_eq!(request.to_string(), cached.to_string(), "{group:?}");
    }
}

/// The provider record `providers` is refused in a request, whatever the request
/// puts there (with providers, the context would hold it twice; without, it is
/// the name the crate reserves for them all the same).
#[test]
fn a_request_naming_the_provider_record_fails_closed() {
    let mut a = Authorizer::builder(lower())
        .temporal_engine(InMemoryTemporalEngine::new())
        .build()
        .expect("prepares");
    let r = a
        .is_authorized(&read(Some("providers")))
        .expect("a decision");
    assert_eq!(r.decision(), Decision::Deny, "{r:?}");
    let errors: Vec<&str> = r.diagnostics().errors().collect();
    assert!(
        errors.iter().any(|e| e.contains("`providers`")),
        "{errors:?}"
    );
}
