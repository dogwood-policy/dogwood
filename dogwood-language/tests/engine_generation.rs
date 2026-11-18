//! `TemporalEngine::set_generation`: the authorizer tells its temporal engine the deployment
//! generation of the leaves before every `prepare`, the builder's at build and one more at each
//! live update, so that an engine whose instances share history can order deployments (a key
//! decided under one generation is never decided again under an older one).

use std::sync::{Arc, Mutex};

use dogwood_language::cedar::Schema;
use dogwood_language::{
    Authorizer, Error, Event, EventSignature, InMemoryTemporalEngine, LoweredPolicySet,
    PolicySchema, ServiceSchema, TemporalBindings, TemporalEngine, TemporalField,
};

const SCHEMA: &str = r#"namespace Svc { entity User; entity Doc;
  action "Read" appliesTo { principal: [User], resource: [Doc], context: {} }; }"#;

fn lower() -> LoweredPolicySet {
    LoweredPolicySet::from_str(
        r#"permit (principal, action == Svc::Action::"Read", resource) when temporal { formerly within 1h Svc::Action::"Read"::request{} };"#,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(SCHEMA).unwrap(),
    )
    .unwrap()
}

/// Records each `(generation set, prepare)` in order.
struct Recorder {
    inner: InMemoryTemporalEngine,
    log: Arc<Mutex<Vec<String>>>,
}

impl TemporalEngine for Recorder {
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        schema: &Schema,
        events: &[EventSignature],
    ) -> Result<(), Error> {
        self.log.lock().unwrap().push("prepare".into());
        self.inner.prepare(leaves, schema, events)
    }
    fn observe(&mut self, event: &Event) {
        self.inner.observe(event)
    }
    fn evaluate(&mut self) -> Result<TemporalBindings, String> {
        self.inner.evaluate()
    }
    fn supports_policy_update(&self) -> bool {
        true
    }
    fn set_generation(&mut self, generation: u64) {
        self.log
            .lock()
            .unwrap()
            .push(format!("generation {generation}"));
    }
}

#[test]
fn the_generation_precedes_every_prepare() {
    let log = Arc::new(Mutex::new(Vec::new()));
    let mut a = Authorizer::builder(lower())
        .temporal_engine(Recorder {
            inner: InMemoryTemporalEngine::new(),
            log: log.clone(),
        })
        .generation(4)
        .build()
        .unwrap();
    a.update_policies(lower()).unwrap();
    a.update_policies(lower()).unwrap();
    assert_eq!(
        *log.lock().unwrap(),
        [
            "generation 4",
            "prepare",
            "generation 5",
            "prepare",
            "generation 6",
            "prepare"
        ]
    );
    assert_eq!(a.policy_set_version().generation(), 6);
}
