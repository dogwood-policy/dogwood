//! `TemporalEngine::set_authored_leaves`: the authorizer hands every temporal engine the
//! authored (non-relativized) leaves before each `prepare`, parallel by position to the leaves
//! `prepare` receives, in global and partitioned evaluation alike.

use std::sync::{Arc, Mutex};

use dogwood_language::{
    Authorizer, Error, Event, EventSignature, LoweredPolicySet, PartitionKey, PolicySchema,
    ServiceSchema, TemporalBindings, TemporalEngine, TemporalField, cedar::Schema,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type Input = { user: String };
  entity Gateway;
  entity OAuthUser;
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input } };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input } };
}
"#;

const POLICY: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when temporal { formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user } };

permit (principal, action == Drupe::Action::"Read", resource)
when temporal { previous within 1h Drupe::Action::"Read"::request{} };
"#;

#[derive(Default)]
struct Seen {
    authored: Vec<Vec<TemporalField>>,
    prepared: Vec<Vec<TemporalField>>,
}

struct Recording {
    seen: Arc<Mutex<Seen>>,
    partitions: bool,
}

const POLICY_UPDATED: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when temporal { previous within 1h Drupe::Action::"Read"::request{} };
"#;

impl TemporalEngine for Recording {
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        _schema: &Schema,
        _events: &[EventSignature],
    ) -> Result<(), Error> {
        self.seen.lock().unwrap().prepared.push(leaves.to_vec());
        Ok(())
    }
    fn observe(&mut self, _event: &Event) {}
    fn evaluate(&mut self) -> Result<TemporalBindings, String> {
        Ok(TemporalBindings::new())
    }
    fn supports_partitioning(&self) -> bool {
        self.partitions
    }
    fn set_partition_keys(&mut self, _keys: &[PartitionKey]) {}
    fn set_authored_leaves(&mut self, authored: &[TemporalField]) {
        self.seen.lock().unwrap().authored.push(authored.to_vec());
    }
    fn supports_policy_update(&self) -> bool {
        true
    }
}

fn lowered_from(src: &str) -> LoweredPolicySet {
    // The default service schema: its universal `callerPrincipal` pin relativizes every leaf.
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    LoweredPolicySet::from_str(src, &ServiceSchema::defaults(), &schema).expect("policy lowers")
}

fn lowered() -> LoweredPolicySet {
    lowered_from(POLICY)
}

#[test]
fn global_evaluation_hands_the_authored_leaves_before_prepare() {
    let policies = lowered();
    let authored: Vec<TemporalField> = policies.nonrelativized_temporal_fields().cloned().collect();
    let relativized: Vec<TemporalField> = policies.temporal_fields().cloned().collect();
    assert_ne!(
        authored
            .iter()
            .map(|l| format!("{:?}", l.condition.condition))
            .collect::<Vec<_>>(),
        relativized
            .iter()
            .map(|l| format!("{:?}", l.condition.condition))
            .collect::<Vec<_>>(),
        "the default schema relativizes the leaves"
    );
    let seen = Arc::new(Mutex::new(Seen::default()));
    let _authorizer = Authorizer::builder(policies)
        .temporal_engine(Recording {
            seen: seen.clone(),
            partitions: false,
        })
        .build()
        .expect("builds");
    let seen = seen.lock().unwrap();
    assert_eq!(seen.authored.len(), 1);
    assert_eq!(seen.prepared.len(), 1);
    let ids = |ls: &[TemporalField]| ls.iter().map(|l| l.id.clone()).collect::<Vec<_>>();
    assert_eq!(
        ids(&seen.authored[0]),
        ids(&seen.prepared[0]),
        "parallel by position"
    );
    assert_eq!(
        seen.authored[0]
            .iter()
            .map(|l| format!("{:?}", l.condition.condition))
            .collect::<Vec<_>>(),
        authored
            .iter()
            .map(|l| format!("{:?}", l.condition.condition))
            .collect::<Vec<_>>(),
        "the authored leaves are the non-relativized ones"
    );
    assert_eq!(
        seen.prepared[0]
            .iter()
            .map(|l| format!("{:?}", l.condition.condition))
            .collect::<Vec<_>>(),
        relativized
            .iter()
            .map(|l| format!("{:?}", l.condition.condition))
            .collect::<Vec<_>>(),
        "prepare still receives the relativized leaves"
    );
}

#[test]
fn partitioned_evaluation_hands_the_prepared_leaves() {
    let policies = lowered();
    let seen = Arc::new(Mutex::new(Seen::default()));
    let _authorizer = Authorizer::builder(policies)
        .temporal_engine(Recording {
            seen: seen.clone(),
            partitions: true,
        })
        .partition_temporal()
        .build()
        .expect("builds");
    let seen = seen.lock().unwrap();
    let conds = |ls: &[TemporalField]| {
        ls.iter()
            .map(|l| format!("{:?}", l.condition.condition))
            .collect::<Vec<_>>()
    };
    assert_eq!(conds(&seen.authored[0]), conds(&seen.prepared[0]));
}

#[test]
fn a_policy_update_hands_the_new_authored_leaves_before_its_prepare() {
    let seen = Arc::new(Mutex::new(Seen::default()));
    let mut authorizer = Authorizer::builder(lowered())
        .temporal_engine(Recording {
            seen: seen.clone(),
            partitions: false,
        })
        .build()
        .expect("builds");
    let updated = lowered_from(POLICY_UPDATED);
    let want: Vec<String> = updated
        .nonrelativized_temporal_fields()
        .map(|l| format!("{:?}", l.condition.condition))
        .collect();
    authorizer.update_policies(updated).expect("updates");
    let seen = seen.lock().unwrap();
    assert_eq!(seen.authored.len(), 2);
    assert_eq!(seen.prepared.len(), 2);
    let conds = |ls: &[TemporalField]| {
        ls.iter()
            .map(|l| format!("{:?}", l.condition.condition))
            .collect::<Vec<_>>()
    };
    assert_eq!(conds(&seen.authored[1]), want);
    let ids = |ls: &[TemporalField]| ls.iter().map(|l| l.id.clone()).collect::<Vec<_>>();
    assert_eq!(
        ids(&seen.authored[1]),
        ids(&seen.prepared[1]),
        "parallel by position"
    );
}
