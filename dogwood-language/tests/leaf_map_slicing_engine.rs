//! End-to-end tests for leaf slicing in the reference interpreter.
//!
//! Each differential requires identical decisions, exact computed-leaf sets,
//! and at least one skipped leaf whose unsliced value was `true`.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};

use dogwood_language::{
    ActionScope, Authorizer, Decision, DecisionLeafMap, Error, Event, EventSignature,
    InMemoryTemporalEngine, LoweredPolicySet, PartitionKey, PolicySchema, ServiceSchema,
    TemporalBindings, TemporalEngine, TemporalField, cedar::Schema,
};

// ── fixtures ────────────────────────────────────────────────────────────

const SCHEMA: &str = r#"
namespace Drupe {
  type Input = { user: String };
  entity Gateway;
  entity OAuthUser;
  action "Admin";
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input } };
  action "Logout" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input } };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input } };
  action "Purge" in [Action::"Admin"] appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input } };
  action "Read::Archive" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input } };
  action "say \"hi\"" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input } };
}
"#;

// Keep skipped leaves true so an incorrect exclusion can change a verdict.
const AFTER_LOGIN: &str = r#"formerly within 1h Drupe::Action::"Login"::request{}"#;

fn policies() -> String {
    format!(
        r#"
permit (principal, action == Drupe::Action::"Login", resource)
when temporal {{ {AFTER_LOGIN} }};

permit (principal, action in [Drupe::Action::"Admin"], resource)
when temporal {{ {AFTER_LOGIN} }};

permit (principal, action in [Drupe::Action::"Logout", Drupe::Action::"Read"], resource)
when temporal {{ {AFTER_LOGIN} }};

permit (principal, action == Drupe::Action::"Read::Archive", resource)
when temporal {{ {AFTER_LOGIN} }};

permit (principal, action == Drupe::Action::"say \"hi\"", resource)
when temporal {{ {AFTER_LOGIN} }};

permit (principal, action == Drupe::Action::"Read", resource)
when temporal {{ {AFTER_LOGIN} }};
"#
    )
}

const L_LOGIN: &str = "policy_0__temporal_0";
const L_ADMIN_GROUP: &str = "policy_1__temporal_0";
const L_LIST: &str = "policy_2__temporal_0";
const L_SEPARATOR_ID: &str = "policy_3__temporal_0";
const L_ESCAPED_ID: &str = "policy_4__temporal_0";
const L_READ_AGAIN: &str = "policy_5__temporal_0";

fn lower(policy: &str, event_schema: &str) -> LoweredPolicySet {
    let service = ServiceSchema::builder()
        .event_schema_str(event_schema)
        .build()
        .expect("event schema builds");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema builds");
    LoweredPolicySet::from_str(policy, &service, &schema).expect("policy lowers")
}

fn unpinned_event_schema() -> String {
    std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/request_response.dwschema"),
    )
    .expect("the shared unpinned event-schema fixture is readable")
}

const PINNED_EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:  resourceType(A),
    requestId:       String,
}
event <A>::response {
    ...inputs(A),
    ...outputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

// Avoid making escaped action-id coverage depend on the trace parser.
fn event(ts: i64, who: &str, action: &str) -> Event {
    Event::builder_for(&["Drupe", "Action"], action, "request")
        .timestamp(ts)
        .principal_for("Drupe::OAuthUser", who)
        .resource_for("Drupe::Gateway", "gw")
        .logged_field(
            "callerPrincipal",
            dogwood_language::Value::Entity {
                ty: "Drupe::OAuthUser".into(),
                id: who.into(),
            },
        )
        .build()
}

// ── the observation seam ────────────────────────────────────────────────

#[derive(Clone, Debug)]
struct Pass {
    action: String,
    computed: BTreeSet<String>,
    bindings: BTreeMap<String, bool>,
}

impl Pass {
    fn skipped(&self) -> BTreeSet<String> {
        self.bindings
            .keys()
            .filter(|id| !self.computed.contains(*id))
            .cloned()
            .collect()
    }
}

/// Records evaluations while delegating behavior to `InMemoryTemporalEngine`.
struct Spy {
    inner: InMemoryTemporalEngine,
    last_action: Option<String>,
    // Used only to verify that the differential catches an unsound map.
    sabotage: Option<String>,
    passes: Arc<Mutex<Vec<Pass>>>,
}

impl Spy {
    fn new(inner: InMemoryTemporalEngine) -> (Self, Arc<Mutex<Vec<Pass>>>) {
        Spy::with_sabotage(inner, None)
    }

    fn with_sabotage(
        inner: InMemoryTemporalEngine,
        sabotage: Option<String>,
    ) -> (Self, Arc<Mutex<Vec<Pass>>>) {
        let passes = Arc::new(Mutex::new(Vec::new()));
        (
            Spy {
                inner,
                last_action: None,
                sabotage,
                passes: Arc::clone(&passes),
            },
            passes,
        )
    }
}

impl TemporalEngine for Spy {
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        schema: &Schema,
        events: &[EventSignature],
    ) -> Result<(), Error> {
        self.inner.prepare(leaves, schema, events)?;
        if let Some(drop_id) = &self.sabotage {
            let kept: Vec<TemporalField> = leaves
                .iter()
                .filter(|f| &f.id != drop_id)
                .cloned()
                .collect();
            self.inner
                .install_leaf_map(DecisionLeafMap::build(&kept, schema));
        }
        Ok(())
    }

    fn observe(&mut self, event: &Event) {
        self.last_action = Some(event.action().to_string());
        self.inner.observe(event);
    }

    fn evaluate(&mut self) -> Result<TemporalBindings, String> {
        let bindings = self.inner.evaluate()?;
        self.passes.lock().unwrap().push(Pass {
            action: self.last_action.clone().unwrap_or_default(),
            computed: self.inner.computed_leaves().clone(),
            bindings: bindings.clone(),
        });
        Ok(bindings)
    }

    fn supports_partitioning(&self) -> bool {
        self.inner.supports_partitioning()
    }

    fn set_partition_keys(&mut self, keys: &[PartitionKey]) {
        self.inner.set_partition_keys(keys);
    }
}

fn run_with(
    lowered: LoweredPolicySet,
    engine: InMemoryTemporalEngine,
    partitioned: bool,
    events: &[Event],
) -> (Vec<Decision>, Vec<Pass>) {
    let (spy, passes) = Spy::new(engine);
    let mut builder = Authorizer::builder(lowered).temporal_engine(spy);
    if partitioned {
        builder = builder.partition_temporal();
    }
    let mut authorizer = builder.build().expect("authorizer builds");
    let decisions = events
        .iter()
        .filter_map(|e| authorizer.is_authorized(e).map(|r| r.decision()))
        .collect();
    let passes = passes.lock().unwrap().clone();
    (decisions, passes)
}

#[track_caller]
fn differential(
    policy: &str,
    event_schema: &str,
    partitioned: bool,
    events: &[Event],
) -> Vec<Pass> {
    let (unsliced, unsliced_passes) = run_with(
        lower(policy, event_schema),
        InMemoryTemporalEngine::new(),
        partitioned,
        events,
    );
    let (sliced, sliced_passes) = run_with(
        lower(policy, event_schema),
        InMemoryTemporalEngine::new().slice_leaves(),
        partitioned,
        events,
    );
    assert_eq!(
        unsliced, sliced,
        "slicing changed a verdict — the one thing it must never do"
    );
    assert_eq!(unsliced_passes.len(), sliced_passes.len());

    for pass in &unsliced_passes {
        assert_eq!(
            pass.computed,
            pass.bindings.keys().cloned().collect::<BTreeSet<_>>(),
            "the default engine must interpret every installed leaf (action {})",
            pass.action
        );
    }

    let mut saw_suppressed_true = false;
    for (u, s) in unsliced_passes.iter().zip(&sliced_passes) {
        for id in s.skipped() {
            assert_eq!(
                s.bindings.get(&id),
                Some(&false),
                "a skipped leaf must still be bound, as `false`"
            );
            if u.bindings.get(&id) == Some(&true) {
                saw_suppressed_true = true;
            }
        }
    }
    assert!(
        saw_suppressed_true,
        "vacuous lane: no decision skipped a leaf that would have been `true`, so an \
         unsound slice could not have been observed here"
    );
    sliced_passes
}

#[track_caller]
fn assert_computed(passes: &[Pass], action: &str, expect: &[&str], why: &str) {
    let pass = passes
        .iter()
        .find(|p| p.action == action)
        .unwrap_or_else(|| panic!("no decision for action {action:?}"));
    let expect: BTreeSet<String> = expect.iter().map(|s| s.to_string()).collect();
    assert_eq!(pass.computed, expect, "{action}: {why}");
}

fn every_action() -> Vec<Event> {
    [
        "Login",
        "Logout",
        "Read",
        "Purge",
        "Read::Archive",
        "say \"hi\"",
    ]
    .iter()
    .enumerate()
    .map(|(i, action)| event(i as i64 * 10, "u1", action))
    .collect()
}

// ── 1. the flag is off by default ───────────────────────────────────────

#[test]
fn the_default_engine_computes_every_leaf() {
    let (decisions, passes) = run_with(
        lower(&policies(), &unpinned_event_schema()),
        InMemoryTemporalEngine::new(),
        false,
        &every_action(),
    );
    assert_eq!(
        decisions.len(),
        6,
        "every fixture action is a decision point"
    );
    for pass in &passes {
        assert_eq!(
            pass.computed.len(),
            6,
            "action {}: the unsliced engine interprets all six leaves",
            pass.action
        );
    }
}

#[test]
fn the_default_engine_builds_no_map() {
    let lowered = lower(&policies(), &unpinned_event_schema());
    let leaves: Vec<TemporalField> = lowered.temporal_fields().cloned().collect();

    let mut engine = InMemoryTemporalEngine::new();
    engine
        .prepare(&leaves, lowered.cedar_schema(), &[])
        .expect("prepare succeeds");
    assert!(engine.leaf_map().is_none());

    let mut sliced = InMemoryTemporalEngine::new().slice_leaves();
    sliced
        .prepare(&leaves, lowered.cedar_schema(), &[])
        .expect("prepare succeeds");
    let map = sliced.leaf_map().expect("slicing builds a map");
    assert_eq!(
        map.entry_count(),
        6,
        "one entry per action that can receive a request — the `Admin` group is not one"
    );
}

// ── 2. exactness, per scope shape ───────────────────────────────────────

#[test]
fn each_action_computes_exactly_its_own_leaves() {
    let passes = differential(
        &policies(),
        &unpinned_event_schema(),
        false,
        &every_action(),
    );

    assert_computed(
        &passes,
        "Login",
        &[L_LOGIN],
        "only the `==`-scoped rule on Login applies",
    );
    assert_computed(
        &passes,
        "Logout",
        &[L_LIST],
        "reached through a multi-action `in [...]` list, not a group",
    );
    assert_computed(
        &passes,
        "Read",
        &[L_LIST, L_READ_AGAIN],
        "two rules name Read — a map entry must hold BOTH leaves",
    );
    assert_computed(
        &passes,
        "Purge",
        &[L_ADMIN_GROUP],
        "the group scope is expanded to its MEMBER; Purge is the member, and the \
         group-scoped leaf is the only one it reads",
    );
    assert_computed(
        &passes,
        "Read::Archive",
        &[L_SEPARATOR_ID],
        "an id holding the `::` type/id separator must not be confused with the \
         `Read` action whose name is its prefix",
    );
    assert_computed(
        &passes,
        "say \"hi\"",
        &[L_ESCAPED_ID],
        "an id that needs escaping is matched by its DECODED identity",
    );
}

#[test]
fn an_action_no_rule_mentions_computes_nothing() {
    let policy = format!(
        r#"
permit (principal, action == Drupe::Action::"Login", resource)
when temporal {{ {AFTER_LOGIN} }};

permit (principal, action == Drupe::Action::"Read", resource)
when temporal {{ {AFTER_LOGIN} }};
"#
    );
    let events = vec![
        event(0, "u1", "Login"),
        event(10, "u1", "Read"),
        event(20, "u1", "Logout"),
    ];
    let passes = differential(&policy, &unpinned_event_schema(), false, &events);
    assert_computed(
        &passes,
        "Logout",
        &[],
        "no rule is scoped to Logout, so its decision interprets no leaf at all",
    );
    assert_computed(&passes, "Read", &["policy_1__temporal_0"], "its own leaf");
}

#[test]
fn a_group_scope_separates_member_from_non_member() {
    let policy = format!(
        r#"
permit (principal, action in [Drupe::Action::"Admin"], resource)
when temporal {{ {AFTER_LOGIN} }};

permit (principal, action == Drupe::Action::"Logout", resource)
when temporal {{ {AFTER_LOGIN} }};
"#
    );
    let events = vec![
        event(0, "u1", "Login"),
        event(10, "u1", "Purge"),
        event(20, "u1", "Logout"),
    ];
    let passes = differential(&policy, &unpinned_event_schema(), false, &events);
    assert_computed(
        &passes,
        "Purge",
        &["policy_0__temporal_0"],
        "member of the group named by the scope",
    );
    assert_computed(
        &passes,
        "Logout",
        &["policy_1__temporal_0"],
        "not a member of the group: the group-scoped leaf is skipped, its own is not",
    );
}

// ── 3. the conservative fallbacks (compute MORE, never less) ────────────

#[test]
fn a_bare_action_scope_is_computed_on_every_action() {
    let policy = format!(
        r#"
permit (principal, action, resource)
when temporal {{ {AFTER_LOGIN} }};

permit (principal, action == Drupe::Action::"Read", resource)
when temporal {{ {AFTER_LOGIN} }};
"#
    );
    let events = vec![
        event(0, "u1", "Login"),
        event(10, "u1", "Read"),
        event(20, "u1", "Logout"),
        event(30, "u1", "Purge"),
    ];
    let passes = differential(&policy, &unpinned_event_schema(), false, &events);
    for pass in &passes {
        assert!(
            pass.computed.contains("policy_0__temporal_0"),
            "action {}: an unconstrained rule's leaf must be computed everywhere",
            pass.action
        );
    }
    assert_computed(
        &passes,
        "Read",
        &["policy_0__temporal_0", "policy_1__temporal_0"],
        "the unconstrained leaf plus its own",
    );
    assert_computed(
        &passes,
        "Logout",
        &["policy_0__temporal_0"],
        "only the unconstrained leaf",
    );

    let lowered = lower(&policy, &unpinned_event_schema());
    let leaves: Vec<TemporalField> = lowered.temporal_fields().cloned().collect();
    let map = DecisionLeafMap::build(&leaves, lowered.cedar_schema());
    let reasons: Vec<_> = map.unresolved().iter().map(|(id, _)| id.clone()).collect();
    assert_eq!(
        reasons,
        vec!["policy_0__temporal_0".to_string()],
        "the bare-scope leaf is the one reported unresolved"
    );
    assert!(
        matches!(
            leaves.first().expect("a leaf").action,
            ActionScope::Unconstrained
        ),
        "precondition: the first rule really has a bare `action` scope"
    );
}

#[test]
fn an_undeclared_request_action_computes_every_leaf() {
    // A second schema that declares `Ghost`, used only to *lower* an event for
    // it; the policy set under test knows nothing about it.
    let events = vec![
        event(0, "u1", "Login"),
        event(10, "u1", "Ghost"),
        event(20, "u1", "Read"),
    ];
    let policy = format!(
        r#"
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {{ {AFTER_LOGIN} }};
"#
    );
    let (unsliced, unsliced_passes) = run_with(
        lower(&policy, &unpinned_event_schema()),
        InMemoryTemporalEngine::new(),
        false,
        &events,
    );
    let (sliced, sliced_passes) = run_with(
        lower(&policy, &unpinned_event_schema()),
        InMemoryTemporalEngine::new().slice_leaves(),
        false,
        &events,
    );
    assert_eq!(
        unsliced, sliced,
        "an undeclared action must decide the same"
    );
    let ghost = sliced_passes
        .iter()
        .find(|p| p.action == "Ghost")
        .expect("the undeclared action still reaches a decision point");
    assert_eq!(
        ghost.computed,
        BTreeSet::from(["policy_0__temporal_0".to_string()]),
        "no map entry for an undeclared action, so every leaf is computed"
    );
    assert_eq!(
        unsliced_passes.len(),
        sliced_passes.len(),
        "same decision points either way"
    );
}

#[test]
fn an_empty_map_is_a_no_op() {
    let lowered = lower(&policies(), &unpinned_event_schema());
    let leaves: Vec<TemporalField> = lowered.temporal_fields().cloned().collect();
    let all_ids: BTreeSet<String> = leaves.iter().map(|f| f.id.clone()).collect();

    let mut engine = InMemoryTemporalEngine::new().slice_leaves();
    engine
        .prepare(&leaves, lowered.cedar_schema(), &[])
        .expect("prepare succeeds");
    // Precondition: with the real map, `Logout` computes just the list leaf.
    engine.observe(&event(0, "u1", "Logout"));
    engine.evaluate().expect("evaluates");
    assert_eq!(
        *engine.computed_leaves(),
        BTreeSet::from([L_LIST.to_string()]),
        "precondition: the real map does slice this action"
    );

    engine.install_leaf_map(DecisionLeafMap::default());
    engine.observe(&event(10, "u1", "Logout"));
    let bindings = engine.evaluate().expect("evaluates");
    assert_eq!(
        *engine.computed_leaves(),
        all_ids,
        "an empty map must slice NOTHING — every lookup misses, and a miss means \
         compute everything"
    );
    assert_eq!(
        bindings.len(),
        6,
        "and every installed leaf is still bound either way"
    );
}

// ── 4. partitioned mode ─────────────────────────────────────────────────

#[test]
fn slicing_applies_in_partitioned_mode_too() {
    let policy = policies();
    let lowered = lower(&policy, PINNED_EVENT_SCHEMA);
    assert!(
        !lowered.partition_keys().is_empty(),
        "precondition: the pinned event schema yields a partition key"
    );

    let events = vec![
        event(0, "u1", "Login"),
        event(10, "u2", "Read"),
        event(20, "u1", "Read"),
        event(30, "u1", "Purge"),
        event(40, "u2", "Logout"),
    ];
    let passes = differential(&policy, PINNED_EVENT_SCHEMA, true, &events);
    // Same exclusion sets as the global lane: the action decides which leaves
    // run, and partitioning does not change any action.
    assert_computed(&passes, "Read", &[L_LIST, L_READ_AGAIN], "action-keyed");
    assert_computed(&passes, "Purge", &[L_ADMIN_GROUP], "action-keyed");
    assert_computed(&passes, "Logout", &[L_LIST], "action-keyed");

    // And the verdicts really do depend on the partition, so the lane is not
    // silently testing global semantics: `u2`'s Read is denied (no Login of its
    // own) while `u1`'s is allowed.
    let (decisions, _) = run_with(
        lower(&policy, PINNED_EVENT_SCHEMA),
        InMemoryTemporalEngine::new().slice_leaves(),
        true,
        &events,
    );
    assert_eq!(
        decisions,
        vec![
            Decision::Allow, // u1 Login — its own leaf, after its own Login
            Decision::Deny,  // u2 Read — u1's Login is in another partition
            Decision::Allow, // u1 Read
            Decision::Allow, // u1 Purge
            Decision::Deny,  // u2 Logout
        ],
        "partitioned semantics, under slicing"
    );
}

// ── 5. the negative control ─────────────────────────────────────────────

/// Verify the differential rejects a map missing a required leaf.
#[test]
fn the_negative_control_catches_a_doctored_map() {
    let policy = format!(
        r#"
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {{ {AFTER_LOGIN} }};
"#
    );
    let events = vec![event(0, "u1", "Login"), event(10, "u1", "Read")];
    let leaf = "policy_0__temporal_0";

    // Honest baseline: `Read` computes its leaf, which is `true`, so Allow.
    let (honest, honest_passes) = run_with(
        lower(&policy, &unpinned_event_schema()),
        InMemoryTemporalEngine::new().slice_leaves(),
        false,
        &events,
    );
    assert_computed(
        &honest_passes,
        "Read",
        &[leaf],
        "precondition: honestly read",
    );
    assert_eq!(
        honest,
        vec![Decision::Deny, Decision::Allow],
        "precondition: Login is no decision this policy permits; Read is"
    );

    // Doctored: the same run with `Read`'s leaf missing from the map.
    let (spy, passes) = Spy::with_sabotage(
        InMemoryTemporalEngine::new().slice_leaves(),
        Some(leaf.to_string()),
    );
    let mut authorizer = Authorizer::builder(lower(&policy, &unpinned_event_schema()))
        .temporal_engine(spy)
        .build()
        .expect("authorizer builds");
    let doctored: Vec<Decision> = events
        .iter()
        .filter_map(|e| authorizer.is_authorized(e).map(|r| r.decision()))
        .collect();
    let doctored_passes = passes.lock().unwrap().clone();

    // Gate 1 — the verdict stream diverges. This is what "slicing never changes a
    // verdict" is worth: broken, it does.
    assert_ne!(
        honest, doctored,
        "a map that drops a needed leaf MUST change a verdict — if it did not, the \
         corpus differential's verdict comparison would be proving nothing"
    );
    assert_eq!(
        doctored,
        vec![Decision::Deny, Decision::Deny],
        "the suppressed leaf is reported `false`, so the `permit` no longer fires"
    );

    // Gate 2 — the exact-exclusion assertion fires. Run the *real* assertion and
    // require it to panic, rather than restating what it checks.
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        assert_computed(&doctored_passes, "Read", &[leaf], "must not hold here");
    }));
    assert!(
        caught.is_err(),
        "the exact-exclusion assertion must reject a run that skipped a leaf its \
         action needs"
    );
}
