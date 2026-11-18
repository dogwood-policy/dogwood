//! The canonical text of a lowered leaf, the pins taken off again, and the
//! slice of a lowered set for an action.

use super::{condition_text, parse_leaf_condition, without_spans};
use crate::api::{ActionRef, ActionScope};
use crate::event_schema::pin::{inject_pins, strip_pins};
use crate::extension::temporal::parse::parse_condition;
use crate::{LoweredPolicySet, PolicySchema, ServiceSchema};

const SCHEMA: &str = r#"
namespace Drupe {
  entity OAuthUser = { id: String };
  entity Gateway;
  type LoginInput = { user: String, server: String };
  type AlertInput = { level: Long, server: String };
  action "Login" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: LoginInput } };
  action "Alert" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: AlertInput } };
  action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: AlertInput } };
}
"#;

/// A macro whose fresh binder `$t` expansion renames per call site.
const POLICIES: &str = r#"
def temporal count_formerly(?w, ?s) {
    count for ($t: Timepoint). where (formerly within ?w (?s && tp($t)))
};

permit (principal, action == Drupe::Action::"Alert", resource)
when temporal {
    exists (n: Long). ((count_formerly(1h, Drupe::Action::"Login"::request{ input.user: _, input.server: context.input.server })) == n && n > 0)
};

permit (principal, action, resource)
when temporal { formerly within 1d Drupe::Action::"Login"::response{ input.user: "a \"b\" \\ c" } };

permit (principal, action in [Drupe::Action::"Read", Drupe::Action::"Login"], resource)
when temporal { formerly within 1h Drupe::Action::"Login"::request{} };
"#;

fn lowered() -> LoweredPolicySet {
    let service = ServiceSchema::builder()
        .build()
        .expect("the default service schema");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("the schema");
    LoweredPolicySet::from_str(POLICIES, &service, &schema).expect("the policies lower")
}

fn drupe(id: &str) -> ActionRef {
    ActionRef {
        namespace: Some("Drupe".to_owned()),
        id: id.to_owned(),
    }
}

/// **Every leaf's authored form, printed, reads back as itself**, a generated
/// binder included; the pins come off and go back on exactly.
#[test]
fn a_leaf_reads_back_from_its_text() {
    let set = lowered();
    let schema = &set.lowered().event_schema;
    let mut generated = 0;
    for leaf in set.nonrelativized_temporal_fields() {
        let pinned = &leaf.condition.condition;
        let authored = strip_pins(pinned, schema).expect("the pins come off");
        let mut again = authored.clone();
        inject_pins(&mut again, schema);
        assert_eq!(&again, pinned, "the pins go back on");
        let text = condition_text(&authored).expect("a canonical text");
        if text.contains("$t$") {
            generated += 1;
        }
        let back = parse_leaf_condition(&text).expect("the text parses");
        assert_eq!(without_spans(&back), without_spans(&authored));
        assert_eq!(condition_text(&back).expect("prints again"), text);
    }
    assert_eq!(generated, 1, "the macro's binder is spelled `$t$<n>`");
}

/// A policy or a macro body cannot write a generated binder's spelling.
#[test]
fn a_policy_cannot_write_a_generated_binder() {
    let e = parse_condition(
        "exists (n: Long). ((count for ($t$5: Timepoint). where (tp($t$5))) == n && n > 0)",
    )
    .expect_err("rejected");
    assert!(e.contains("macro expansion generated"), "{e}");
    let e = crate::extension::temporal::parse::parse_macro_body(
        "count for ($t$5: Timepoint). where (tp($t$5))",
        dogwood_syntax::DEFAULT_MAX_DEPTH,
    )
    .expect_err("rejected");
    assert!(e.contains("macro expansion generated"), "{e}");
    // The leaf parser reads it as the binder.
    let leaf = parse_leaf_condition(
        "exists (n: Long). (((count for ($t$5: Timepoint). where (tp($t$5))) == n) && (n > 0))",
    )
    .expect("a lowered leaf");
    assert!(condition_text(&leaf).expect("prints").contains("$t$5"));
    // A plain binder reference is a macro's, not a lowered leaf's.
    assert!(
        parse_leaf_condition(
            "exists (n: Long). (((count for ($t: Timepoint). where (tp($t))) == n) && (n > 0))"
        )
        .is_err()
    );
}

/// What a lowered leaf cannot hold has no canonical text, and the leaf parser
/// rejects it.
#[test]
fn macro_only_nodes_are_rejected() {
    for text in [
        r#"my_macro(1h)"#,
        r#"formerly within ?w Drupe::Action::"Login"::request{}"#,
        r#"Drupe::Action::"Login"::request{ input.user: ?u }"#,
        r#"Drupe::Action::"Login"::request{ input.user: ["a", "b"] }"#,
    ] {
        assert!(parse_leaf_condition(text).is_err(), "{text}");
        if let Ok(c) = crate::extension::temporal::parse::parse_condition_unchecked(text) {
            assert!(condition_text(&c).is_err(), "{text}");
        }
    }
    // An unbound variable is not closed.
    assert!(parse_leaf_condition(r#"Drupe::Action::"Login"::request{ input.user: u }"#).is_err());
}

/// **The slice of an action**: the leaves whose rule's scope can apply to it,
/// in leaf order, the same every time; a leaf over an action list that can
/// apply is sent with its scope narrowed to the action.
#[test]
fn the_slice_of_an_action() {
    let set = lowered();
    let ids: Vec<String> = set
        .nonrelativized_temporal_fields()
        .map(|f| f.id.clone())
        .collect();
    let alert = set.temporal_slice(&drupe("Alert")).expect("a slice");
    assert_eq!(
        alert.iter().map(|d| d.id.clone()).collect::<Vec<_>>(),
        vec![ids[0].clone(), ids[1].clone()]
    );
    assert_eq!(alert[0].action, ActionScope::Concrete(drupe("Alert")));
    assert_eq!(alert[1].action, ActionScope::Unconstrained);
    assert_eq!(set.temporal_slice(&drupe("Alert")), Ok(alert.clone()));
    // Each condition is the authored leaf's text: its parse, pinned, is the
    // set's leaf.
    let schema = &set.lowered().event_schema;
    for (d, leaf) in alert.iter().zip(set.nonrelativized_temporal_fields()) {
        let mut parsed = parse_leaf_condition(&d.condition).expect("parses");
        inject_pins(&mut parsed, schema);
        assert_eq!(
            without_spans(&parsed),
            without_spans(&leaf.condition.condition)
        );
    }
    // `Read` and `Login` reach the third rule, over an action list: its leaf is
    // sent with the action as its scope, after the unconstrained rule's.
    for action in ["Read", "Login"] {
        let slice = set.temporal_slice(&drupe(action)).expect("a slice");
        assert_eq!(
            slice.iter().map(|d| d.id.clone()).collect::<Vec<_>>(),
            vec![ids[1].clone(), ids[2].clone()]
        );
        assert_eq!(slice[0].action, ActionScope::Unconstrained);
        assert_eq!(slice[1].action, ActionScope::Concrete(drupe(action)));
        assert_eq!(set.temporal_slice(&drupe(action)), Ok(slice.clone()));
        let leaf = set
            .nonrelativized_temporal_fields()
            .nth(2)
            .expect("the third leaf");
        let mut parsed = parse_leaf_condition(&slice[1].condition).expect("parses");
        inject_pins(&mut parsed, schema);
        assert_eq!(
            without_spans(&parsed),
            without_spans(&leaf.condition.condition)
        );
    }
    // An action no scope names gets the unconstrained rule's leaf alone.
    let other = set.temporal_slice(&drupe("Other")).expect("a slice");
    assert_eq!(
        other.iter().map(|d| d.id.clone()).collect::<Vec<_>>(),
        vec![ids[1].clone()]
    );
}

/// A predicate that does not end with its event's pins has no authored form.
#[test]
fn missing_pins_do_not_strip() {
    let set = lowered();
    let schema = &set.lowered().event_schema;
    let bare =
        parse_condition(r#"formerly within 1h Drupe::Action::"Login"::request{}"#).expect("parses");
    // Under the default schema, `request` pins `callerPrincipal`.
    assert!(strip_pins(&bare, schema).is_none());
    let mut pinned = bare.clone();
    inject_pins(&mut pinned, schema);
    assert_eq!(strip_pins(&pinned, schema), Some(bare));
}

// ─── Slices of rules scoped by action groups and action lists ─────────────

/// A two-level action hierarchy (`All` holds the group `Reads` and the action
/// `Write`; `Reads` holds `Read` and `Peek`), a group that is also appliable
/// (`Hub`, whose member is `Spoke`), a group no action is in (`Empty`), and an
/// action outside every group (`Solo`). `tag` is a `String` on every action.
const GROUPS_SCHEMA: &str = r#"namespace W {
  type LongIn = { amount: Long, tag: String };
  type StrIn  = { amount: String, tag: String };
  type ReadIn = { amount: Long, tag: String, readonly: Long };
  entity Gateway;
  entity Staff   = { id: String, tier: Long };
  action "All";
  action "Reads" in [All];
  action "Empty";
  action "Read" in [Reads] appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: ReadIn } };
  action "Peek" in [Reads] appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: StrIn } };
  action "Write" in [All] appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: LongIn } };
  action "Solo" appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: LongIn } };
  action "Hub" in [All] appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: LongIn } };
  action "Spoke" in [Hub] appliesTo {
    principal: [Staff], resource: [Gateway], context: { input: StrIn } };
}"#;

/// The event schema of [`GROUPS_SCHEMA`]'s traces, unpinned: one trace.
const GROUPS_EVENTS: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
event <A>::response {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

/// The same, pinned to the caller: one trace per principal, and every
/// predicate carries the pin.
const GROUPS_EVENTS_PINNED: &str = r#"
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:  resourceType(A),
    requestId:       String,
}
event <A>::response {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

/// One rule per kind of scope, in this order (the leaf ids follow it):
///
/// 0. a group (`in [Reads]`);
/// 1. a nested group (`in [All]`), through a macro whose binder expansion
///    generates;
/// 2. a list mixing a group and an action (`in [Reads, Solo]`);
/// 3. a list of actions (`in [Write, Solo]`);
/// 4. an unconstrained scope;
/// 5. `== Solo`;
/// 6. a group that is also appliable (`in [Hub]`).
///
/// Rule `permit (principal, action in [All], resource)` has no leaf, and
/// lets the forbids decide.
const GROUPS_POLICIES: &str = r#"
def temporal count_formerly(?w, ?s) {
    count for ($t: Timepoint). where (formerly within ?w (?s && tp($t)))
};

permit (principal, action in [W::Action::"All"], resource);

permit (principal, action in [W::Action::"Reads"], resource)
when temporal { formerly within 1h W::Action::"Read"::request{ input.tag: context.input.tag } };

forbid (principal, action in [W::Action::"All"], resource)
when temporal {
    exists (n: Long). ((count_formerly(1h, W::Action::"Write"::request{})) == n && n > 2)
};

forbid (principal, action in [W::Action::"Reads", W::Action::"Solo"], resource)
when temporal { formerly within 1h W::Action::"Solo"::response{ input.tag: context.input.tag } };

forbid (principal, action in [W::Action::"Write", W::Action::"Solo"], resource)
when temporal { formerly within 1h W::Action::"Peek"::request{ input.tag: context.input.tag } };

forbid (principal, action, resource)
when temporal {
    (count for (t: Timepoint). where formerly within 1h (W::Action::"Hub"::request{} && tp(t))) > 3
};

permit (principal, action == W::Action::"Solo", resource)
when temporal { formerly within 1h W::Action::"Read"::request{} };

forbid (principal, action in [W::Action::"Hub"], resource)
when temporal { formerly within 1h W::Action::"Spoke"::response{ input.tag: context.input.tag } };
"#;

fn groups_set(event_schema: &str) -> LoweredPolicySet {
    let service = ServiceSchema::builder()
        .event_schema_str(event_schema)
        .build()
        .expect("the event schema");
    let schema = PolicySchema::from_cedarschema_str(GROUPS_SCHEMA).expect("the schema");
    let set =
        LoweredPolicySet::from_str(GROUPS_POLICIES, &service, &schema).expect("the policies lower");
    let errors: Vec<String> = crate::Validator::new()
        .validate(&set)
        .validation_errors()
        .map(|e| e.to_string())
        .collect();
    assert!(errors.is_empty(), "the policies validate: {errors:?}");
    set
}

fn w(id: &str) -> ActionRef {
    ActionRef {
        namespace: Some("W".to_owned()),
        id: id.to_owned(),
    }
}

/// The action of an event (its namespace without the `Action` segment).
fn action_of(event: &crate::Event) -> ActionRef {
    let mut ns = event.namespace().to_vec();
    ns.pop();
    ActionRef {
        namespace: (!ns.is_empty()).then(|| ns.join("::")),
        id: event.action().to_owned(),
    }
}

/// **The leaves an evaluator makes of a slice**: each descriptor's id and
/// scope, and its text parsed with the event schema's pins injected, as an
/// evaluator of temporal fields that lowers nothing itself makes them. The
/// rest of each leaf is the set's.
fn leaves_of_slice(
    set: &LoweredPolicySet,
    slice: &[crate::TemporalLeafDescriptor],
) -> Vec<crate::TemporalField> {
    let schema = &set.lowered().event_schema;
    slice
        .iter()
        .map(|d| {
            let mut leaf = set
                .nonrelativized_temporal_fields()
                .find(|f| f.id == d.id)
                .expect("a leaf of the set")
                .clone();
            let mut condition = parse_leaf_condition(&d.condition).expect("the text parses");
            inject_pins(&mut condition, schema);
            if let ActionScope::Concrete(a) = &d.action {
                leaf.target_actions = vec![a.clone()];
            }
            leaf.action = d.action.clone();
            leaf.condition.condition = condition;
            leaf
        })
        .collect()
}

/// A trace over the six appliable actions: requests and responses, by three
/// principals, with two tags, some minutes apart, so that each 1h
/// window holds several events and every leaf both holds and fails.
fn groups_trace() -> String {
    const ACTIONS: [(&str, &str); 6] = [
        ("Read", "amount: 1, tag: \"{tag}\", readonly: 0"),
        ("Peek", "amount: \"1\", tag: \"{tag}\""),
        ("Write", "amount: 1, tag: \"{tag}\""),
        ("Solo", "amount: 1, tag: \"{tag}\""),
        ("Hub", "amount: 1, tag: \"{tag}\""),
        ("Spoke", "amount: \"1\", tag: \"{tag}\""),
    ];
    let mut lines = Vec::new();
    let mut seed: u64 = 0x5eed;
    let mut next = |n: u64| {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (seed >> 33) % n
    };
    let mut ts = 0;
    for k in 0..240 {
        ts += 300 + 60 * next(10);
        let (action, input) = ACTIONS[next(6) as usize];
        let input = input.replace("{tag}", if next(2) == 0 { "x" } else { "y" });
        let (principal, entity) = match next(3) {
            0 => ("W::Staff::\"t\"", "W::Staff::\"t\": { id: \"t\", tier: 2 }"),
            1 => ("W::Staff::\"u\"", "W::Staff::\"u\": { id: \"u\", tier: 3 }"),
            _ => ("W::Staff::\"s\"", "W::Staff::\"s\": { id: \"s\", tier: 1 }"),
        };
        let kind = if next(3) == 0 { "response" } else { "request" };
        let context = if kind == "request" {
            format!(" entities({entity}) request_context(input: {{ {input} }})")
        } else {
            String::new()
        };
        lines.push(format!(
            "@{ts} scope(principal: {principal}, resource: W::Gateway::\"gw\"){context} \
             W::Action::\"{action}\"::{kind}(input: {{ {input} }}, callerPrincipal: {principal}, \
             callerResource: W::Gateway::\"gw\", requestId: \"r{k}\")"
        ));
    }
    lines.join("\n")
}

/// What [`slices_agree`] compared.
#[derive(Debug, Default)]
struct Agreement {
    /// Decisions, and the slice verdicts compared at them.
    decisions: usize,
    compared: usize,
    /// Of those, the verdicts that held, and the verdicts of leaves sent with a
    /// narrowed scope (a rule over an action list), and how many of them held.
    held: usize,
    narrowed: usize,
    narrowed_held: usize,
    /// The decisions made with the slices' verdicts alone that were `Deny`s and
    /// `Allow`s.
    denies: usize,
    allows: usize,
}

/// A temporal engine that decides each decision with the verdicts of its
/// action's slice alone, every other leaf `false`, as a caller that sends each
/// decision's slice to an evaluator of temporal fields and binds the verdicts
/// it gets back. Each action's slice is evaluated by its own interpreter over
/// the whole history, from the leaves the evaluator makes of the slice
/// ([`leaves_of_slice`]). With `drop_narrowed`, the leaves sent with a narrowed
/// scope are left out of every slice (the negative control).
struct SliceDecider {
    keys: Vec<crate::PartitionKey>,
    slices: Vec<(
        ActionRef,
        Vec<crate::TemporalField>,
        crate::InMemoryTemporalEngine,
    )>,
    ids: Vec<crate::ExtensionId>,
    last: Option<ActionRef>,
}

impl SliceDecider {
    fn new(set: &LoweredPolicySet, actions: &[ActionRef], drop_narrowed: bool) -> Self {
        let slices = actions
            .iter()
            .map(|a| {
                let mut slice = set.temporal_slice(a).expect("a slice");
                if drop_narrowed {
                    slice.retain(|d| {
                        set.nonrelativized_temporal_fields()
                            .any(|f| f.id == d.id && !matches!(f.action, ActionScope::List(_)))
                    });
                }
                let leaves = leaves_of_slice(set, &slice);
                (a.clone(), leaves, crate::InMemoryTemporalEngine::new())
            })
            .collect();
        SliceDecider {
            keys: Vec::new(),
            slices,
            ids: Vec::new(),
            last: None,
        }
    }
}

impl crate::TemporalEngine for SliceDecider {
    fn prepare(
        &mut self,
        leaves: &[crate::TemporalField],
        schema: &cedar_policy::Schema,
        events: &[crate::EventSignature],
    ) -> Result<(), crate::Error> {
        self.ids = leaves.iter().map(|f| f.id.clone()).collect();
        for (_, slice, engine) in &mut self.slices {
            crate::TemporalEngine::set_partition_keys(engine, &self.keys);
            crate::TemporalEngine::prepare(engine, slice, schema, events)?;
        }
        Ok(())
    }

    fn observe(&mut self, event: &crate::Event) {
        self.last = Some(action_of(event));
        for (_, _, engine) in &mut self.slices {
            crate::TemporalEngine::observe(engine, event);
        }
    }

    fn evaluate(&mut self) -> Result<crate::TemporalBindings, String> {
        let last = self.last.clone().ok_or("no event observed")?;
        let verdicts = match self.slices.iter_mut().find(|(a, _, _)| *a == last) {
            Some((_, _, engine)) => crate::TemporalEngine::evaluate(engine)?,
            None => crate::TemporalBindings::new(),
        };
        Ok(self
            .ids
            .iter()
            .map(|id| (id.clone(), verdicts.get(id).copied().unwrap_or(false)))
            .collect())
    }

    fn supports_partitioning(&self) -> bool {
        true
    }

    fn set_partition_keys(&mut self, keys: &[crate::PartitionKey]) {
        self.keys = keys.to_vec();
    }
}

/// What the authorizer answered an event: a decision and its errors, a
/// history event ingested, or a rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Answer {
    Decided(crate::Decision, Vec<String>),
    Ingested,
    Rejected(String),
}

/// The answer to every event, under partitioned evaluation, with `engine` (or
/// the interpreter).
fn answers(
    set: &LoweredPolicySet,
    events: &[crate::Event],
    engine: Option<SliceDecider>,
) -> Result<Vec<Answer>, String> {
    let mut b = crate::Authorizer::builder(set.clone()).partition_temporal();
    if let Some(e) = engine {
        b = b.temporal_engine(e);
    }
    let mut authz = b.build().map_err(|e| format!("the authorizer: {e}"))?;
    Ok(events
        .iter()
        .map(|e| match authz.submit(e) {
            Ok(Some(r)) => Answer::Decided(
                r.decision(),
                r.diagnostics().errors().map(str::to_owned).collect(),
            ),
            Ok(None) => Answer::Ingested,
            Err(e) => Answer::Rejected(format!("{e:?}")),
        })
        .collect())
}

/// The decision of every event, under partitioned evaluation, with `engine`
/// (or the interpreter); a rejected event or a decision with errors is a
/// failure.
fn decisions(
    set: &LoweredPolicySet,
    events: &[crate::Event],
    engine: Option<SliceDecider>,
) -> Result<Vec<Option<crate::Decision>>, String> {
    answers(set, events, engine)?
        .into_iter()
        .enumerate()
        .map(|(k, a)| match a {
            Answer::Decided(d, errors) if errors.is_empty() => Ok(Some(d)),
            Answer::Decided(_, errors) => Err(format!("event {k}: decided with errors {errors:?}")),
            Answer::Ingested => Ok(None),
            Answer::Rejected(e) => Err(format!("event {k}: rejected: {e}")),
        })
        .collect()
}

/// **The slices agree with the set**, over `events`, under partitioned
/// evaluation (one trace per partition, the leaves as authored), with the
/// interpreter:
///
/// * at each decision, each leaf of its action's slice, made from the slice as
///   an evaluator makes it ([`leaves_of_slice`]), has the verdict the set's own
///   leaf has;
/// * each decision made with the verdicts of its action's slice alone, every
///   other leaf `false`, is the set's decision.
fn slices_agree(set: &LoweredPolicySet, events: &[crate::Event]) -> Result<Agreement, Vec<String>> {
    use crate::TemporalEngine;
    let mut failures = Vec::new();
    let mut actions: Vec<ActionRef> = Vec::new();
    for e in events {
        let a = action_of(e);
        if set.is_decision_kind(e.kind()) && !actions.contains(&a) {
            actions.push(a);
        }
    }
    let keys = set.partition_keys().to_vec();
    let full: Vec<crate::TemporalField> = set.nonrelativized_temporal_fields().cloned().collect();
    let mut whole = crate::InMemoryTemporalEngine::new();
    whole.set_partition_keys(&keys);
    whole
        .prepare(&full, set.cedar_schema(), &[])
        .expect("the interpreter prepares");
    let mut sliced = Vec::new();
    for a in &actions {
        let slice = match set.temporal_slice(a) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!("the slice of {a:?}: {e}"));
                continue;
            }
        };
        let narrowed: Vec<bool> = slice
            .iter()
            .map(|d| {
                set.nonrelativized_temporal_fields()
                    .any(|f| f.id == d.id && matches!(f.action, ActionScope::List(_)))
            })
            .collect();
        let leaves = leaves_of_slice(set, &slice);
        let mut engine = crate::InMemoryTemporalEngine::new();
        engine.set_partition_keys(&keys);
        engine
            .prepare(&leaves, set.cedar_schema(), &[])
            .expect("the interpreter prepares");
        sliced.push((a.clone(), leaves, narrowed, engine));
    }
    let mut n = Agreement::default();
    for (k, e) in events.iter().enumerate() {
        whole.observe(e);
        for (_, _, _, engine) in &mut sliced {
            engine.observe(e);
        }
        if !set.is_decision_kind(e.kind()) {
            continue;
        }
        let a = action_of(e);
        let Some((_, leaves, narrowed, engine)) = sliced.iter_mut().find(|(x, ..)| *x == a) else {
            continue;
        };
        n.decisions += 1;
        let want = whole.evaluate().expect("the set's verdicts");
        let got = engine.evaluate().expect("the slice's verdicts");
        for (leaf, narrowed) in leaves.iter().zip(narrowed.iter()) {
            let (w, g) = (want.get(&leaf.id), got.get(&leaf.id));
            if w.is_none() || w != g {
                failures.push(format!(
                    "event {k} ({}): leaf {}: the set's verdict {w:?}, the slice's {g:?}",
                    a.id, leaf.id
                ));
            }
            n.compared += 1;
            let held = g == Some(&true);
            n.held += usize::from(held);
            if *narrowed {
                n.narrowed += 1;
                n.narrowed_held += usize::from(held);
            }
        }
    }
    match (
        answers(set, events, None),
        answers(set, events, Some(SliceDecider::new(set, &actions, false))),
    ) {
        (Ok(want), Ok(got)) => {
            for (k, (w, g)) in want.iter().zip(&got).enumerate() {
                if w != g {
                    failures.push(format!(
                        "event {k}: the set answers {w:?}, the slices' verdicts {g:?}"
                    ));
                }
                n.denies += usize::from(matches!(g, Answer::Decided(crate::Decision::Deny, _)));
                n.allows += usize::from(matches!(g, Answer::Decided(crate::Decision::Allow, _)));
            }
        }
        (w, g) => failures.push(format!("the decisions: {:?} / {:?}", w.err(), g.err())),
    }
    if failures.is_empty() {
        Ok(n)
    } else {
        Err(failures)
    }
}

/// **The slice of each action of a set scoped by groups and lists**: the leaves
/// of the rules that can apply to it, in leaf order, each rule over a list or
/// a group sent with its scope narrowed to the action; each text parses back
/// to the authored condition, and with the pins injected is the set's leaf.
#[test]
fn the_slice_narrows_groups_and_lists() {
    for events in [GROUPS_EVENTS, GROUPS_EVENTS_PINNED] {
        let set = groups_set(events);
        let fields: Vec<&crate::TemporalField> = set.nonrelativized_temporal_fields().collect();
        let ids: Vec<String> = fields.iter().map(|f| f.id.clone()).collect();
        assert_eq!(ids.len(), 7);
        let derived = &set.lowered().event_schema;
        // (the action, the rules whose leaves its slice holds)
        let expected: [(&str, &[usize]); 10] = [
            // a member of `Reads` and, through it, of `All`
            ("Read", &[0, 1, 2, 4]),
            ("Peek", &[0, 1, 2, 4]),
            // a member of `All`, and listed with `Solo`
            ("Write", &[1, 3, 4]),
            // in no group; listed twice, and named by `==`
            ("Solo", &[2, 3, 4, 5]),
            // an appliable group: in `All`, and in its own `in [Hub]`
            ("Hub", &[1, 4, 6]),
            // a member of `Hub`, so of `All` too
            ("Spoke", &[1, 4, 6]),
            // a pure group a list names: the lists that name it; the group
            // `All` holds it but does not resolve to it. No request can name a
            // pure group (it applies to no principal, so its decision fails
            // closed), so no decision reads these two slices
            ("Reads", &[0, 2, 4]),
            ("All", &[1, 4]),
            // a group no action is in, and an action the schema does not
            // declare: the unconstrained rule's leaf alone
            ("Empty", &[4]),
            ("Other", &[4]),
        ];
        for (action, rules) in expected {
            let a = w(action);
            let slice = set.temporal_slice(&a).expect("a slice");
            let got: Vec<String> = slice.iter().map(|d| d.id.clone()).collect();
            let want: Vec<String> = rules.iter().map(|&r| ids[r].clone()).collect();
            assert_eq!(got, want, "the slice of {action}");
            assert_eq!(
                set.temporal_slice(&a),
                Ok(slice.clone()),
                "{action}: the same again"
            );
            for d in &slice {
                let leaf = fields
                    .iter()
                    .find(|f| f.id == d.id)
                    .expect("a leaf of the set");
                let scope = match &leaf.action {
                    ActionScope::List(_) => ActionScope::Concrete(a.clone()),
                    s => s.clone(),
                };
                assert_eq!(d.action, scope, "{action}: the scope of {}", d.id);
                assert!(!matches!(d.action, ActionScope::List(_)));
                let authored = strip_pins(&leaf.condition.condition, derived).expect("pins off");
                let back = parse_leaf_condition(&d.condition).expect("the text parses");
                assert_eq!(
                    without_spans(&back),
                    without_spans(&authored),
                    "{action}: {}",
                    d.id
                );
                assert_eq!(condition_text(&back).as_deref(), Ok(d.condition.as_str()));
                let mut pinned = back;
                inject_pins(&mut pinned, derived);
                assert_eq!(
                    without_spans(&pinned),
                    without_spans(&leaf.condition.condition),
                    "{action}: {} with its pins",
                    d.id
                );
            }
        }
        // The macro's generated binder survives the narrowing.
        let write = set.temporal_slice(&w("Write")).expect("a slice");
        assert!(write[0].condition.contains("$t$"), "{}", write[0].condition);
    }
}

/// **The groups whose scope resolves to each action of [`GROUPS_SCHEMA`]**,
/// transitively: none for an action outside every group, for a pure group (its
/// enclosing group resolves to its members, not to it), for a group no action
/// is in, and for an action the schema does not declare (in another namespace
/// too).
#[test]
fn the_groups_of_an_action() {
    let set = groups_set(GROUPS_EVENTS);
    let expected: [(&str, &[&str]); 10] = [
        ("Read", &["All", "Reads"]),
        ("Peek", &["All", "Reads"]),
        ("Write", &["All"]),
        ("Solo", &[]),
        ("Hub", &["All"]),
        ("Spoke", &["All", "Hub"]),
        ("Reads", &[]),
        ("All", &[]),
        ("Empty", &[]),
        ("Other", &[]),
    ];
    for (action, groups) in expected {
        let want: Vec<ActionRef> = groups.iter().map(|g| w(g)).collect();
        assert_eq!(
            set.action_groups(&w(action)),
            want,
            "the groups of {action}"
        );
    }
    let unnamespaced = ActionRef {
        namespace: None,
        id: "Read".to_owned(),
    };
    assert_eq!(set.action_groups(&unnamespaced), Vec::<ActionRef>::new());
}

/// **The groups of an action across namespaces**, on a set lowered from no
/// policies: an action in two groups of its namespace, one of them nested in a
/// group of another namespace, and an unnamespaced action in an unnamespaced
/// group.
#[test]
fn the_groups_of_an_action_across_namespaces() {
    const SCHEMA: &str = r#"
namespace B { action "Top"; }
namespace A {
  entity U;
  action "G1" in [B::Action::"Top"];
  action "G2";
  action "X" in [G1, G2] appliesTo { principal: [U], resource: [U] };
}
entity V;
action "TG";
action "T" in [Action::"TG"] appliesTo { principal: [V], resource: [V] };
"#;
    let service = ServiceSchema::builder()
        .build()
        .expect("the service schema");
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("the schema");
    let set = LoweredPolicySet::from_str("", &service, &schema).expect("no policies lower");
    let a = |ns: Option<&str>, id: &str| ActionRef {
        namespace: ns.map(str::to_owned),
        id: id.to_owned(),
    };
    assert_eq!(
        set.action_groups(&a(Some("A"), "X")),
        vec![a(Some("A"), "G1"), a(Some("A"), "G2"), a(Some("B"), "Top")]
    );
    assert_eq!(set.action_groups(&a(None, "T")), vec![a(None, "TG")]);
    assert_eq!(set.action_groups(&a(Some("B"), "X")), vec![]);
    assert_eq!(set.action_groups(&a(Some("A"), "G1")), vec![]);
}

/// **The scope a leaf is sent under**, for each shape of scope: an unconstrained
/// scope applies as it is; `==` applies to the action it names and to no
/// member of it; a list applies, narrowed to the action, when it names the
/// action or one of its groups, and to nothing else.
#[test]
fn a_scope_narrowed_to_an_action() {
    let (read, reads, all, solo) = (w("Read"), w("Reads"), w("All"), w("Solo"));
    let groups = [all.clone(), reads.clone()];
    let concrete = |a: &ActionRef| Some(ActionScope::Concrete(a.clone()));
    let list = |v: &[&ActionRef]| ActionScope::List(v.iter().map(|&a| a.clone()).collect());
    assert_eq!(
        ActionScope::Unconstrained.narrowed_to(&read, &groups),
        Some(ActionScope::Unconstrained)
    );
    assert_eq!(
        ActionScope::Unconstrained.narrowed_to(&w("Other"), &[]),
        Some(ActionScope::Unconstrained)
    );
    assert_eq!(
        ActionScope::Concrete(read.clone()).narrowed_to(&read, &groups),
        concrete(&read)
    );
    assert_eq!(
        ActionScope::Concrete(reads.clone()).narrowed_to(&read, &groups),
        None
    );
    assert_eq!(
        ActionScope::Concrete(solo.clone()).narrowed_to(&read, &groups),
        None
    );
    // named, through a group, through a nested group, next to a member
    assert_eq!(list(&[&read]).narrowed_to(&read, &groups), concrete(&read));
    assert_eq!(
        list(&[&reads, &solo]).narrowed_to(&read, &groups),
        concrete(&read)
    );
    assert_eq!(list(&[&all]).narrowed_to(&read, &groups), concrete(&read));
    assert_eq!(
        list(&[&reads, &read]).narrowed_to(&read, &groups),
        concrete(&read)
    );
    assert_eq!(list(&[&solo]).narrowed_to(&read, &groups), None);
    assert_eq!(list(&[]).narrowed_to(&read, &groups), None);
    // a pure group, or an undeclared action, has no groups: only a list
    // naming it applies
    assert_eq!(list(&[&all]).narrowed_to(&reads, &[]), None);
    assert_eq!(list(&[&reads]).narrowed_to(&reads, &[]), concrete(&reads));
    assert_eq!(
        list(&[&w("Other")]).narrowed_to(&w("Other"), &[]),
        concrete(&w("Other"))
    );
}

/// **The shared rule is the slice's, and the scope's resolution**: for every
/// leaf of the action-group set and every action (each declared one, each one
/// a scope names, and one the schema does not declare),
/// [`ActionScope::narrowed_to`] with [`LoweredPolicySet::action_groups`]
/// applies exactly when the rule names the action or resolves to it
/// ([`TemporalField::target_actions`](crate::TemporalField::target_actions)),
/// and agrees with [`LoweredPolicySet::temporal_slice`] on membership and scope.
#[test]
fn the_shared_rule_is_the_slice() {
    for events in [GROUPS_EVENTS, GROUPS_EVENTS_PINNED] {
        let set = groups_set(events);
        let mut actions: Vec<ActionRef> = [
            "All", "Reads", "Empty", "Read", "Peek", "Write", "Solo", "Hub", "Spoke", "Other",
        ]
        .iter()
        .map(|a| w(a))
        .collect();
        actions.push(ActionRef {
            namespace: None,
            id: "Read".to_owned(),
        });
        for action in &actions {
            let groups = set.action_groups(action);
            let slice = set.temporal_slice(action).expect("a slice");
            let mut sent = slice.iter();
            for leaf in set.nonrelativized_temporal_fields() {
                let shared = leaf.action.narrowed_to(action, &groups);
                let resolved = match &leaf.action {
                    ActionScope::Unconstrained => Some(ActionScope::Unconstrained),
                    ActionScope::Concrete(a) => (a == action).then(|| leaf.action.clone()),
                    ActionScope::List(l) => (l.contains(action)
                        || leaf.target_actions.contains(action))
                    .then(|| ActionScope::Concrete(action.clone())),
                };
                assert_eq!(shared, resolved, "{action:?}: {}", leaf.id);
                if let Some(scope) = shared {
                    let d = sent.next().expect("the slice holds the leaf");
                    assert_eq!((&d.id, &d.action), (&leaf.id, &scope), "{action:?}");
                }
            }
            assert!(sent.next().is_none(), "{action:?}: the slice holds more");
        }
    }
}

/// **The slices decide as the set**, over a trace of every appliable action,
/// unpinned and pinned: at each decision, each leaf of its action's slice (sent
/// as text, parsed, pinned) has the set's verdict, the narrowed leaves among
/// them; and the decisions made with the slices' verdicts alone are the set's.
/// Without the narrowed leaves they are not (the negative control).
#[test]
fn the_slices_decide_as_the_set() {
    for events in [GROUPS_EVENTS, GROUPS_EVENTS_PINNED] {
        let set = groups_set(events);
        let trace = crate::parse_trace(&groups_trace()).expect("the trace parses");
        let n = slices_agree(&set, &trace).unwrap_or_else(|f| panic!("{}", f.join("\n")));
        eprintln!("{n:?}");
        decisions(&set, &trace, None).expect("every event conforms and decides without errors");
        assert!(n.decisions > 100, "{n:?}");
        assert!(n.held > 0 && n.held < n.compared, "{n:?}");
        assert!(n.narrowed > 0 && n.narrowed_held > 0, "{n:?}");
        assert!(n.narrowed_held < n.narrowed, "{n:?}");
        assert!(n.denies > 0 && n.allows > 0, "{n:?}");
        // The leaves the slices narrow decide some decision: without them, the
        // slices decide otherwise.
        let mut actions: Vec<ActionRef> = Vec::new();
        for e in &trace {
            if set.is_decision_kind(e.kind()) && !actions.contains(&action_of(e)) {
                actions.push(action_of(e));
            }
        }
        let want = decisions(&set, &trace, None).expect("decisions");
        let without = decisions(&set, &trace, Some(SliceDecider::new(&set, &actions, true)))
            .expect("decisions");
        assert_ne!(want, without, "the narrowed leaves decide nothing");
    }
}

/// **Every leaf of the corpora**, under the case's event schema and under the
/// default one: the pins come off and go back on; the authored leaf has a
/// canonical text, which parses back as it and prints the same again; and the
/// slice of every action a leaf can apply to, and of every action the schema
/// declares, is the leaves whose scope can
/// apply to it, in order, every time, each sent under its rule's scope or, for
/// a rule over an action list, under the action, its text the leaf's.
#[cfg(feature = "corpus")]
#[test]
fn every_corpus_leaf_reads_back_from_its_text() {
    use crate::corpus::{TemporalCategory, macro_cases, mixed_cases, temporal_cases};
    type Case = (String, String, String, Option<String>, Option<String>);
    let mut cases: Vec<Case> = Vec::new();
    for c in temporal_cases() {
        if c.category == TemporalCategory::Passing {
            cases.push((c.name, c.policy_src, c.schema_src, c.event_schema_src, None));
        }
    }
    for c in macro_cases() {
        cases.push((
            c.name,
            c.policy_src,
            c.schema_src,
            c.event_schema_src,
            c.macros_src,
        ));
    }
    for c in mixed_cases() {
        cases.push((c.name, c.policy_src, c.schema_src, c.event_schema_src, None));
    }
    let (mut sets, mut leaves, mut generated, mut slices, mut narrowed) = (0, 0, 0, 0, 0);
    let mut failures = Vec::new();
    for (name, policy, schema_src, event_schema, macros) in &cases {
        let Ok(schema) = PolicySchema::from_cedarschema_str(schema_src) else {
            continue;
        };
        for event in [event_schema.as_deref(), None] {
            let mut b = ServiceSchema::builder();
            if let Some(e) = event {
                b = b.event_schema_str(e);
            }
            if let Some(m) = macros {
                b = b.macros_str(m);
            }
            let Ok(service) = b.build() else { continue };
            let Ok(set) = LoweredPolicySet::from_str(policy, &service, &schema) else {
                continue;
            };
            sets += 1;
            let derived = &set.lowered().event_schema;
            let mut actions: Vec<ActionRef> = Vec::new();
            for leaf in set.nonrelativized_temporal_fields() {
                leaves += 1;
                let pinned = &leaf.condition.condition;
                let Some(authored) = strip_pins(pinned, derived) else {
                    failures.push(format!("{name}: {}: the pins do not come off", leaf.id));
                    continue;
                };
                let mut again = authored.clone();
                inject_pins(&mut again, derived);
                if &again != pinned {
                    failures.push(format!("{name}: {}: the pins do not go back on", leaf.id));
                }
                let text = match condition_text(&authored) {
                    Ok(t) => t,
                    Err(e) => {
                        failures.push(format!("{name}: {}: no text: {e}", leaf.id));
                        continue;
                    }
                };
                generated += usize::from(text.contains('$'));
                match parse_leaf_condition(&text) {
                    Ok(back) => {
                        if without_spans(&back) != without_spans(&authored) {
                            failures.push(format!("{name}: {}: reads back otherwise", leaf.id));
                        }
                        if condition_text(&back).as_deref() != Ok(text.as_str()) {
                            failures.push(format!("{name}: {}: prints otherwise", leaf.id));
                        }
                    }
                    Err(e) => failures.push(format!("{name}: {}: does not parse: {e}", leaf.id)),
                }
                for a in &leaf.target_actions {
                    if !actions.contains(a) {
                        actions.push(a.clone());
                    }
                }
                if let ActionScope::Concrete(a) = &leaf.action
                    && !actions.contains(a)
                {
                    actions.push(a.clone());
                }
            }
            for leaf in set.nonrelativized_temporal_fields() {
                if let ActionScope::List(l) = &leaf.action {
                    for a in l {
                        if !actions.contains(a) {
                            actions.push(a.clone());
                        }
                    }
                }
            }
            // Every action the schema declares, pure groups among them.
            for uid in set.cedar_schema().actions() {
                let ns = uid.type_name().namespace();
                let a = crate::api::action_ref(ns, uid.id().unescaped().to_owned());
                if !actions.contains(&a) {
                    actions.push(a);
                }
            }
            for action in &actions {
                // Each leaf whose rule's scope can apply to `action`, with the
                // scope it is sent under.
                let expected: Vec<_> = set
                    .nonrelativized_temporal_fields()
                    .filter_map(|f| {
                        let scope = match &f.action {
                            ActionScope::Unconstrained => ActionScope::Unconstrained,
                            ActionScope::Concrete(a) if a == action => f.action.clone(),
                            ActionScope::List(l)
                                if l.contains(action) || f.target_actions.contains(action) =>
                            {
                                ActionScope::Concrete(action.clone())
                            }
                            _ => return None,
                        };
                        Some((f, scope))
                    })
                    .collect();
                match set.temporal_slice(action) {
                    Ok(slice) => {
                        slices += 1;
                        let ids: Vec<_> = slice.iter().map(|d| d.id.clone()).collect();
                        let want: Vec<_> = expected.iter().map(|(f, _)| f.id.clone()).collect();
                        if ids != want {
                            failures.push(format!("{name}: the slice of {action:?} is {ids:?}"));
                        }
                        for (d, (f, scope)) in slice.iter().zip(&expected) {
                            if &d.action != scope {
                                failures.push(format!(
                                    "{name}: the slice of {action:?} sends {} under {:?}",
                                    d.id, d.action
                                ));
                            }
                            narrowed += usize::from(matches!(f.action, ActionScope::List(_)));
                            let back = parse_leaf_condition(&d.condition).map(|mut c| {
                                inject_pins(&mut c, derived);
                                without_spans(&c)
                            });
                            if back.as_ref() != Ok(&without_spans(&f.condition.condition)) {
                                failures.push(format!(
                                    "{name}: the slice of {action:?}: {} does not read back",
                                    d.id
                                ));
                            }
                        }
                        if set.temporal_slice(action) != Ok(slice) {
                            failures.push(format!("{name}: the slice of {action:?} varies"));
                        }
                    }
                    Err(e) => failures.push(format!("{name}: slice of {action:?}: {e}")),
                }
            }
        }
    }
    eprintln!(
        "leaf texts: {sets} lowered sets, {leaves} leaves ({generated} with generated binders), \
         {slices} slices, {narrowed} leaves sent with a list's scope narrowed to the action"
    );
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert!(
        generated > 0,
        "the corpora have leaves with generated binders"
    );
    assert!(narrowed > 0, "the corpora have rules over action lists");
}

/// **Every corpus slice decides as its set**: on every trace of the temporal,
/// macro and mixed corpora, under the case's event schema and under the default
/// one, the slices agree with the set ([`slices_agree`]): at each decision each
/// leaf of its action's slice, parsed from its text and pinned, has the set's
/// verdict, and the answers made with the slices' verdicts alone are the set's.
#[cfg(feature = "corpus")]
#[test]
fn every_corpus_slice_decides_as_the_set() {
    use crate::corpus::{TemporalCategory, macro_cases, mixed_cases, temporal_cases};
    type Case = (
        String,
        String,
        String,
        Option<String>,
        Option<String>,
        Vec<String>,
    );
    let mut cases: Vec<Case> = Vec::new();
    for c in temporal_cases() {
        if c.category == TemporalCategory::Passing {
            let traces = c.traces.into_iter().map(|t| t.trace_log).collect();
            cases.push((
                c.name,
                c.policy_src,
                c.schema_src,
                c.event_schema_src,
                None,
                traces,
            ));
        }
    }
    for c in macro_cases() {
        let traces = c.traces.into_iter().map(|t| t.trace_log).collect();
        cases.push((
            c.name,
            c.policy_src,
            c.schema_src,
            c.event_schema_src,
            c.macros_src,
            traces,
        ));
    }
    for c in mixed_cases() {
        let traces = c.traces.into_iter().map(|t| t.trace_log).collect();
        cases.push((
            c.name,
            c.policy_src,
            c.schema_src,
            c.event_schema_src,
            None,
            traces,
        ));
    }
    let mut total = Agreement::default();
    let (mut runs, mut listed) = (0, 0);
    let mut failures = Vec::new();
    for (name, policy, schema_src, event_schema, macros, traces) in &cases {
        let Ok(schema) = PolicySchema::from_cedarschema_str(schema_src) else {
            continue;
        };
        for event in [event_schema.as_deref(), None] {
            let mut b = ServiceSchema::builder();
            if let Some(e) = event {
                b = b.event_schema_str(e);
            }
            if let Some(m) = macros {
                b = b.macros_str(m);
            }
            let Ok(service) = b.build() else { continue };
            let Ok(set) = LoweredPolicySet::from_str(policy, &service, &schema) else {
                continue;
            };
            if set.nonrelativized_temporal_fields().next().is_none() {
                continue;
            }
            let lists = set
                .nonrelativized_temporal_fields()
                .any(|f| matches!(f.action, ActionScope::List(_)));
            for (ti, trace) in traces.iter().enumerate() {
                let Ok(events) = crate::parse_trace(trace) else {
                    continue;
                };
                // A set an authorizer cannot be built for (its validator
                // rejects it, say) has no decisions to compare.
                if crate::Authorizer::builder(set.clone())
                    .partition_temporal()
                    .build()
                    .is_err()
                {
                    continue;
                }
                runs += 1;
                listed += usize::from(lists);
                match slices_agree(&set, &events) {
                    Ok(n) => {
                        total.decisions += n.decisions;
                        total.compared += n.compared;
                        total.held += n.held;
                        total.narrowed += n.narrowed;
                        total.narrowed_held += n.narrowed_held;
                        total.denies += n.denies;
                        total.allows += n.allows;
                    }
                    Err(f) => {
                        for m in f {
                            let mode = if event.is_some() { "case" } else { "default" };
                            failures.push(format!("{name} [{mode}] trace {ti}: {m}"));
                        }
                    }
                }
            }
        }
    }
    eprintln!("slices vs sets: {runs} traces ({listed} of sets with action lists), {total:?}");
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert!(runs > 1_000, "only {runs} traces");
    assert!(total.narrowed_held > 0, "{total:?}");
}
