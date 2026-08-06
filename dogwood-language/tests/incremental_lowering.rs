//! Incremental / combinable lowering.
//!
//! The two-phase API ([`ParsedPolicySet::parse`] → `lower`) plus the
//! caller-supplied *distincter* lets a service lower sub-policies
//! independently — as they arrive, from different sources — and combine the
//! results into one Cedar `PolicySet` (e.g. an external Cedar policy store) without the
//! synthesized policy ids or the hoisted `context.<id>` field names colliding.
//!
//! These tests demonstrate:
//!   1. a distinct distincter yields non-colliding policy ids and field names
//!      across independent lowerings of the *same* source;
//!   2. the default (no distincter) path is `policy_<index>`;
//!   3. combining two independently-lowered Cedar policy sets into one
//!      succeeds (no duplicate-id rejection) and the rule mapping stays intact;
//!   4. one parsed set can be lowered against several action schemas;
//!   5. an augmented schema feeds forward into a later lowering (accretive);
//!   6. `decision_kinds` / `is_decision_kind` match the authorizer's gate;
//!   7. a non-identifier distincter is rejected up front;
//!   8. repeated feed-forward over a reference-style context that carries
//!      builtin types survives — the augmented schema Dogwood emits (with
//!      Cedar's reserved `__cedar::` spelling on inlined builtins) re-ingests
//!      cleanly, iteration after iteration (regression for the `__cedar`
//!      reserved-namespace schema-parse bug).

use dogwood_language::{
    Error, LoweredPolicySet, ParsedPolicySet, PolicySchema, ServiceSchema, Validator,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type ReadInput = { user: String };
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

// A pure-Cedar rule (no hoisted fields) and a temporal rule (one hoisted
// `context.<id>` field), so both the policy-id and the field-name namespaces
// are exercised.
const CEDAR_POLICY: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when { context.input.user == "alice" };
"#;

const TEMPORAL_POLICY: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Read"::request{
        input.user: context.input.user
    }
};
"#;

fn service() -> ServiceSchema {
    ServiceSchema::defaults()
}

fn policy_schema() -> PolicySchema {
    PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema")
}

/// Every policy id emitted by a lowered set.
fn policy_ids(set: &LoweredPolicySet) -> Vec<String> {
    set.rules().map(|r| r.cedar_policy_id).collect()
}

#[test]
fn default_distincter_is_policy_index() {
    let set =
        LoweredPolicySet::from_str(CEDAR_POLICY, &service(), &policy_schema()).expect("lowers");
    assert_eq!(policy_ids(&set), vec!["policy_0".to_string()]);
}

#[test]
fn distinct_distincters_yield_disjoint_policy_ids() {
    // The SAME source, lowered twice — but under different distincters — must
    // mint disjoint policy ids (this is exactly the collision the distincter
    // exists to prevent: with the default path both would be `policy_0`).
    let parsed = ParsedPolicySet::parse(CEDAR_POLICY, &service()).expect("parses");

    let a = parsed
        .lower_with_distincter(&policy_schema(), "storeA")
        .expect("lowers A");
    let b = parsed
        .lower_with_distincter(&policy_schema(), "storeB")
        .expect("lowers B");

    assert_eq!(policy_ids(&a), vec!["storeA_0".to_string()]);
    assert_eq!(policy_ids(&b), vec!["storeB_0".to_string()]);

    // Disjoint: no id appears in both.
    for id in policy_ids(&a) {
        assert!(
            !policy_ids(&b).contains(&id),
            "id `{id}` collides across independently-lowered sets"
        );
    }
}

#[test]
fn distinct_distincters_yield_disjoint_hoisted_field_names() {
    // The temporal policy hoists a `context.<id>` field. Two independent
    // lowerings under different distincters must produce different field names,
    // so combining them never silently overwrites one hoisted field with
    // another (the augmentation insert is keyed by the field name).
    let parsed = ParsedPolicySet::parse(TEMPORAL_POLICY, &service()).expect("parses");

    let a = parsed
        .lower_with_distincter(&policy_schema(), "storeA")
        .expect("lowers A");
    let b = parsed
        .lower_with_distincter(&policy_schema(), "storeB")
        .expect("lowers B");

    let a_fields: Vec<&str> = a.temporal_fields().map(|f| f.id.as_str()).collect();
    let b_fields: Vec<&str> = b.temporal_fields().map(|f| f.id.as_str()).collect();

    assert_eq!(a_fields.len(), 1, "one temporal leaf hoisted");
    assert_eq!(b_fields.len(), 1);
    assert!(
        a_fields[0].starts_with("storeA_0"),
        "field `{}` should be namespaced by its rule key",
        a_fields[0]
    );
    assert!(b_fields[0].starts_with("storeB_0"));
    assert_ne!(
        a_fields[0], b_fields[0],
        "hoisted field names must be disjoint across independently-lowered sets"
    );
}

#[test]
fn independently_lowered_sets_combine_into_one_cedar_policy_set() {
    // Lower two DIFFERENT policies independently, each with its own distincter,
    // then union their Cedar policies into a single `cedar_policy::PolicySet`.
    // Positional ids (`policy_0` in both) would collide on `add`; the distinct
    // rule keys make the union succeed.
    let parsed_a = ParsedPolicySet::parse(CEDAR_POLICY, &service()).expect("parses A");
    let parsed_b = ParsedPolicySet::parse(TEMPORAL_POLICY, &service()).expect("parses B");

    let a = parsed_a
        .lower_with_distincter(&policy_schema(), "ruleA")
        .expect("lowers A");
    let b = parsed_b
        .lower_with_distincter(&policy_schema(), "ruleB")
        .expect("lowers B");

    // Build a combined Cedar PolicySet from both lowerings' policies.
    let mut combined = cedar_policy::PolicySet::new();
    for p in a.as_cedar().policies() {
        combined
            .add(p.clone())
            .expect("no id collision adding A's policies");
    }
    for p in b.as_cedar().policies() {
        combined
            .add(p.clone())
            .expect("no id collision adding B's policies");
    }

    assert_eq!(
        combined.policies().count(),
        2,
        "both rules present in the combined set"
    );

    // The rule-id mappings from each set resolve against the combined ids.
    assert!(a.rule_ref("ruleA_0").is_some());
    assert!(b.rule_ref("ruleB_0").is_some());
    // And each set only knows its own ids.
    assert!(a.rule_ref("ruleB_0").is_none());
}

#[test]
fn one_parsed_set_lowers_against_several_action_schemas() {
    // Parse once (no action schema needed), then lower against two different
    // action schemas — the workflow the phase split is built for (the action
    // schema arrives late / varies).
    let parsed = ParsedPolicySet::parse(CEDAR_POLICY, &service()).expect("parses");

    // The base schema — the policy validates cleanly.
    let ok = parsed
        .lower(&policy_schema())
        .expect("lowers against base schema");
    assert!(Validator::new().validate(&ok).validation_passed());

    // A schema whose Read action has NO `user` input field — the same parsed
    // policy still lowers, but validation now flags the unknown attribute,
    // proving the second lowering really used the second action schema.
    const SCHEMA_NO_USER: &str = r#"
    namespace Drupe {
      type ReadInput = { other: String };
      entity Gateway;
      entity OAuthUser = { id: String } tags String;
      action "Read" appliesTo {
        principal: [OAuthUser],
        resource: [Gateway],
        context: { input: ReadInput }
      };
    }
    "#;
    let other_schema = PolicySchema::from_cedarschema_str(SCHEMA_NO_USER).expect("action schema");
    let mismatched = parsed.lower(&other_schema).expect("still lowers");
    assert!(
        !Validator::new().validate(&mismatched).validation_passed(),
        "context.input.user should not typecheck against a schema without a `user` field"
    );
}

#[test]
fn decision_kinds_match_the_authorizer_gate() {
    // A consumer reimplementing the decision loop must gate on the decision
    // kinds. `decision_kinds()` / `is_decision_kind()` must report exactly what
    // `Authorizer::is_authorized` gates on: with the default event schema,
    // `request` is a decision kind and `response` is history-only.
    use dogwood_language::{Authorizer, Event, Value};

    let set =
        LoweredPolicySet::from_str(CEDAR_POLICY, &service(), &policy_schema()).expect("lowers");

    let kinds: std::collections::BTreeSet<&str> = set.decision_kinds().collect();
    assert!(
        kinds.contains("request"),
        "request is a decision kind: {kinds:?}"
    );
    assert!(
        !kinds.contains("response"),
        "response is history-only: {kinds:?}"
    );
    assert!(set.is_decision_kind("request"));
    assert!(!set.is_decision_kind("response"));
    assert!(!set.is_decision_kind("nonexistent"));

    // The accessor must agree with the authorizer: a decision-kind event yields
    // Some, a history-only event yields None. This is the invariant a parallel
    // decision loop relies on.
    let mut authorizer = Authorizer::new(set);
    let request = Event::builder("Drupe::Action::Read", "request")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .build();
    let response = Event::builder("Drupe::Action::Read", "response")
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .build();
    assert!(
        authorizer.is_authorized(&request).is_some(),
        "a `request` (decision kind) yields Some"
    );
    assert!(
        authorizer.is_authorized(&response).is_none(),
        "a `response` (history-only) yields None"
    );
}

#[test]
fn distincter_must_be_a_valid_cedar_identifier() {
    // The distincter is interpolated into synthesized policy ids and hoisted
    // `context.<id>` attribute names, so a non-identifier distincter would
    // produce an invalid schema / policy that only fails opaquely downstream.
    // `lower_with_distincter` rejects it up front with `Error::InvalidDistincter`.
    let parsed = ParsedPolicySet::parse(TEMPORAL_POLICY, &service()).expect("parses");

    // Valid identifier fragments lower fine.
    for good in ["storeA", "tenant_42", "_leading_underscore", "policy"] {
        assert!(
            parsed.lower_with_distincter(&policy_schema(), good).is_ok(),
            "valid distincter {good:?} should lower"
        );
    }

    // Non-identifier strings are rejected — space, `::`, quote, dot, dash,
    // leading digit, and empty.
    for bad in [
        "has space",
        "has::colons",
        "has\"quote",
        "has.dot",
        "has-dash",
        "1leading_digit",
        "",
    ] {
        match parsed.lower_with_distincter(&policy_schema(), bad) {
            Err(Error::InvalidDistincter(d)) => assert_eq!(d, bad),
            Err(e) => panic!("distincter {bad:?}: wrong error variant: {e}"),
            Ok(_) => panic!("distincter {bad:?} should be rejected as invalid, but lowered"),
        }
    }
}

#[test]
fn augmented_schema_feeds_forward_into_a_later_lowering() {
    // The feed-forward workflow the incremental design targets: lower one
    // temporal policy, take its AUGMENTED schema back out as cedarschema text,
    // and lower a *second* temporal policy against that augmented schema. Both
    // policies' hoisted `context.<id>` fields must survive and typecheck — i.e.
    // the second augmentation accretes onto the first rather than dropping it.
    //
    // This is only possible because `cedar_schema_str()` exposes the augmented
    // schema in a form `PolicySchema::from_cedarschema_str` can re-ingest.

    // Pass 1: lower policy A under distincter "a".
    let a = ParsedPolicySet::parse(TEMPORAL_POLICY, &service())
        .expect("A parses")
        .lower_with_distincter(&policy_schema(), "a")
        .expect("A lowers");
    let a_field = a
        .temporal_fields()
        .next()
        .expect("A hoisted one temporal field")
        .id
        .clone();
    assert!(
        a_field.starts_with("a_0"),
        "A's field namespaced by its distincter: {a_field}"
    );

    // Take A's augmented schema back out as text and re-ingest it as the base
    // action schema for the next lowering. (Before `cedar_schema_str`, there was
    // no public way to do this — the HIGH review finding.)
    let augmented_text = a
        .cedar_schema_str()
        .expect("A's augmented schema serializes");
    assert!(
        augmented_text.contains(&a_field),
        "A's augmented schema text declares A's hoisted field `{a_field}`"
    );
    let carried_schema =
        PolicySchema::from_cedarschema_str(&augmented_text).expect("augmented schema re-ingests");

    // Pass 2: lower policy B against A's augmented schema, under a DISTINCT
    // distincter "b" (so B's hoisted field cannot collide with A's carried one).
    let b = ParsedPolicySet::parse(TEMPORAL_POLICY, &service())
        .expect("B parses")
        .lower_with_distincter(&carried_schema, "b")
        .expect("B lowers against A's augmented schema");
    let b_field = b
        .temporal_fields()
        .next()
        .expect("B hoisted one temporal field")
        .id
        .clone();
    assert!(
        b_field.starts_with("b_0"),
        "B's field namespaced by its distincter: {b_field}"
    );
    assert_ne!(
        a_field, b_field,
        "the two lowerings' hoisted fields are distinct"
    );

    // The payoff: B's augmented schema must declare BOTH fields (A's carried
    // forward + B's freshly added) — proving augmentation accreted, not clobbered.
    let b_augmented = b
        .cedar_schema_str()
        .expect("B's augmented schema serializes");
    assert!(
        b_augmented.contains(&a_field),
        "B's augmented schema must still carry A's field `{a_field}` (accretion, not overwrite)"
    );
    assert!(
        b_augmented.contains(&b_field),
        "B's augmented schema must add B's field `{b_field}`"
    );

    // And B still validates against its (doubly-augmented) schema.
    assert!(
        Validator::new().validate(&b).validation_passed(),
        "B validates against the fed-forward augmented schema"
    );
}

/// A schema shaped like the real MCP → Cedar generator output: a broker-style
/// tool namespace (deliberately generic, to prove the behavior is not
/// tied to any particular name) with an entity hierarchy, an action group, and — the
/// load-bearing detail — actions whose `context` is a **common-type
/// reference** (`context: QuoteCtx`) rather than an inline record, where the
/// referenced record nests `input` / `output` / `system` sub-records built
/// from every builtin the generator emits: primitives (`String`, `Long`,
/// `Bool`) and extension types (`decimal`, `datetime`).
///
/// This shape matters because augmentation only pins builtins to Cedar's
/// reserved `__cedar::` spelling when it has to **inline a context
/// reference** (an inline context leaves the prefix only on the flat hoisted
/// field, which the event-schema deriver never descends into). A reference
/// context forces Cedar's type resolver to run, which fully-qualifies every
/// builtin *inside* the `input`/`output` records — the positions the deriver
/// walks — so the reserved spelling reaches the code path that once rejected
/// it.
const BROKER_REF_CONTEXT_SCHEMA: &str = r#"
namespace Brokerage {
  type QuoteInput  = { symbol: String, qty: Long };
  type QuoteOutput = { price: decimal, filled: Bool };
  type SystemContext = { now: datetime };
  type QuoteCtx = { input: QuoteInput, output?: QuoteOutput, system: SystemContext };

  entity Gateway;
  entity Desk;
  entity Trader in [Desk] = { id: String } tags String;

  action "Trade";
  action "GetQuote" in [Action::"Trade"] appliesTo {
    principal: [Trader],
    resource: [Gateway],
    context: QuoteCtx
  };
}
"#;

/// End-to-end regression for the `__cedar` reserved-namespace bug, exercised
/// through the **repeated** feed-forward loop a downstream consumer runs when
/// it augments a schema, feeds the result back in, and augments again.
///
/// Each pass:
///   1. lowers a temporal policy (which hoists a `context.<id>` field, forcing
///      the reference context `QuoteCtx` to be inlined + type-resolved, which
///      pins the nested builtins to `__cedar::String` / `__cedar::Long` /
///      `__cedar::decimal` / `__cedar::datetime`);
///   2. serializes the augmented schema back to `.cedarschema` text;
///   3. feeds that text in as the next pass's action schema.
///
/// Before the fix, pass 2's event-schema derivation split `__cedar::String`
/// into namespace `__cedar` + basename `String`, and Cedar's namespace parser
/// rejected the reserved name — the exact customer error. This asserts the
/// loop survives several iterations, that the `__cedar::` spelling really is
/// present inside an `input`/`output` sub-record (so the test cannot silently
/// stop exercising the bug), and that every pass still validates.
#[test]
fn repeated_feed_forward_over_reserved_builtin_context_survives() {
    let svc = ServiceSchema::defaults();
    // A temporal policy over the reference-context action: the `formerly
    // within` clause hoists one field, so lowering must inline `QuoteCtx`.
    let policy = r#"
        permit ( principal, action == Brokerage::Action::"GetQuote", resource )
        when temporal {
            formerly within 1h Brokerage::Action::"GetQuote"::request{
                input.symbol: context.input.symbol
            }
        };
    "#;

    let mut current = BROKER_REF_CONTEXT_SCHEMA.to_string();
    let mut saw_nested_reserved_builtin = false;

    // Iterate the augment → serialize → re-ingest loop several times. A single
    // pass would not catch a regression that only bites on RE-derivation of an
    // already-augmented schema, which is exactly this bug.
    for pass in 0..3 {
        let schema = PolicySchema::from_cedarschema_str(&current)
            .unwrap_or_else(|e| panic!("pass {pass}: augmented schema re-ingests: {e:?}"));

        // Give each pass a distinct distincter so the carried-forward and
        // freshly-hoisted field names cannot collide across iterations.
        let distincter = format!("p{pass}");
        let lowered = ParsedPolicySet::parse(policy, &svc)
            .unwrap_or_else(|e| panic!("pass {pass}: policy parses: {e:?}"))
            .lower_with_distincter(&schema, &distincter)
            .unwrap_or_else(|e| panic!("pass {pass}: lowers against fed-forward schema: {e:?}"));

        assert!(
            Validator::new().validate(&lowered).validation_passed(),
            "pass {pass}: policy validates against the fed-forward augmented schema"
        );

        let augmented = lowered
            .cedar_schema_str()
            .unwrap_or_else(|e| panic!("pass {pass}: augmented schema serializes: {e:?}"));

        // Guard against the test silently ceasing to exercise the bug. The
        // flat hoisted field is always `__cedar::Bool`, and the deriver never
        // descends into it — so its presence alone would NOT reproduce the
        // bug. These four builtins, by contrast, come only from the inlined
        // `input`/`output`/`system` sub-records the deriver *does* walk, so
        // seeing any of them proves the reserved spelling reached the failing
        // code path (and is deliberately distinct from the `__cedar::Bool`
        // hoisted field, which does not).
        if augmented.contains("__cedar::String")
            || augmented.contains("__cedar::Long")
            || augmented.contains("__cedar::decimal")
            || augmented.contains("__cedar::datetime")
        {
            saw_nested_reserved_builtin = true;
        }

        current = augmented;
    }

    assert!(
        saw_nested_reserved_builtin,
        "the augmented schema never carried a nested `__cedar::`-qualified \
         builtin — the test is no longer exercising the reserved-namespace bug; \
         augmented schema was:\n{current}"
    );
}
