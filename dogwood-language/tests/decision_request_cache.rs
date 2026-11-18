//! `DecisionRequestCache`: `decision_request` for many decisions against one schema, with what
//! depends on the schema alone computed once and parsed entity uids kept.
//!
//! The DSQL engine's leaf masker builds the request and entity store of every decision with the
//! crate's `decision_request` (so that it cannot drift from what the authorizer decides with). At
//! P = 100,000 that construction was three quarters of the masker's cost: each call parsed three
//! uids with Cedar's parser and rebuilt the schema's action entities. The cache must build exactly
//! what `decision_request` builds, for every event, the second time as the first.

use dogwood_language::{
    DecisionRequestCache, Event, LoweredPolicySet, PolicySchema, ServiceSchema, parse_trace,
};

const SCHEMA: &str = r#"
namespace Svc {
  entity Tenant;
  entity Group in [Tenant];
  entity User in [Group] = { dept?: String, level?: Long };
  entity Gateway = { zone?: String };
  type In = { doc: String, tag?: String };
  action "Read" appliesTo { principal: [User], resource: [Gateway], context: { input: In, system?: { hour: Long } } };
  action "Write" in ["Read"] appliesTo { principal: [User], resource: [Gateway], context: { input: In } };
}
"#;

const POLICY: &str = r#"
permit (principal, action in Svc::Action::"Read", resource)
when { principal.dept == "eng" }
when temporal { formerly within 1h Svc::Action::"Read"::request{} };
"#;

/// Events with and without supplied entities (attributes, parents), a `null`, repeated uids,
/// and the two actions.
const TRACE: &str = r#"@1 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::User::"alice": { dept: "eng" } in [Svc::Group::"g1"], Svc::Group::"g1": {} in [Svc::Tenant::"t1"]) request_context(input: { doc: "d1", tag: null }) Svc::Action::"Read"::request(input: { doc: "d1" })
@2 scope(principal: Svc::User::"bob", resource: Svc::Gateway::"gw2") request_context(input: { doc: "d2" }, system: { hour: 3 }) Svc::Action::"Read"::request(input: { doc: "d2" })
@3 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") request_context(input: { doc: "d3" }) Svc::Action::"Write"::request(input: { doc: "d3" })
@4 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw2") entities(Svc::Gateway::"gw2": { zone: "z" }) request_context(input: { doc: "d4" }) Svc::Action::"Read"::request(input: { doc: "d4" })
@5 scope(principal: Svc::User::"bob", resource: Svc::Gateway::"gw2") request_context(input: { doc: "d2" }, system: { hour: 3 }) Svc::Action::"Read"::request(input: { doc: "d2" })
"#;

fn lower() -> LoweredPolicySet {
    LoweredPolicySet::from_str(
        POLICY,
        &ServiceSchema::defaults(),
        &PolicySchema::from_cedarschema_str(SCHEMA).unwrap(),
    )
    .unwrap()
}

/// The two constructions agree: the same request (principal, action, resource and context) and
/// the same entity store, or the same error.
fn agree(cache: &DecisionRequestCache, set: &LoweredPolicySet, event: &Event) {
    let want = dogwood_language::decision_request(event, set.cedar_schema());
    let got = cache.decision_request(event);
    match (&want, &got) {
        (Ok((r1, e1)), Ok((r2, e2))) => {
            assert_eq!(format!("{r1:?}"), format!("{r2:?}"), "the request");
            // `deep_eq`: `==` on stores compares their entities' uids only.
            assert!(e1.deep_eq(e2), "the entity store: {e1:?} vs {e2:?}");
        }
        (Err(a), Err(b)) => assert_eq!(a, b, "the error"),
        _ => panic!(
            "one built, the other did not: {:?} vs {:?}",
            want.as_ref().err(),
            got.as_ref().err()
        ),
    }
}

#[test]
fn the_cache_builds_what_decision_request_builds() {
    let set = lower();
    let cache = DecisionRequestCache::new(set.cedar_schema()).expect("the cache builds");
    let events = parse_trace(TRACE).unwrap();
    // Twice: the second pass reads every uid from the cache.
    for _ in 0..2 {
        for e in &events {
            agree(&cache, &set, e);
        }
    }
    // The store holds the action hierarchy and the supplied parents.
    let (_, store) = cache.decision_request(&events[2]).unwrap();
    assert!(
        format!("{store:?}").contains("Write"),
        "the action entities are in the store"
    );
}

/// The errors are `decision_request`'s, and a failed parse is not cached as a success.
#[test]
fn the_cache_fails_where_decision_request_fails() {
    let set = lower();
    let cache = DecisionRequestCache::new(set.cedar_schema()).expect("the cache builds");
    let no_principal = Event::builder("Svc::Action::Read", "request")
        .resource("Svc::Gateway::\"gw1\"")
        .build();
    let malformed = Event::builder("Svc::Action::Read", "request")
        .principal("Svc::User::\"al\"ice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .build();
    for _ in 0..2 {
        agree(&cache, &set, &no_principal);
        agree(&cache, &set, &malformed);
    }
    assert!(cache.decision_request(&no_principal).is_err());
}

/// Past its capacity the uid cache starts over, and still answers the same.
#[test]
fn the_cache_answers_the_same_past_its_capacity() {
    let set = lower();
    let cache = DecisionRequestCache::new(set.cedar_schema()).expect("the cache builds");
    for i in 0..70_000 {
        let e = Event::builder("Svc::Action::Read", "request")
            .principal(&format!("Svc::User::\"u{i}\""))
            .resource("Svc::Gateway::\"gw1\"")
            .build();
        if i % 7_001 == 0 || i >= 69_990 {
            agree(&cache, &set, &e);
        } else {
            assert!(
                cache.decision_request(&e).is_ok()
                    || dogwood_language::decision_request(&e, set.cedar_schema()).is_err()
            );
        }
    }
}
