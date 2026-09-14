//! End-to-end tests for `LoweredPolicySet::leaf_map`, including action-group
//! expansion through the augmented schema.

use std::collections::BTreeSet;

use dogwood_language::{ActionScope, Event, LoweredPolicySet, PolicySchema, ServiceSchema};

const SCHEMA: &str = r#"
namespace Drupe {
  type Input = { user: String };
  entity Gateway;
  entity OAuthUser;
  action "Admin";
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input }
  };
  action "Logout" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input }
  };
  action "Purge" in [Action::"Admin"] appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: Input }
  };
}
"#;

const POLICY: &str = r#"
permit (principal, action == Drupe::Action::"Login", resource)
when temporal { formerly within 1h Drupe::Action::"Login"::request{} };

permit (principal, action in [Drupe::Action::"Admin"], resource)
when temporal { formerly within 1h Drupe::Action::"Login"::request{} };
"#;

fn lower() -> LoweredPolicySet {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("the fixture schema builds");
    LoweredPolicySet::from_str(POLICY, &ServiceSchema::defaults(), &schema).expect("lowers")
}

fn event(action: &str) -> Event {
    Event::builder_for(&["Drupe", "Action"], action, "request").build()
}

fn leaf_id(lowered: &LoweredPolicySet, pick: impl Fn(&ActionScope) -> bool) -> String {
    lowered
        .temporal_fields()
        .find(|f| pick(&f.action))
        .expect("the fixture has a leaf under that scope")
        .id
        .clone()
}

fn needed(lowered: &LoweredPolicySet, action: &str) -> Option<BTreeSet<String>> {
    lowered
        .leaf_map()
        .needed_for(&event(action))
        .map(|set| (*set).clone())
}

#[test]
fn each_action_reads_exactly_the_leaves_of_the_rules_it_can_match() {
    let lowered = lower();
    let login_leaf = leaf_id(
        &lowered,
        |s| matches!(s, ActionScope::Concrete(a) if a.id == "Login"),
    );
    let admin_leaf = leaf_id(&lowered, |s| matches!(s, ActionScope::List(_)));
    assert_ne!(login_leaf, admin_leaf, "two rules, two distinct leaves");

    assert_eq!(
        needed(&lowered, "Login"),
        Some(BTreeSet::from([login_leaf])),
        "a `==`-scoped rule's leaf, and only it, is read by its own action"
    );
    assert_eq!(
        needed(&lowered, "Purge"),
        Some(BTreeSet::from([admin_leaf])),
        "the group scope is expanded through the schema to its member `Purge` — \
         Cedar applies a group-scoped rule to the group's MEMBERS"
    );
    assert_eq!(
        needed(&lowered, "Logout"),
        Some(BTreeSet::new()),
        "an action no rule is scoped to reads nothing: present (so it slices) \
         and empty (so it computes no verdict at all)"
    );
    assert!(
        lowered.leaf_map().unresolved().is_empty(),
        "every scope in the fixture resolves, so nothing is computed unconditionally"
    );
}

#[test]
fn an_action_the_map_cannot_answer_for_falls_back() {
    let lowered = lower();
    assert_eq!(needed(&lowered, "Undeclared"), None);
    assert_eq!(needed(&lowered, "Admin"), None, "a pure action group");
    assert_eq!(
        lowered.leaf_map().entry_count(),
        3,
        "Login, Logout and Purge — every action that can receive a request, \
         and not the `Admin` group"
    );
}
