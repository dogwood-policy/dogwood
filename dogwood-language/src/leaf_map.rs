//! Precomputed answers to which temporal leaves a decision can read.
//!
//! A backend builds a [`DecisionLeafMap`] during
//! [`TemporalEngine::prepare`](crate::TemporalEngine::prepare) and calls
//! [`DecisionLeafMap::needed_for`] for each decision. The contract is:
//!
//! - `Some(ids)` identifies every leaf that decision can read. Other installed
//!   leaves may be bound `false` without changing the decision.
//! - `None` means the map has no answer, so the backend must compute every leaf.
//!   An empty set, not `None`, means no leaves are needed.
//! - Every installed leaf must still be bound; an absent `context.<id>` is a
//!   Cedar evaluation error.
//! - Callers must not depend on the current slicing granularity; future versions
//!   may return smaller sets for the same event.
//!
//! The current implementation indexes leaves by request action. It consumes the
//! same `TemporalField::target_actions` expansion that schema augmentation uses
//! to declare each hoisted context field. Unknown or unresolvable scopes are
//! widened to every action, while lookup misses fall back through `None`.
//! Principal and resource constraints are intentionally ignored.
//! Under-expansion also omits the corresponding schema attribute and therefore
//! fails during Cedar evaluation; over-expansion only computes extra leaves.
//!
//! Action keys are Cedar [`EntityUid`]s. Event actions and expanded scope
//! actions both use the request path's UID renderer, avoiding a second identity
//! derivation for escaped or separator-containing action ids.
//!
//! This assumes one [`TemporalField`] per hoist site per policy. If leaves are
//! deduplicated across policies, `target_actions` must become the union of the
//! scopes of every referencing policy.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use cedar_policy::{EntityUid, Schema};
use std::str::FromStr;

use crate::api::{ActionRef, ActionScope, ExtensionId, TemporalField};
use crate::interpreter::value::Event;

/// Derive the lookup key through the same renderer used to build Cedar requests.
fn event_action_uid(event: &Event) -> Option<EntityUid> {
    EntityUid::from_str(&crate::api::qualified_action_uid(
        event.namespace(),
        event.action(),
    ))
    .ok()
}

/// Derive a scope target's key through the request renderer.
fn target_action_uid(action: &ActionRef) -> Option<EntityUid> {
    EntityUid::from_str(&crate::api::action_ref_uid(action)).ok()
}

/// Precomputed temporal leaves needed by a decision.
///
/// [`Default`] has no answers, so every lookup returns `None`.
#[derive(Debug, Default)]
pub struct DecisionLeafMap {
    // Arc lets an engine retain the answer while mutably evaluating itself.
    by_action: HashMap<EntityUid, Arc<BTreeSet<ExtensionId>>>,
    // Folded into every entry after construction.
    always: BTreeSet<ExtensionId>,
    unresolved: Vec<(ExtensionId, &'static str)>,
}

impl DecisionLeafMap {
    /// Build a map from the inputs supplied to [`TemporalEngine::prepare`].
    ///
    /// Relativized and non-relativized leaves produce the same map because
    /// relativization does not change leaf ids or action scopes.
    pub fn build(leaves: &[TemporalField], schema: &Schema) -> Self {
        let mut map = Self::seeded(schema);
        for leaf in leaves {
            map.add_leaf(&leaf.id, &leaf.action, &leaf.target_actions);
        }
        map.fold_always();
        map
    }

    /// Return the leaves `event` can read.
    ///
    /// `None` means the map has no answer and the caller must compute every
    /// leaf. The caller must bind every installed leaf, using `false` for those
    /// omitted from a returned set.
    pub fn needed_for(&self, event: &Event) -> Option<Arc<BTreeSet<ExtensionId>>> {
        self.by_action.get(&event_action_uid(event)?).cloned()
    }

    /// Return the number of decisions the map can answer without falling back.
    pub fn entry_count(&self) -> usize {
        self.by_action.len()
    }

    /// Return leaves widened to every decision and the reason for each widening.
    pub fn unresolved(&self) -> &[(ExtensionId, &'static str)] {
        &self.unresolved
    }

    /// Seed requestable actions. Groups are excluded so a group used as a
    /// request action falls back rather than reusing its members' expansion.
    fn seeded(schema: &Schema) -> Self {
        let groups: HashSet<&EntityUid> = schema.action_groups().collect();
        let by_action = schema
            .actions()
            .filter(|uid| !groups.contains(uid))
            .map(|uid| (uid.clone(), Arc::<BTreeSet<ExtensionId>>::default()))
            .collect();
        Self {
            by_action,
            always: BTreeSet::new(),
            unresolved: Vec::new(),
        }
    }

    /// Record a leaf under its resolved actions, widening on resolution failure.
    fn add_leaf(&mut self, id: &str, scope: &ActionScope, targets: &[ActionRef]) {
        match Self::expansion(scope, targets) {
            Ok(targets) => {
                for uid in targets {
                    let entry = self.by_action.entry(uid).or_default();
                    Arc::make_mut(entry).insert(id.to_string());
                }
            }
            Err(why) => {
                self.always.insert(id.to_string());
                self.unresolved.push((id.to_string(), why));
            }
        }
    }

    /// Resolve all action keys or fail the entire leaf toward widening.
    ///
    /// Unconstrained scopes cannot trust a finite target expansion. Likewise,
    /// accepting only the parseable subset of targets would silently omit the
    /// leaf from other actions.
    fn expansion(
        scope: &ActionScope,
        targets: &[ActionRef],
    ) -> Result<Vec<EntityUid>, &'static str> {
        if matches!(scope, ActionScope::Unconstrained) {
            return Err("bare `action` scope: the rule applies to every action");
        }
        if targets.is_empty() {
            return Err("the action scope resolved to no concrete action");
        }
        targets
            .iter()
            .map(target_action_uid)
            .collect::<Option<Vec<_>>>()
            .ok_or("an action in the scope has no uid Cedar can parse")
    }

    /// Fold widened leaves into every entry so lookup remains a single probe.
    fn fold_always(&mut self) {
        // Destructured rather than `self.by_action.values_mut()`, which would
        // hold `self` mutably while `self.always` is read.
        let Self {
            by_action, always, ..
        } = self;
        if always.is_empty() {
            return;
        }
        for set in by_action.values_mut() {
            Arc::make_mut(set).extend(always.iter().cloned());
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;

    const SCHEMA: &str = r#"
namespace Test {
  entity User;
  entity Doc;
  action "Admin";
  action "Read" appliesTo { principal: [User], resource: [Doc] };
  action "Delete" in [Action::"Admin"] appliesTo { principal: [User], resource: [Doc] };
}
"#;

    fn schema() -> Schema {
        Schema::from_str(SCHEMA).expect("the fixture schema builds")
    }

    // Keep expected keys independent from the renderer under test.
    fn key(uid: &str) -> EntityUid {
        EntityUid::from_str(uid).expect("the fixture uid literal parses")
    }

    fn test_key(id: &str) -> EntityUid {
        key(&format!(r#"Test::Action::"{id}""#))
    }

    fn action_ref(namespace: Option<&str>, id: &str) -> ActionRef {
        ActionRef {
            namespace: namespace.map(str::to_string),
            id: id.to_string(),
        }
    }

    fn request_action_uid(path: &[&str], id: &str) -> EntityUid {
        let path: Vec<String> = path.iter().map(|s| s.to_string()).collect();
        EntityUid::from_str(&crate::api::qualified_action_uid(&path, id))
            .expect("the request's rendering parses")
    }

    fn event(path: &[&str], id: &str) -> Event {
        Event::builder_for(path, id, "request").build()
    }

    #[test]
    fn the_event_derived_uid_is_the_request_derived_uid() {
        let cases: [(&[&str], &str, &str); 6] = [
            (&["Test", "Action"], "Read", r#"Test::Action::"Read""#),
            (
                &["Test", "Action"],
                "Read::Archive",
                r#"Test::Action::"Read::Archive""#,
            ),
            (
                &["Test", "Action"],
                r#"say "hi""#,
                r#"Test::Action::"say \"hi\"""#,
            ),
            (&["Action"], "Read", r#"Action::"Read""#),
            (&[], "Read", r#"Action::"Read""#),
            (
                &["A", "B", "Action"],
                "Read::Archive",
                r#"A::B::Action::"Read::Archive""#,
            ),
        ];
        for (path, id, literal) in cases {
            assert_eq!(
                event_action_uid(&event(path, id)),
                Some(request_action_uid(path, id)),
                "event {path:?}::{id:?} and its request uid must key identically"
            );
            assert_eq!(
                event_action_uid(&event(path, id)),
                Some(key(literal)),
                "event {path:?}::{id:?} must key as {literal}"
            );
        }
    }

    #[test]
    fn distinct_actions_key_distinctly() {
        let keys = [
            event_action_uid(&event(&["Test", "Action"], "Read")),
            event_action_uid(&event(&["Test", "Action"], "Read::Archive")),
            event_action_uid(&event(&["Other", "Action"], "Read")),
            event_action_uid(&event(&[], "Read")),
        ];
        for (i, a) in keys.iter().enumerate() {
            for b in &keys[i + 1..] {
                assert_ne!(a, b, "distinct actions must not collide");
            }
        }
    }

    #[test]
    fn an_unnamespaced_action_keys_identically_from_every_source() {
        let want = key(r#"Action::"Read""#);
        assert_eq!(event_action_uid(&event(&[], "Read")).unwrap(), want);
        assert_eq!(event_action_uid(&event(&["Action"], "Read")).unwrap(), want);
        assert_eq!(target_action_uid(&action_ref(None, "Read")).unwrap(), want);
        assert_eq!(request_action_uid(&[], "Read"), want);
    }

    #[test]
    fn a_scope_target_keys_as_the_schema_declares_it_even_for_awkward_ids() {
        const AWKWARD: &str = r#"
namespace Test {
  entity User;
  entity Doc;
  action "Read::Archive" appliesTo { principal: [User], resource: [Doc] };
  action "say \"hi\"" appliesTo { principal: [User], resource: [Doc] };
}
"#;
        let seeded =
            DecisionLeafMap::seeded(&Schema::from_str(AWKWARD).expect("the schema builds"));
        for id in ["Read::Archive", r#"say "hi""#] {
            let uid = target_action_uid(&action_ref(Some("Test"), id))
                .unwrap_or_else(|| panic!("the scope target {id:?} renders a parseable uid"));
            assert!(
                seeded.by_action.contains_key(&uid),
                "the key derived for scope target {id:?} must be the one the schema declares"
            );
        }
    }

    #[test]
    fn a_scope_target_with_no_parseable_uid_is_needed_by_every_action() {
        // A namespace that is not a legal Cedar name: the rendered type path
        // `1Bad::Action` cannot parse, so no uid exists to key under.
        let target = action_ref(Some("1Bad"), "Read");
        assert!(
            target_action_uid(&target).is_none(),
            "the fixture must really be unparseable, or this proves nothing"
        );

        let mut map = DecisionLeafMap::seeded(&schema());
        map.add_leaf(
            "leaf_unparseable",
            &ActionScope::Concrete(target.clone()),
            &[target],
        );
        map.fold_always();

        for id in ["Read", "Delete"] {
            assert!(
                map.by_action[&test_key(id)].contains("leaf_unparseable"),
                "a leaf whose scope target has no uid must be computed for {id} too"
            );
        }
        assert_eq!(
            map.unresolved(),
            [(
                "leaf_unparseable".to_string(),
                "an action in the scope has no uid Cedar can parse"
            )],
            "and it is reported rather than silently dropped"
        );
    }

    #[test]
    fn seeding_covers_every_declared_action_except_the_groups() {
        let map = DecisionLeafMap::seeded(&schema());
        assert!(map.by_action.contains_key(&test_key("Read")));
        assert!(map.by_action.contains_key(&test_key("Delete")));
        assert!(
            !map.by_action.contains_key(&test_key("Admin")),
            "an action group must not be keyed: its expansions name its members, \
             so an entry for it would under-report"
        );
        assert_eq!(map.entry_count(), 2, "Read and Delete, not Admin");
        assert!(
            map.by_action.values().all(|set| set.is_empty()),
            "a seeded action needs no leaf until a rule scopes to one"
        );
    }

    #[test]
    fn a_resolved_scope_keys_its_leaf_under_exactly_its_actions() {
        let mut map = DecisionLeafMap::seeded(&schema());
        map.add_leaf(
            "leaf_read",
            &ActionScope::Concrete(action_ref(Some("Test"), "Read")),
            &[action_ref(Some("Test"), "Read")],
        );
        map.fold_always();

        assert_eq!(
            *map.by_action[&test_key("Read")],
            BTreeSet::from(["leaf_read".to_string()])
        );
        assert!(
            map.by_action[&test_key("Delete")].is_empty(),
            "a Delete decision reads no leaf, so it computes none"
        );
        assert!(map.unresolved().is_empty());
    }

    #[test]
    fn every_element_of_a_list_scope_keys_the_leaf() {
        let targets = [
            action_ref(Some("Test"), "Read"),
            action_ref(Some("Test"), "Delete"),
        ];
        let mut map = DecisionLeafMap::seeded(&schema());
        map.add_leaf("leaf_both", &ActionScope::List(targets.to_vec()), &targets);
        map.fold_always();

        for id in ["Read", "Delete"] {
            assert!(
                map.by_action[&test_key(id)].contains("leaf_both"),
                "{id} is in the list scope"
            );
        }
    }

    #[test]
    fn an_unconstrained_scope_is_needed_by_every_action() {
        let mut map = DecisionLeafMap::seeded(&schema());
        // Deliberately given the expansion of a *different*, narrower scope:
        // `Unconstrained` must not be keyed from `target_actions` at all.
        map.add_leaf(
            "leaf_any",
            &ActionScope::Unconstrained,
            &[action_ref(Some("Test"), "Read")],
        );
        map.fold_always();

        for id in ["Read", "Delete"] {
            assert!(
                map.by_action[&test_key(id)].contains("leaf_any"),
                "a bare `action` scope applies to {id} too"
            );
        }
        assert_eq!(
            map.unresolved(),
            [(
                "leaf_any".to_string(),
                "bare `action` scope: the rule applies to every action"
            )],
            "and it is reported, so a policy set that defeats slicing says why"
        );
    }

    #[test]
    fn a_scope_that_resolves_to_nothing_is_needed_by_every_action() {
        let mut map = DecisionLeafMap::seeded(&schema());
        map.add_leaf("leaf_unknown", &ActionScope::List(Vec::new()), &[]);
        map.fold_always();

        for id in ["Read", "Delete"] {
            assert!(map.by_action[&test_key(id)].contains("leaf_unknown"));
        }
        assert_eq!(
            map.unresolved(),
            [(
                "leaf_unknown".to_string(),
                "the action scope resolved to no concrete action"
            )]
        );
    }

    #[test]
    fn an_action_the_map_cannot_answer_for_yields_no_leaf_set() {
        let map = DecisionLeafMap::build(&[], &schema());
        assert!(
            map.needed_for(&event(&["Test", "Action"], "Undeclared"))
                .is_none(),
            "an action the schema does not declare must fall back"
        );
        assert!(
            map.needed_for(&event(&["Test", "Action"], "Admin"))
                .is_none(),
            "an action group arriving as a request action must fall back"
        );
        assert!(
            map.needed_for(&event(&["Test", "Action"], "Read"))
                .is_some(),
            "a declared action must NOT fall back — otherwise nothing is sliced"
        );
        assert!(
            DecisionLeafMap::default()
                .needed_for(&event(&["Test", "Action"], "Read"))
                .is_none(),
            "a map that was never built slices nothing"
        );
    }

    #[test]
    fn an_undeclared_target_action_gets_its_own_complete_entry() {
        let mut map = DecisionLeafMap::seeded(&schema());
        map.add_leaf(
            "leaf_ghost",
            &ActionScope::Concrete(action_ref(Some("Test"), "Ghost")),
            &[action_ref(Some("Test"), "Ghost")],
        );
        map.add_leaf("leaf_any", &ActionScope::Unconstrained, &[]);
        map.fold_always();

        let ghost = &map.by_action[&test_key("Ghost")];
        assert!(ghost.contains("leaf_ghost"));
        assert!(
            ghost.contains("leaf_any"),
            "the unresolvable leaves are folded into every entry, this one included"
        );
    }
}
