//! Multi-action cases composed from the mostly single-action corpus.
//!
//! # The composition argument
//!
//! Each constituent is moved under a disjoint `G<i>` namespace, then traces and
//! committed verdict streams are concatenated with matching timestamp and
//! time-point offsets. Disjoint names prevent one constituent's events or rules
//! from matching another's, and concatenation preserves earlier decisions
//! because temporal operators only inspect the past.
//!
//! Bare-action cases use a gap beyond `max_window`, making foreign leaves false.
//! Tightly spaced cases use only action-scoped rules and deliberately keep some
//! foreign leaves true, so an unsound exclusion can change a verdict. Every
//! synthesized case is checked by the same `support::check_case` path as a
//! committed case.

#[path = "support/slicing.rs"]
mod support;

use std::collections::{BTreeMap, BTreeSet};

use dogwood_language::{DecisionLeafMap, Event, parse_trace};
use support::{Case, Totals, check_all, check_case, corpus};

// ── the combinator ──────────────────────────────────────────────────────

/// Beyond the 24-hour `max_window` cap.
const GAP_WIDE: i64 = 1_000_000;

/// Close enough for a foreign `formerly within 1h` to match.
const GAP_TIGHT: i64 = 5;

struct Part<'a> {
    case: &'a Case,
    trace: usize,
}

fn part<'a>(cases: &'a [Case], name: &str) -> Part<'a> {
    let case = cases
        .iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("corpus case {name} not found"));
    assert!(
        gluable(case),
        "corpus case {name} is no longer gluable — see `gluable`"
    );
    Part { case, trace: 0 }
}

fn declared_namespaces(schema: &str) -> Vec<String> {
    schema
        .lines()
        .filter_map(|l| l.trim().strip_prefix("namespace "))
        .map(|rest| rest.trim().trim_end_matches('{').trim().to_string())
        .filter(|n| !n.is_empty())
        .collect()
}

/// Requalify exact `<namespace>::` references with a disjoint prefix.
fn qualify(text: &str, namespaces: &[String], prefix: &str) -> String {
    let mut out = text.to_string();
    for ns in namespaces {
        out = out.replace(&format!("{ns}::"), &format!("{prefix}::{ns}::"));
    }
    out
}

fn requalify_schema(schema: &str, prefix: &str, namespaces: &[String]) -> String {
    qualify(schema, namespaces, prefix)
        .lines()
        .map(|line| match line.trim_start().strip_prefix("namespace ") {
            Some(rest) => format!("namespace {prefix}::{rest}"),
            None => line.to_string(),
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Shift every `@<ts>` in a trace by `by`.
fn offset_trace(trace: &str, by: i64) -> String {
    trace
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|line| {
            let (at, rest) = line
                .split_once(' ')
                .unwrap_or_else(|| panic!("trace line without a timestamp: {line}"));
            let ts: i64 = at
                .trim_start_matches('@')
                .parse()
                .unwrap_or_else(|_| panic!("non-integer timestamp: {at}"));
            format!("@{} {rest}", ts + by)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Shift a verdict stream the same way: timestamps by `by`, time-point indices by
/// the number of events that now precede the constituent.
fn offset_expected(expected: &str, by: i64, index_by: usize) -> Vec<String> {
    expected
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|line| {
            let (at, rest) = line
                .split_once(" (time point ")
                .unwrap_or_else(|| panic!("unexpected verdict line: {line}"));
            let (index, verdict) = rest
                .split_once("): ")
                .unwrap_or_else(|| panic!("unexpected verdict line: {line}"));
            let ts: i64 = at.trim().trim_start_matches('@').parse().unwrap();
            let index: usize = index.trim().parse().unwrap();
            format!(
                "@{} (time point {}): {}",
                ts + by,
                index + index_by,
                verdict.trim()
            )
        })
        .collect()
}

/// Can this case be a constituent?
///
/// The glue rewrites namespaces textually, so it needs a case whose declarations
/// all live inside a namespace and whose trace and expected stream are in the
/// ordinary shapes. Provider declarations are excluded: their Rhai and their
/// declared entity types are not requalified, so a glued case would refer to
/// entity types under the wrong prefix. That drops the `mixed` corpus from this
/// file — it is covered unglued by `leaf_map_corpus_differential.rs`.
fn gluable(case: &Case) -> bool {
    if case.providers.is_some() || declared_namespaces(case.schema.as_str()).is_empty() {
        return false;
    }
    // Every declaration inside a namespace: a column-0 line is a namespace
    // header, its closing brace, a comment, or blank.
    let all_namespaced = case.schema.lines().all(|l| {
        let body = l.trim_start();
        body.len() != l.len()
            || body.is_empty()
            || body.starts_with("namespace ")
            || body.starts_with('}')
            || body.starts_with("//")
    });
    let traces_shaped = case.traces.iter().all(|(_, trace, expected)| {
        trace
            .lines()
            .filter(|l| !l.trim().is_empty())
            .all(|l| l.starts_with('@'))
            && expected
                .lines()
                .filter(|l| !l.trim().is_empty())
                .all(|l| l.starts_with('@') && l.contains(" (time point ") && l.contains("): "))
    });
    all_namespaced && traces_shaped
}

/// Glue constituents into one multi-action case: concatenated schemas and
/// policies, one concatenated trace, and the concatenated (shifted) expected
/// verdict stream. See the module docs for why that stream is the right
/// expectation.
fn glue(parts: &[Part], gap: i64) -> Case {
    let event_schema = parts[0].case.event_schema.clone();
    let (mut schema, mut policy) = (String::new(), String::new());
    let (mut trace, mut expected) = (Vec::new(), Vec::new());
    let (mut ts_offset, mut index_offset) = (0i64, 0usize);
    let mut names = Vec::new();

    for (i, p) in parts.iter().enumerate() {
        assert_eq!(
            p.case.event_schema, event_schema,
            "constituents must agree on the event schema: {} vs {}",
            parts[0].case.name, p.case.name
        );
        let prefix = format!("G{i}");
        let namespaces = declared_namespaces(&p.case.schema);
        let (_, src_trace, src_expected) = &p.case.traces[p.trace];
        let events = parse_trace(src_trace).expect("a committed corpus trace parses");

        schema.push_str(&requalify_schema(&p.case.schema, &prefix, &namespaces));
        schema.push('\n');
        policy.push_str(&qualify(&p.case.policy, &namespaces, &prefix));
        policy.push('\n');
        trace.push(offset_trace(
            &qualify(src_trace, &namespaces, &prefix),
            ts_offset,
        ));
        expected.extend(offset_expected(src_expected, ts_offset, index_offset));

        let span = events.iter().map(|e| e.timestamp()).max().unwrap_or(0);
        ts_offset += span + gap;
        index_offset += events.len();
        names.push(p.case.name.clone());
    }

    Case {
        name: format!("glue[{}]", names.join(" + ")),
        policy,
        schema,
        event_schema,
        providers: None,
        traces: vec![("0".to_string(), trace.join("\n"), expected.join("\n"))],
    }
}

/// Rewrite one `action == <uid>` scope into a two-action `action in [...]` list.
/// The corpus has no multi-action list scope to glue, so the shape is made from
/// one: asserting the substitution fired keeps this from silently degrading into
/// a no-op.
fn broaden_to_list(case: &mut Case, from: &str, extra: &str) {
    let needle = format!("action == {from}");
    assert!(
        case.policy.contains(&needle),
        "{}: no `{needle}` scope to broaden",
        case.name
    );
    case.policy = case
        .policy
        .replace(&needle, &format!("action in [{from}, {extra}]"));
}

// ── reading the map directly, for the structural claims ─────────────────

/// Every leaf id of a case, and the map built for it.
fn map_of(case: &Case) -> (BTreeSet<String>, DecisionLeafMap) {
    let lowered = case.lower().expect("a glued case lowers");
    let ids = lowered.temporal_fields().map(|f| f.id.clone()).collect();
    (ids, lowered.leaf_map())
}

/// The events of a glued case's single trace.
fn events_of(case: &Case) -> Vec<Event> {
    parse_trace(&case.traces[0].1).expect("a glued trace parses")
}

/// What the map says must be computed at `event` — every leaf when it declines.
fn needed(map: &DecisionLeafMap, all: &BTreeSet<String>, event: &Event) -> BTreeSet<String> {
    map.needed_for(event)
        .map(|ids| (*ids).clone())
        .unwrap_or_else(|| all.clone())
}

/// Check one glued case and fail with its own report. Returns the counters so a
/// shape can assert what it specifically exercised.
#[track_caller]
fn check(case: &Case) -> Totals {
    let (totals, failures) = check_case(case);
    assert!(
        failures.is_empty(),
        "{}: {} failure(s):\n\n{}",
        case.name,
        failures.len(),
        failures.join("\n\n")
    );
    assert!(
        totals.traces == 1 && totals.decisions > 0,
        "{}: the glued case decided nothing: {totals:?}",
        case.name
    );
    totals
}

// ── the shapes ──────────────────────────────────────────────────────────

/// Cross-action, tightly glued: at every decision of one constituent the other's
/// leaf is skipped, and — because both leaves are context-independent and the
/// constituents are seconds apart — that skipped leaf's honest value is `true`.
/// An unsound skip here changes a verdict; there is nothing for it to hide
/// behind.
#[test]
fn a_tight_cross_action_glue_skips_leaves_that_would_have_been_true() {
    let cases = corpus();
    let glued = glue(
        &[
            // `formerly within 1h Login{ input.user: _, input.server: _ }` on Read:
            // no correlation with the deciding request, so it is true for any
            // action once a Login is in history.
            part(&cases, "0700_all_explicit_wildcards_equals_empty_args"),
            // `formerly within 1h Login{ input.server: "s1" }` on Login: likewise
            // pinned to a literal rather than to the request.
            part(&cases, "0272_literal_constant_in_predicate_field"),
        ],
        GAP_TIGHT,
    );
    let totals = check(&glued);
    assert!(
        totals.suppressed_true_decisions > 0,
        "the tight glue suppressed no `true` leaf, so the verdict comparison had \
         nothing to catch: {totals:?}"
    );
    assert!(
        totals.sliced_leaves < totals.unsliced_leaves,
        "nothing was sliced: {totals:?}"
    );
}

/// Action **groups** and **escaped ids** in one glue: both constituents scope
/// their rules with `action in [<group>]`, and their action ids carry quotes,
/// backslashes, and unicode escapes. Each constituent's own trace already mixes
/// group members with non-members, so a member decision must compute its leaf and
/// a non-member decision must skip it; gluing adds the cross-namespace direction
/// on top.
#[test]
fn a_group_scope_glue_keeps_members_and_skips_everything_else() {
    let cases = corpus();
    let glued = glue(
        &[
            part(&cases, "1214_escaped_action_group_ids_end_to_end"),
            part(&cases, "1213_escaped_enum_ids_end_to_end"),
        ],
        GAP_WIDE,
    );
    let totals = check(&glued);
    assert!(
        totals.sliced_decisions > 0,
        "no group-scoped decision skipped anything: {totals:?}"
    );

    // A group scope must still resolve: none of these leaves may land in
    // `unresolved()`, which is the conservative "needed everywhere" bucket.
    let (_, map) = map_of(&glued);
    assert!(
        map.unresolved().is_empty(),
        "a group scope was not resolved: {:?}",
        map.unresolved()
    );
}

/// A **list scope naming two actions in different constituents**: one leaf, two
/// namespaces. It must be computed at both actions' decisions and skipped at the
/// third constituent's — the shape a map that keyed a leaf by a single action
/// would get wrong.
#[test]
fn a_list_scope_glue_shares_one_leaf_between_two_constituents() {
    let cases = corpus();
    let mut glued = glue(
        &[
            part(&cases, "0004_write_after_read"),
            part(&cases, "0004_write_after_read"),
            part(&cases, "0011_multiple_permits"),
        ],
        GAP_WIDE,
    );
    broaden_to_list(
        &mut glued,
        r#"G0::Drupe::Action::"Write""#,
        r#"G1::Drupe::Action::"Write""#,
    );
    let totals = check(&glued);
    assert!(
        totals.sliced_decisions > 0,
        "nothing was skipped in the list glue: {totals:?}"
    );

    // The broadened rule is the first policy of the first constituent, so its leaf
    // is `policy_0__temporal_0`.
    let shared = "policy_0__temporal_0".to_string();
    let (all, map) = map_of(&glued);
    assert!(all.contains(&shared), "leaf ids changed: {all:?}");
    let mut seen = BTreeSet::new();
    for event in events_of(&glued) {
        let action = format!("{}::{}", event.namespace().join("::"), event.action());
        let holds = needed(&map, &all, &event).contains(&shared);
        seen.insert((action, holds));
    }
    assert!(!seen.is_empty(), "the glued trace held no events");
    for (action, holds) in &seen {
        // The two actions the broadened list names, and nothing else — `G1`'s
        // Write only because the list reaches across the namespace boundary.
        let listed = action == "G0::Drupe::Action::Write" || action == "G1::Drupe::Action::Write";
        assert_eq!(
            *holds, listed,
            "{action}: shared leaf needed = {holds}, expected {listed} (seen: {seen:?})"
        );
    }
}

/// A bare `action` scope glued alongside scoped ones. It is the conservative
/// lane: the leaf must be computed at **every** decision of every constituent,
/// including actions in namespaces its own case never heard of, and the map must
/// say so through `unresolved()`.
#[test]
fn a_bare_action_scope_survives_gluing_and_is_needed_everywhere() {
    let cases = corpus();
    let glued = glue(
        &[
            part(&cases, "0807_two_rules_one_bare_action_one_specific"),
            part(&cases, "0700_all_explicit_wildcards_equals_empty_args"),
        ],
        GAP_WIDE,
    );
    check(&glued);

    let (all, map) = map_of(&glued);
    let bare = "policy_0__temporal_0".to_string();
    assert!(
        map.unresolved().iter().any(|(id, _)| id == &bare),
        "the bare-scope leaf is not in unresolved(): {:?}",
        map.unresolved()
    );
    for event in events_of(&glued) {
        assert!(
            needed(&map, &all, &event).contains(&bare),
            "{}::{}: the bare-scope leaf was not needed",
            event.namespace().join("::"),
            event.action()
        );
    }
}

/// Two rules on the *same* action, glued with a case that has none: the action
/// needs both of its leaves and neither of the stranger's. A map that overwrote
/// an action's entry instead of extending it passes every single-rule case and
/// fails here.
#[test]
fn two_rules_on_one_action_keep_both_leaves_after_gluing() {
    let cases = corpus();
    let glued = glue(
        &[
            part(&cases, "0011_multiple_permits"),
            part(&cases, "0700_all_explicit_wildcards_equals_empty_args"),
        ],
        GAP_WIDE,
    );
    check(&glued);

    let (all, map) = map_of(&glued);
    assert_eq!(all.len(), 3, "expected two leaves then one: {all:?}");
    for event in events_of(&glued) {
        let ns = event.namespace().join("::");
        let expect: BTreeSet<String> = match (ns.as_str(), event.action()) {
            ("G0::Drupe::Action", "Read") => ["policy_0__temporal_0", "policy_1__temporal_0"]
                .iter()
                .map(|s| s.to_string())
                .collect(),
            ("G1::Drupe::Action", "Read") => ["policy_2__temporal_0"]
                .iter()
                .map(|s| s.to_string())
                .collect(),
            _ => BTreeSet::new(),
        };
        assert_eq!(
            needed(&map, &all, &event),
            expect,
            "{ns}::{}: wrong leaf set",
            event.action()
        );
    }
}

/// Escaped and `::`-containing action ids under an `==` scope, glued with an
/// ordinary case. Nothing about slicing may depend on how an id is *spelled*.
#[test]
fn escaped_action_ids_glue_and_still_slice() {
    let cases = corpus();
    let glued = glue(
        &[
            part(&cases, "1200_escaped_action_ids_end_to_end"),
            part(&cases, "0700_all_explicit_wildcards_equals_empty_args"),
        ],
        GAP_WIDE,
    );
    let totals = check(&glued);
    assert!(
        totals.sliced_decisions > 0,
        "the escaped-id glue skipped nothing: {totals:?}"
    );
}

/// One dense glue: eight constituents, so most leaves are out of scope at any
/// decision and the common case is "compute one leaf out of ten".
#[test]
fn a_dense_eight_way_glue_computes_almost_nothing_per_decision() {
    let cases = corpus();
    let names = [
        "0003_self_approval_blocked",
        "0004_write_after_read",
        "0008_no_write_after_logout",
        "0011_multiple_permits",
        "0036_plain_heartbeat",
        "0272_literal_constant_in_predicate_field",
        "0700_all_explicit_wildcards_equals_empty_args",
        "0902_entity_id_single_quote",
    ];
    let parts: Vec<Part> = names.iter().map(|n| part(&cases, n)).collect();
    let glued = glue(&parts, GAP_WIDE);
    let totals = check(&glued);

    let (all, _) = map_of(&glued);
    assert!(all.len() >= 8, "expected a leaf per constituent: {all:?}");
    // Density: with eight constituents in one policy set, a decision reads a small
    // fraction of the installed leaves.
    let per_decision = totals.sliced_leaves as f64 / totals.decisions as f64;
    assert!(
        per_decision < 2.0,
        "a decision computed {per_decision:.2} leaves of {} installed: {totals:?}",
        all.len()
    );
    eprintln!(
        "dense 8-way glue: {} leaves installed, {per_decision:.2} computed per decision, {totals:?}",
        all.len()
    );
}

/// Breadth, not shapes: glue the whole gluable corpus in consecutive pairs and
/// run the differential over every one. Each glued case is a two-action case
/// whose expected stream is its constituents' committed streams concatenated, so
/// this checks composition and slicing together across hundreds of action pairs
/// nobody wrote by hand.
#[test]
fn the_whole_corpus_glued_pairwise_never_changes_a_verdict() {
    let cases = corpus();
    let gluable: Vec<&Case> = cases.iter().filter(|c| gluable(c)).collect();
    assert!(
        gluable.len() > 300,
        "too few gluable cases: {}",
        gluable.len()
    );

    // Constituents must share an event schema — the glued case has one, and a
    // case that overrides it means something specific by it (author-defined event
    // kinds, renamed injected fields, pins). So pair within each event schema's
    // own group rather than across.
    let mut by_event_schema: BTreeMap<&str, Vec<&Case>> = BTreeMap::new();
    for case in &gluable {
        by_event_schema
            .entry(case.event_schema.as_str())
            .or_default()
            .push(case);
    }
    let glued: Vec<Case> = by_event_schema
        .values()
        .flat_map(|group| group.chunks(2))
        .filter(|pair| pair.len() == 2)
        .map(|pair| {
            glue(
                &[
                    Part {
                        case: pair[0],
                        trace: 0,
                    },
                    Part {
                        case: pair[1],
                        trace: 0,
                    },
                ],
                GAP_WIDE,
            )
        })
        .collect();

    let (totals, failures) = check_all(&glued);
    eprintln!(
        "glued pairwise: {} cases from {} corpus cases: {totals:?}",
        glued.len(),
        gluable.len()
    );
    assert!(
        failures.is_empty(),
        "{} failure(s):\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
    assert!(totals.decisions > 500, "too few decisions: {totals:?}");
    assert!(
        totals.sliced_leaves * 2 < totals.unsliced_leaves,
        "pairwise gluing should roughly halve the leaves computed: {totals:?}"
    );
    assert!(
        totals.zero_leaf_decisions > 0,
        "no glued decision computed nothing: {totals:?}"
    );
}
