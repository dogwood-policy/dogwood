//! Stable policy identity: `IdSource`, `PolicyRef` revisions, the policy-set
//! version, and live policy updates through `Authorizer::update_policies`.
//!
//! The live-update scenario (`live_update_*`) deploys three versions of one
//! policy set on a running authorizer:
//!
//! - **V1:** five rules.
//! - **V2:** a rule inserted at the top, the rest reversed, one rule's Cedar
//!   condition edited, another's window edited, one rule removed, and a kept
//!   rule given an extra annotation and a comment (not a semantic edit).
//! - **V3:** the removed rule re-added verbatim, a rule with no temporal leaf
//!   added, and the order reversed again.
//!
//! At every decision the reported supporting policies must equal the expected
//! stable ids (hand-computed), and must agree with an oracle: a fresh
//! authorizer for the version in force, replaying the whole history.

use std::collections::BTreeSet;

use dogwood_language::{
    AuthorizationDecision, AuthorizationRequest, Authorizer, Decision, Distincter, Error, Event,
    IdSource, LoweredPolicySet, ParsedPolicySet, PolicyEngine, PolicyIdErrorKind, PolicySchema,
    Response, ServiceSchema, TemporalBindings, TemporalEngine, TemporalField, Value, lower_many,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type DocInput = { doc: String };
  entity Gateway;
  entity User;
  action "Login" appliesTo { principal: [User], resource: [Gateway], context: { input: DocInput } };
  action "Approve" appliesTo { principal: [User], resource: [Gateway], context: { input: DocInput } };
  action "Delete" appliesTo { principal: [User], resource: [Gateway], context: { input: DocInput } };
  action "Read" appliesTo { principal: [User], resource: [Gateway], context: { input: DocInput } };
  action "Write" appliesTo { principal: [User], resource: [Gateway], context: { input: DocInput } };
}
"#;

// ─── the rules of the live-update scenario ───────────────────────────

const R1_READ_AFTER_LOGIN: &str = r#"
@id("read-after-login")
permit (principal, action == Drupe::Action::"Read", resource)
when temporal { formerly within 1d Drupe::Action::"Login"::request{} };
"#;

/// R1 again, reformatted, commented and given another annotation: the same
/// rule, so the same revision.
const R1_RESTYLED: &str = r#"
// Reads need a login in the last day.
@advice("log in first")
@id("read-after-login")
permit (
    principal,
    action == Drupe::Action::"Read",
    resource
)
when temporal {
    formerly within 1d Drupe::Action::"Login"::request{ }
};
"#;

const R2_WRITE_AFTER_LOGIN: &str = r#"
@id("write-after-login")
permit (principal, action == Drupe::Action::"Write", resource)
when temporal { formerly within 1d Drupe::Action::"Login"::request{} };
"#;

const R3_DENY_SECRET: &str = r#"
@id("deny-secret-read")
forbid (principal, action == Drupe::Action::"Read", resource)
when { context.input.doc == "secret" };
"#;

/// R3 with its Cedar condition edited.
const R3_DENY_CLASSIFIED: &str = r#"
@id("deny-secret-read")
forbid (principal, action == Drupe::Action::"Read", resource)
when { context.input.doc == "classified" };
"#;

const R4_DENY_WRITE_AFTER_DELETE: &str = r#"
@id("deny-write-after-delete")
forbid (principal, action == Drupe::Action::"Write", resource)
when temporal { formerly within 10m Drupe::Action::"Delete"::request{} };
"#;

const R5_READ_AFTER_APPROVAL: &str = r#"
@id("read-after-approval")
permit (principal, action == Drupe::Action::"Read", resource)
when temporal { formerly within 5m Drupe::Action::"Approve"::request{ input.doc: context.input.doc } };
"#;

/// R5 with its window edited (5m to 2m).
const R5_SHORT_WINDOW: &str = r#"
@id("read-after-approval")
permit (principal, action == Drupe::Action::"Read", resource)
when temporal { formerly within 2m Drupe::Action::"Approve"::request{ input.doc: context.input.doc } };
"#;

/// Inserted at the top of V2; no temporal leaf.
const R0_OPS_READ: &str = r#"
@id("ops-read")
permit (principal, action == Drupe::Action::"Read", resource)
when { context.input.doc == "ops" };
"#;

/// Added in V3; no temporal leaf.
const R6_AUDIT_WRITE: &str = r#"
@id("audit-write")
permit (principal, action == Drupe::Action::"Write", resource)
when { context.input.doc == "audit" };
"#;

fn v1() -> String {
    [
        R1_READ_AFTER_LOGIN,
        R2_WRITE_AFTER_LOGIN,
        R3_DENY_SECRET,
        R4_DENY_WRITE_AFTER_DELETE,
        R5_READ_AFTER_APPROVAL,
    ]
    .concat()
}

fn v2() -> String {
    [
        R0_OPS_READ,
        R5_SHORT_WINDOW,
        R3_DENY_CLASSIFIED,
        R2_WRITE_AFTER_LOGIN,
        R1_RESTYLED,
    ]
    .concat()
}

fn v3() -> String {
    [
        R1_READ_AFTER_LOGIN,
        R2_WRITE_AFTER_LOGIN,
        R4_DENY_WRITE_AFTER_DELETE,
        R3_DENY_CLASSIFIED,
        R5_SHORT_WINDOW,
        R0_OPS_READ,
        R6_AUDIT_WRITE,
    ]
    .concat()
}

fn service() -> ServiceSchema {
    ServiceSchema::defaults()
}

fn policy_schema() -> PolicySchema {
    PolicySchema::from_cedarschema_str(SCHEMA).expect("schema builds")
}

fn lower_with(source: &str, ids: IdSource) -> LoweredPolicySet {
    ParsedPolicySet::parse(source, &service())
        .expect("parses")
        .with_ids(ids)
        .expect("ids assign")
        .lower(&policy_schema())
        .expect("lowers")
}

fn lower_annotated(source: &str) -> LoweredPolicySet {
    lower_with(source, IdSource::Annotation)
}

fn event(action: &str, ts: i64, doc: &str) -> Event {
    Event::builder(&format!("Drupe::Action::{action}"), "request")
        .timestamp(ts)
        .principal("Drupe::User::\"alice\"")
        .resource("Drupe::Gateway::\"gw\"")
        .field("input", "doc", Value::String(doc.to_string()))
        .request_context("input", "doc", Value::String(doc.to_string()))
        .build()
}

fn ids(response: &Response) -> BTreeSet<String> {
    response
        .diagnostics()
        .determining()
        .map(|p| p.id().to_string())
        .collect()
}

fn set(ids: &[&str]) -> BTreeSet<String> {
    ids.iter().map(|s| s.to_string()).collect()
}

/// The revision `lowered` reports for the rule with policy id `id`.
fn revision(lowered: &LoweredPolicySet, id: &str) -> String {
    lowered
        .policy_ref(id)
        .unwrap_or_else(|| panic!("no rule `{id}`"))
        .revision()
        .to_string()
}

// ─── default behavior is unchanged ───────────────────────────────────

#[test]
fn positional_ids_are_the_default_and_unchanged() {
    let lowered = LoweredPolicySet::from_str(&v1(), &service(), &policy_schema()).expect("lowers");
    assert!(!lowered.has_stable_ids());
    let rule_ids: Vec<String> = lowered.rules().map(|r| r.cedar_policy_id).collect();
    assert_eq!(
        rule_ids,
        ["policy_0", "policy_1", "policy_2", "policy_3", "policy_4"]
    );
    // `@id` stays an ordinary annotation under the default.
    let positional = lower_with(&v1(), IdSource::Positional);
    let explicit_positional: Vec<String> = positional.rules().map(|r| r.cedar_policy_id).collect();
    assert_eq!(rule_ids, explicit_positional);

    let mut authz = Authorizer::new(lowered);
    authz.is_authorized(&event("Login", 0, "x"));
    let response = authz
        .is_authorized(&event("Read", 10, "x"))
        .expect("decides");
    assert_eq!(response.decision(), Decision::Allow);
    // No version under positional ids; `determining()` parallels `reason()`.
    assert!(response.policy_set().is_none());
    let reason: Vec<&str> = response
        .diagnostics()
        .reason()
        .map(|r| r.cedar_policy_id.as_str())
        .collect();
    let determining: Vec<&str> = response
        .diagnostics()
        .determining()
        .map(|p| p.id())
        .collect();
    assert_eq!(reason, ["policy_0"]);
    assert_eq!(reason, determining);
}

// ─── id sources ──────────────────────────────────────────────────────

#[test]
fn annotation_ids_become_the_cedar_policy_ids_and_leaf_names_stay_positional() {
    let lowered = lower_annotated(&v1());
    assert!(lowered.has_stable_ids());
    let rule_ids: Vec<String> = lowered.rules().map(|r| r.cedar_policy_id).collect();
    assert_eq!(
        rule_ids,
        [
            "read-after-login",
            "write-after-login",
            "deny-secret-read",
            "deny-write-after-delete",
            "read-after-approval",
        ]
    );
    let mut cedar_ids: Vec<String> = lowered
        .as_cedar()
        .policies()
        .map(|p| p.id().to_string())
        .collect();
    cedar_ids.sort();
    let mut expected = rule_ids.clone();
    expected.sort();
    assert_eq!(cedar_ids, expected);

    // The hoisted field names are unchanged by the id source.
    let leaf_ids: Vec<String> = lowered.temporal_fields().map(|f| f.id.clone()).collect();
    let positional = LoweredPolicySet::from_str(&v1(), &service(), &policy_schema()).unwrap();
    let positional_leaf_ids: Vec<String> =
        positional.temporal_fields().map(|f| f.id.clone()).collect();
    assert_eq!(leaf_ids, positional_leaf_ids);
    assert_eq!(
        leaf_ids,
        [
            "policy_0__temporal_0",
            "policy_1__temporal_0",
            "policy_3__temporal_0",
            "policy_4__temporal_0",
        ]
    );
    // ...and so are the revisions (they never depend on the id).
    let revs: Vec<String> = lowered
        .policy_refs()
        .map(|p| p.revision().to_string())
        .collect();
    let positional_revs: Vec<String> = positional
        .policy_refs()
        .map(|p| p.revision().to_string())
        .collect();
    assert_eq!(revs, positional_revs);
}

#[test]
fn parsed_policies_expose_their_ids_before_lowering() {
    let parsed = ParsedPolicySet::parse(&v1(), &service())
        .unwrap()
        .with_ids(IdSource::Annotation)
        .unwrap();
    let ids: Vec<Option<&str>> = parsed.policies().map(|p| p.policy_id()).collect();
    assert_eq!(ids[0], Some("read-after-login"));
    assert_eq!(ids[4], Some("read-after-approval"));
    let positional = ParsedPolicySet::parse(&v1(), &service()).unwrap();
    assert!(positional.policies().all(|p| p.policy_id().is_none()));
}

#[test]
fn explicit_ids_name_rules_by_position_in_the_source_and_ignore_annotations() {
    let explicit = IdSource::Explicit(
        ["r-a", "r-b", "r-c", "r-d", "r-e"]
            .map(str::to_string)
            .to_vec(),
    );
    let lowered = lower_with(&v1(), explicit);
    let rule_ids: Vec<String> = lowered.rules().map(|r| r.cedar_policy_id).collect();
    assert_eq!(rule_ids, ["r-a", "r-b", "r-c", "r-d", "r-e"]);
    // Positional (unannotated) source works the same.
    let unannotated = "permit (principal, action == Drupe::Action::\"Read\", resource);";
    let lowered = lower_with(
        unannotated,
        IdSource::Explicit(vec!["018f7f9e-1b2c-7d3e-8f40-123456789abc".to_string()]),
    );
    assert_eq!(
        lowered.rules().next().unwrap().cedar_policy_id,
        "018f7f9e-1b2c-7d3e-8f40-123456789abc"
    );
}

fn id_error(source: &str, ids: IdSource) -> dogwood_language::PolicyIdError {
    match ParsedPolicySet::parse(source, &service())
        .expect("parses")
        .with_ids(ids)
    {
        Err(Error::PolicyId(e)) => e,
        Err(other) => panic!("expected Error::PolicyId, got {other:?}"),
        Ok(_) => panic!("expected the ids to be rejected"),
    }
}

#[test]
fn annotation_ids_must_be_present() {
    let source = format!(
        "{R1_READ_AFTER_LOGIN}\npermit (principal, action == Drupe::Action::\"Write\", resource);"
    );
    let e = id_error(&source, IdSource::Annotation);
    assert_eq!(e.kind(), PolicyIdErrorKind::Missing);
    assert_eq!(e.policy_index(), Some(1));
    assert!(e.location().is_some(), "the error points at the policy");
    assert!(e.to_string().contains("policy 1"), "{e}");

    // `@id` with no value is missing too.
    let e = id_error(
        "@id\npermit (principal, action, resource);",
        IdSource::Annotation,
    );
    assert_eq!(e.kind(), PolicyIdErrorKind::Missing);
}

/// A rule with two `@id` annotations has no one id: the stable id would be one
/// of them and Cedar's policy keeps the last, so `IdSource::Annotation` rejects
/// it, naming the rule and the second annotation. Positional ids read no
/// annotation, and accept it.
#[test]
fn a_rule_with_two_id_annotations_is_rejected() {
    let source = "@id(\"x\")\n@id(\"y\")\npermit (principal, action, resource);";
    let e = id_error(source, IdSource::Annotation);
    assert_eq!(e.kind(), PolicyIdErrorKind::RepeatedAnnotation);
    assert_eq!(e.policy_index(), Some(0));
    assert_eq!(e.id(), None);
    assert!(e.location().is_some(), "the error points at the policy");
    assert_eq!(
        e.to_string(),
        "policy 0 has a second `@id` annotation, `@id(\"y\")` after `@id(\"x\")`; \
         IdSource::Annotation takes a policy's id from its one `@id(\"…\")` annotation"
    );

    // A second rule's, and one without a value, count too.
    let e = id_error(
        &format!("{R1_READ_AFTER_LOGIN}\n@id\n@id(\"y\")\npermit (principal, action, resource);"),
        IdSource::Annotation,
    );
    assert_eq!(e.kind(), PolicyIdErrorKind::RepeatedAnnotation);
    assert_eq!(e.policy_index(), Some(1));
    assert!(e.to_string().contains("`@id(\"y\")` after `@id`"), "{e}");

    let parsed = ParsedPolicySet::parse(source, &service()).expect("parses");
    assert!(parsed.with_ids(IdSource::Positional).is_ok());
}

#[test]
fn ids_must_be_unique() {
    let source = format!("{R3_DENY_SECRET}{R1_READ_AFTER_LOGIN}{R3_DENY_CLASSIFIED}");
    let e = id_error(&source, IdSource::Annotation);
    assert_eq!(e.kind(), PolicyIdErrorKind::Duplicate);
    assert_eq!(e.id(), Some("deny-secret-read"));
    assert_eq!(e.policy_index(), Some(2));
    assert!(e.to_string().contains("policies 0 and 2"), "{e}");

    let e = id_error(
        &v1(),
        IdSource::Explicit(["a", "b", "a", "c", "d"].map(str::to_string).to_vec()),
    );
    assert_eq!(e.kind(), PolicyIdErrorKind::Duplicate);
    assert_eq!(e.policy_index(), Some(2));
}

#[test]
fn ids_must_be_valid_and_explicit_lists_complete() {
    let e = id_error(
        "@id(\"a/b\")\npermit (principal, action, resource);",
        IdSource::Annotation,
    );
    assert_eq!(e.kind(), PolicyIdErrorKind::Invalid);
    assert_eq!(e.id(), Some("a/b"));
    let e = id_error(
        "@id(\"\")\npermit (principal, action, resource);",
        IdSource::Annotation,
    );
    assert_eq!(e.kind(), PolicyIdErrorKind::Invalid);
    let e = id_error(
        "permit (principal, action, resource);",
        IdSource::Explicit(vec!["has space".to_string()]),
    );
    assert_eq!(e.kind(), PolicyIdErrorKind::Invalid);
    let e = id_error(&v1(), IdSource::Explicit(vec!["only-one".to_string()]));
    assert_eq!(e.kind(), PolicyIdErrorKind::CountMismatch);
    assert_eq!(e.policy_index(), None);
}

#[test]
fn positional_restores_todays_ids() {
    let parsed = ParsedPolicySet::parse(&v1(), &service())
        .unwrap()
        .with_ids(IdSource::Annotation)
        .unwrap()
        .with_ids(IdSource::Positional)
        .unwrap();
    let lowered = parsed.lower(&policy_schema()).unwrap();
    assert!(!lowered.has_stable_ids());
    assert_eq!(lowered.rules().next().unwrap().cedar_policy_id, "policy_0");
}

// ─── distincter prefixes ─────────────────────────────────────────────

#[test]
fn a_distincter_prefixes_stable_ids_with_a_slash() {
    let lowered = ParsedPolicySet::parse(&v1(), &service())
        .unwrap()
        .with_ids(IdSource::Annotation)
        .unwrap()
        .lower_with_distincter(&policy_schema(), "sys")
        .unwrap();
    let rule_ids: Vec<String> = lowered.rules().map(|r| r.cedar_policy_id).collect();
    assert_eq!(rule_ids[0], "sys/read-after-login");
    assert_eq!(rule_ids[4], "sys/read-after-approval");
    // The field names keep the positional distincter key.
    assert_eq!(
        lowered.temporal_fields().next().unwrap().id,
        "sys_0__temporal_0"
    );
}

#[test]
fn lower_many_prefixes_each_entry_and_keeps_shared_rules_identical() {
    let service = service();
    let schema = policy_schema();
    let system =
        ParsedPolicySet::parse(&format!("{R1_READ_AFTER_LOGIN}{R3_DENY_SECRET}"), &service)
            .unwrap()
            .with_ids(IdSource::Annotation)
            .unwrap();
    let alice = ParsedPolicySet::parse(R2_WRITE_AFTER_LOGIN, &service)
        .unwrap()
        .with_ids(IdSource::Explicit(vec!["rule-17".to_string()]))
        .unwrap();
    let bob = ParsedPolicySet::parse(
        &format!("{R5_READ_AFTER_APPROVAL}{R6_AUDIT_WRITE}"),
        &service,
    )
    .unwrap()
    .with_ids(IdSource::Explicit(vec![
        "rule-3".to_string(),
        "rule-4".to_string(),
    ]))
    .unwrap();
    let d = |s: &str| -> Distincter { s.parse().unwrap() };

    let for_alice = lower_many(&[(&system, d("sys")), (&alice, d("usr"))], &schema).unwrap();
    let for_bob = lower_many(&[(&system, d("sys")), (&bob, d("usr"))], &schema).unwrap();
    assert!(for_alice.has_stable_ids() && for_bob.has_stable_ids());

    let alice_ids: Vec<String> = for_alice
        .policy_refs()
        .map(|p| p.id().to_string())
        .collect();
    assert_eq!(
        alice_ids,
        [
            "sys/read-after-login",
            "sys/deny-secret-read",
            "usr/rule-17"
        ]
    );
    let bob_ids: Vec<String> = for_bob.policy_refs().map(|p| p.id().to_string()).collect();
    assert_eq!(
        bob_ids,
        [
            "sys/read-after-login",
            "sys/deny-secret-read",
            "usr/rule-3",
            "usr/rule-4"
        ]
    );
    // A system rule has one id and one revision in every user's set.
    for id in ["sys/read-after-login", "sys/deny-secret-read"] {
        assert_eq!(for_alice.policy_ref(id), for_bob.policy_ref(id));
    }

    // Decisions name the prefixed ids.
    let mut authz = Authorizer::new(for_alice);
    authz.is_authorized(&event("Login", 0, "x"));
    let r = authz.is_authorized(&event("Write", 5, "x")).unwrap();
    assert_eq!(ids(&r), set(&["usr/rule-17"]));
    let r = authz.is_authorized(&event("Read", 6, "secret")).unwrap();
    assert_eq!(r.decision(), Decision::Deny);
    assert_eq!(ids(&r), set(&["sys/deny-secret-read"]));

    // Mixing a positional entry in makes the merged set not stable.
    let positional = ParsedPolicySet::parse(R6_AUDIT_WRITE, &service).unwrap();
    let mixed = lower_many(&[(&system, d("sys")), (&positional, d("usr"))], &schema).unwrap();
    assert!(!mixed.has_stable_ids());
    let mixed_ids: Vec<String> = mixed.policy_refs().map(|p| p.id().to_string()).collect();
    assert_eq!(
        mixed_ids,
        ["sys/read-after-login", "sys/deny-secret-read", "usr_0"]
    );
}

// ─── revisions ───────────────────────────────────────────────────────

#[test]
fn revisions_ignore_order_format_comments_and_annotations() {
    let a = lower_annotated(&v1());
    let reordered = lower_annotated(
        &[
            R5_READ_AFTER_APPROVAL,
            R4_DENY_WRITE_AFTER_DELETE,
            R3_DENY_SECRET,
            R2_WRITE_AFTER_LOGIN,
            R1_RESTYLED,
        ]
        .concat(),
    );
    for p in a.policy_refs() {
        assert_eq!(
            reordered.policy_ref(p.id()).as_ref(),
            Some(&p),
            "rule `{}` kept its revision across a reorder and restyle",
            p.id()
        );
    }
    // Revisions do not depend on the id, either: a renamed rule keeps it.
    let renamed = lower_annotated(&R1_READ_AFTER_LOGIN.replace("read-after-login", "renamed"));
    assert_eq!(
        revision(&renamed, "renamed"),
        revision(&a, "read-after-login")
    );
}

#[test]
fn revisions_change_on_semantic_edits() {
    let base = lower_annotated(R5_READ_AFTER_APPROVAL);
    let rev = revision(&base, "read-after-approval");
    let edits = [
        // window
        R5_SHORT_WINDOW.to_string(),
        // effect
        R5_READ_AFTER_APPROVAL.replace("permit", "forbid"),
        // scope
        R5_READ_AFTER_APPROVAL.replace("\"Read\", resource", "\"Write\", resource"),
        // temporal predicate
        R5_READ_AFTER_APPROVAL.replace("\"Approve\"::request", "\"Login\"::request"),
        // correlation
        R5_READ_AFTER_APPROVAL.replace("input.doc: context.input.doc", ""),
        // an added Cedar condition
        R5_READ_AFTER_APPROVAL.replace("};", "}\nwhen { context.input.doc != \"x\" };"),
    ];
    let mut seen = BTreeSet::from([rev.clone()]);
    for edited in &edits {
        let r = revision(&lower_annotated(edited), "read-after-approval");
        assert_ne!(r, rev, "edit did not change the revision:\n{edited}");
        assert!(seen.insert(r), "two different edits share a revision");
    }
    // The Cedar-only edit of R3.
    assert_ne!(
        revision(&lower_annotated(R3_DENY_SECRET), "deny-secret-read"),
        revision(&lower_annotated(R3_DENY_CLASSIFIED), "deny-secret-read"),
    );
    // Revisions are lowercase hex SHA-256.
    assert_eq!(rev.len(), 64);
    assert!(
        rev.chars()
            .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
    );
}

#[test]
fn revisions_do_not_depend_on_macro_gensym_offsets() {
    // A macro binder is gensym'd from its call site's byte offset, so text
    // inserted before a macro-using rule renames its binders. The revision
    // must not move.
    let def = r#"
def temporal count_formerly(?w, ?s) {
    count for ($t: Timepoint). where (formerly within ?w (?s && tp($t)))
};
"#;
    let rule = r#"
@id("uses-macro")
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    exists (n: Long). ((count_formerly(1h, Drupe::Action::"Login"::request{})) == n && n > 0)
};
"#;
    let alone = lower_annotated(&format!("{def}{rule}"));
    let shifted = lower_annotated(&format!(
        "{def}{R6_AUDIT_WRITE}\n// padding padding\n{rule}"
    ));
    assert_eq!(
        revision(&alone, "uses-macro"),
        revision(&shifted, "uses-macro")
    );
}

#[test]
fn revisions_follow_the_event_schema_pins() {
    // The default event schema pins `callerPrincipal`; the unpinned one does
    // not. The same text then means a different leaf, so a different revision.
    let pinned = lower_annotated(R1_READ_AFTER_LOGIN);
    let unpinned_service = ServiceSchema::builder()
        .event_schema_str(dogwood_language::UNPINNED_EVENT_SCHEMA)
        .build()
        .expect("service builds");
    let unpinned = ParsedPolicySet::parse(R1_READ_AFTER_LOGIN, &unpinned_service)
        .unwrap()
        .with_ids(IdSource::Annotation)
        .unwrap()
        .lower(&policy_schema())
        .unwrap();
    assert_ne!(
        revision(&pinned, "read-after-login"),
        revision(&unpinned, "read-after-login")
    );
}

// ─── leaf content hashes ─────────────────────────────────────────────

#[test]
fn leaf_content_hashes_are_position_free() {
    let v1 = lower_annotated(&v1());
    let v2 = lower_annotated(&v2());
    let hashes = |l: &LoweredPolicySet| -> Vec<String> {
        l.temporal_fields()
            .map(TemporalField::content_hash)
            .collect()
    };
    let (h1, h2) = (hashes(&v1), hashes(&v2));
    // V1 leaves: R1, R2, R4, R5. V2 leaves: R5', R2, R1.
    assert_eq!(h1.len(), 4);
    assert_eq!(h2.len(), 3);
    assert_eq!(h1[0], h2[2], "R1's leaf hashes alike at position 0 and 4");
    assert_eq!(h1[1], h2[1], "R2's leaf");
    assert_ne!(h1[3], h2[0], "R5's leaf changed with its window");
    // R1 and R2 have the same condition but different action scopes.
    assert_ne!(h1[0], h1[1]);
    // The leaf name moved; the hash did not.
    assert_ne!(
        v1.temporal_fields().next().unwrap().id,
        v2.temporal_fields().nth(2).unwrap().id
    );
}

// ─── versions ────────────────────────────────────────────────────────

#[test]
fn version_hashes_identify_the_rules_and_ignore_order() {
    let a = lower_annotated(&v1());
    let again = lower_annotated(&v1());
    assert_eq!(a.version_hash(), again.version_hash());
    let restyled = lower_annotated(&v1().replace(R1_READ_AFTER_LOGIN, R1_RESTYLED));
    assert_eq!(a.version_hash(), restyled.version_hash());
    let v2 = lower_annotated(&v2());
    assert_ne!(a.version_hash(), v2.version_hash());
    assert_eq!(a.version_hash().len(), 64);
}

// ─── fail-closed on ids the set does not contain ─────────────────────

/// A policy engine that always allows, naming a fixed id.
struct NamesId(&'static str);

impl PolicyEngine for NamesId {
    fn prepare(
        &mut self,
        _: &dogwood_language::cedar::PolicySet,
        _: &dogwood_language::cedar::Schema,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn is_authorized(&self, _: AuthorizationRequest<'_>) -> AuthorizationDecision {
        AuthorizationDecision {
            decision: Decision::Allow,
            determining_policy_ids: vec![self.0.to_string()],
            errors: Vec::new(),
        }
    }
}

#[test]
fn an_unknown_determining_id_fails_closed_with_stable_ids() {
    let mut authz = Authorizer::builder(lower_annotated(&v1()))
        .policy_engine(NamesId("avp-7f3a"))
        .build()
        .unwrap();
    let r = authz.is_authorized(&event("Read", 0, "x")).unwrap();
    assert_eq!(r.decision(), Decision::Deny);
    assert_eq!(r.diagnostics().determining().count(), 0);
    let errors: Vec<&str> = r.diagnostics().errors().collect();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("`avp-7f3a`") && e.contains("failing closed")),
        "{errors:?}"
    );
    assert!(r.policy_set().is_some());

    // A known id is reported as usual.
    let mut authz = Authorizer::builder(lower_annotated(&v1()))
        .policy_engine(NamesId("read-after-login"))
        .build()
        .unwrap();
    let r = authz.is_authorized(&event("Read", 0, "x")).unwrap();
    assert_eq!(r.decision(), Decision::Allow);
    assert_eq!(ids(&r), set(&["read-after-login"]));
}

#[test]
fn an_unknown_determining_id_is_still_dropped_under_positional_ids() {
    // Today's behavior, kept for existing deployments.
    let lowered = LoweredPolicySet::from_str(&v1(), &service(), &policy_schema()).unwrap();
    let mut authz = Authorizer::builder(lowered)
        .policy_engine(NamesId("avp-7f3a"))
        .build()
        .unwrap();
    let r = authz.is_authorized(&event("Read", 0, "x")).unwrap();
    assert_eq!(r.decision(), Decision::Allow);
    assert_eq!(r.diagnostics().reason().count(), 0);
    assert_eq!(r.diagnostics().errors().count(), 0);
}

// ─── erroring policies ───────────────────────────────────────────────

#[test]
fn erroring_policies_are_reported_by_id_and_revision() {
    // `context.input.missing` does not exist, so the policy errs at runtime
    // (validation would flag it; lowering does not).
    let source = r#"
@id("reads-a-missing-field")
forbid (principal, action == Drupe::Action::"Read", resource)
when { context.input has doc && context.input.doc.lessThan(decimal("1.0")) };

@id("always-read")
permit (principal, action == Drupe::Action::"Read", resource);
"#;
    let lowered = lower_annotated(source);
    let erring_rev = revision(&lowered, "reads-a-missing-field");
    let mut authz = Authorizer::new(lowered);
    let r = authz.is_authorized(&event("Read", 0, "x")).unwrap();
    assert_eq!(r.decision(), Decision::Allow);
    assert_eq!(ids(&r), set(&["always-read"]));
    let erroring: Vec<_> = r.diagnostics().erroring().collect();
    assert_eq!(erroring.len(), 1, "{:?}", r.diagnostics());
    assert_eq!(erroring[0].policy().id(), "reads-a-missing-field");
    assert_eq!(erroring[0].policy().revision(), erring_rev);
    assert!(!erroring[0].message().is_empty());
    // The text channel is unchanged: Cedar's message, naming the policy.
    let errors: Vec<&str> = r.diagnostics().errors().collect();
    assert_eq!(errors.len(), 1);
    assert!(errors[0].contains("reads-a-missing-field"), "{errors:?}");
}

// ─── live updates ────────────────────────────────────────────────────

/// One step of the scenario: deploy a version, or submit an event with the
/// expected decision and supporting policies.
enum Step {
    Deploy(fn() -> String),
    Decide(
        &'static str,
        i64,
        &'static str,
        Decision,
        &'static [&'static str],
    ),
}

use Step::{Decide, Deploy};

/// The live-update scenario. Each deployment follows a gap longer than the
/// short windows (10m, 5m, 2m), so the new and edited leaves see the same
/// past under every update reading, while the one-day `Login` leaves carry
/// their history across both updates.
const SCENARIO: &[Step] = &[
    Deploy(v1),
    Decide("Login", 0, "x", Decision::Deny, &[]),
    Decide("Read", 10, "x", Decision::Allow, &["read-after-login"]),
    Decide("Approve", 20, "x", Decision::Deny, &[]),
    Decide(
        "Read",
        30,
        "x",
        Decision::Allow,
        &["read-after-login", "read-after-approval"],
    ),
    Decide("Read", 40, "secret", Decision::Deny, &["deny-secret-read"]),
    Decide("Delete", 50, "x", Decision::Deny, &[]),
    Decide(
        "Write",
        60,
        "x",
        Decision::Deny,
        &["deny-write-after-delete"],
    ),
    Deploy(v2),
    Decide(
        "Read",
        2010,
        "ops",
        Decision::Allow,
        &["ops-read", "read-after-login"],
    ),
    Decide("Approve", 2020, "x", Decision::Deny, &[]),
    Decide(
        "Read",
        2030,
        "x",
        Decision::Allow,
        &["read-after-login", "read-after-approval"],
    ),
    Decide(
        "Read",
        2040,
        "secret",
        Decision::Allow,
        &["read-after-login"],
    ),
    Decide(
        "Read",
        2050,
        "classified",
        Decision::Deny,
        &["deny-secret-read"],
    ),
    Decide("Delete", 2060, "x", Decision::Deny, &[]),
    Decide("Write", 2070, "x", Decision::Allow, &["write-after-login"]),
    Deploy(v3),
    Decide("Write", 4010, "x", Decision::Allow, &["write-after-login"]),
    Decide("Delete", 4020, "x", Decision::Deny, &[]),
    Decide(
        "Write",
        4030,
        "x",
        Decision::Deny,
        &["deny-write-after-delete"],
    ),
    Decide(
        "Write",
        4040,
        "audit",
        Decision::Deny,
        &["deny-write-after-delete"],
    ),
    Decide(
        "Write",
        4050,
        "ops",
        Decision::Deny,
        &["deny-write-after-delete"],
    ),
    Decide("Read", 4060, "x", Decision::Allow, &["read-after-login"]),
    Decide(
        "Read",
        4070,
        "ops",
        Decision::Allow,
        &["ops-read", "read-after-login"],
    ),
];

/// The oracle: a fresh authorizer for `version`, replaying the whole history
/// (the retrospective reading), decides `last`.
fn oracle(version: &str, history: &[Event]) -> Response {
    let mut authz = Authorizer::new(lower_annotated(version));
    let mut last = None;
    for e in history {
        last = authz.is_authorized(e);
    }
    last.expect("the last event decides")
}

#[test]
fn live_update_reports_stable_supporting_policies_at_every_decision() {
    let mut authz: Option<Authorizer> = None;
    let mut deployed = String::new();
    let mut history: Vec<Event> = Vec::new();
    let mut generation = 0;
    let mut decisions = 0;
    for step in SCENARIO {
        match step {
            Deploy(version) => {
                deployed = version();
                let lowered = lower_annotated(&deployed);
                match authz.as_mut() {
                    None => authz = Some(Authorizer::new(lowered)),
                    Some(a) => {
                        a.update_policies(lowered).expect("live update");
                        generation += 1;
                    }
                }
            }
            Decide(action, ts, doc, decision, expected) => {
                let e = event(action, *ts, doc);
                history.push(e.clone());
                let a = authz.as_mut().expect("deployed");
                let r = a.is_authorized(&e).expect("a request decides");
                let what = format!("{action}({doc}) at {ts}");
                assert_eq!(r.decision(), *decision, "{what}: {:?}", r.diagnostics());
                assert_eq!(ids(&r), set(expected), "{what}");
                // The response names the deployment it was decided under.
                let version = r.policy_set().expect("stable ids carry a version");
                assert_eq!(version.generation(), generation, "{what}");
                assert_eq!(version.hash(), lower_annotated(&deployed).version_hash());
                // Every reported revision is the deployed rule's revision.
                let current = lower_annotated(&deployed);
                for p in r.diagnostics().determining() {
                    assert_eq!(current.policy_ref(p.id()).as_ref(), Some(p), "{what}");
                }
                // The oracle agrees, supporting policies included.
                let o = oracle(&deployed, &history);
                assert_eq!(r.decision(), o.decision(), "{what}: oracle decision");
                assert_eq!(
                    r.diagnostics().determining().collect::<BTreeSet<_>>(),
                    o.diagnostics().determining().collect::<BTreeSet<_>>(),
                    "{what}: oracle supporting policies"
                );
                decisions += 1;
            }
        }
    }
    assert_eq!(generation, 2);
    assert_eq!(decisions, 21);
}

#[test]
fn live_update_revisions_track_edits_and_re_adds() {
    let (a, b, c) = (
        lower_annotated(&v1()),
        lower_annotated(&v2()),
        lower_annotated(&v3()),
    );
    // Kept (moved, restyled): one revision throughout.
    assert_eq!(
        revision(&a, "read-after-login"),
        revision(&b, "read-after-login")
    );
    assert_eq!(
        revision(&b, "read-after-login"),
        revision(&c, "read-after-login")
    );
    // Edited in V2: a new revision, kept in V3.
    for id in ["read-after-approval", "deny-secret-read"] {
        assert_ne!(revision(&a, id), revision(&b, id), "{id}");
        assert_eq!(revision(&b, id), revision(&c, id), "{id}");
    }
    // Removed in V2, re-added verbatim in V3: its V1 revision.
    assert!(b.policy_ref("deny-write-after-delete").is_none());
    assert_eq!(
        revision(&a, "deny-write-after-delete"),
        revision(&c, "deny-write-after-delete")
    );
}

#[test]
fn positional_ids_misattribute_after_the_same_update() {
    // The contrast: under positional ids, `policy_0` is R1 in V1 but the
    // inserted R0 in V2 — the same string names a different rule, silently.
    let v1 = LoweredPolicySet::from_str(&v1(), &service(), &policy_schema()).unwrap();
    let v2 = LoweredPolicySet::from_str(&v2(), &service(), &policy_schema()).unwrap();
    assert_ne!(
        v1.policy_ref("policy_0").unwrap().revision(),
        v2.policy_ref("policy_0").unwrap().revision()
    );
    let r1_rev = v1.policy_ref("policy_0").unwrap().revision().to_string();
    let in_v2: Vec<String> = v2
        .policy_refs()
        .filter(|p| p.revision() == r1_rev)
        .map(|p| p.id().to_string())
        .collect();
    assert_eq!(in_v2, ["policy_4"], "R1 moved from policy_0 to policy_4");
}

// ─── update guards ───────────────────────────────────────────────────

/// A temporal engine that keeps no state and cannot be updated (the trait's
/// default), optionally failing every `prepare` after the first.
struct Frozen {
    prepared: usize,
    fail_after_first: bool,
}

impl TemporalEngine for Frozen {
    fn prepare(
        &mut self,
        _: &[TemporalField],
        _: &dogwood_language::cedar::Schema,
        _: &[dogwood_language::EventSignature],
    ) -> Result<(), Error> {
        self.prepared += 1;
        if self.fail_after_first && self.prepared > 1 {
            return Err(Error::Leaf {
                id: "frozen".to_string(),
                message: "cannot re-prepare".to_string(),
            });
        }
        Ok(())
    }
    fn observe(&mut self, _: &Event) {}
    fn evaluate(&mut self) -> Result<TemporalBindings, String> {
        Ok(TemporalBindings::new())
    }
}

/// `Frozen`, but claiming update support, to exercise a failing re-prepare.
struct Flaky(Frozen);

impl TemporalEngine for Flaky {
    fn prepare(
        &mut self,
        l: &[TemporalField],
        s: &dogwood_language::cedar::Schema,
        e: &[dogwood_language::EventSignature],
    ) -> Result<(), Error> {
        self.0.prepare(l, s, e)
    }
    fn observe(&mut self, e: &Event) {
        self.0.observe(e)
    }
    fn evaluate(&mut self) -> Result<TemporalBindings, String> {
        self.0.evaluate()
    }
    fn supports_policy_update(&self) -> bool {
        true
    }
}

#[test]
fn updates_need_engines_that_support_them() {
    let mut authz = Authorizer::builder(lower_annotated(R3_DENY_SECRET))
        .temporal_engine(Frozen {
            prepared: 0,
            fail_after_first: false,
        })
        .build()
        .unwrap();
    let err = authz
        .update_policies(lower_annotated(R3_DENY_CLASSIFIED))
        .unwrap_err();
    assert!(
        matches!(err, Error::PolicyUpdateUnsupported("temporal")),
        "{err:?}"
    );
    // Unchanged: still V1, generation 0, still deciding.
    let r = authz.is_authorized(&event("Read", 0, "secret")).unwrap();
    assert_eq!(ids(&r), set(&["deny-secret-read"]));
    assert_eq!(r.policy_set().unwrap().generation(), 0);

    // A policy engine that does not support updates must be replaced.
    let mut authz = Authorizer::builder(lower_annotated(R1_READ_AFTER_LOGIN))
        .policy_engine(NamesId("read-after-login"))
        .build()
        .unwrap();
    let err = authz
        .update_policies(lower_annotated(R2_WRITE_AFTER_LOGIN))
        .unwrap_err();
    assert!(
        matches!(err, Error::PolicyUpdateUnsupported("policy")),
        "{err:?}"
    );
    authz
        .update_policies_with_engine(
            lower_annotated(R2_WRITE_AFTER_LOGIN),
            NamesId("write-after-login"),
        )
        .expect("a replaced policy engine needs no update support");
    let r = authz.is_authorized(&event("Write", 0, "x")).unwrap();
    assert_eq!(ids(&r), set(&["write-after-login"]));
    assert_eq!(r.policy_set().unwrap().generation(), 1);
}

#[test]
fn a_failed_update_fails_closed_until_an_update_succeeds() {
    let mut authz = Authorizer::builder(lower_annotated(R3_DENY_SECRET))
        .temporal_engine(Flaky(Frozen {
            prepared: 0,
            fail_after_first: true,
        }))
        .build()
        .unwrap();
    assert!(authz.update_policies(lower_annotated(R0_OPS_READ)).is_err());
    let r = authz.is_authorized(&event("Read", 0, "ops")).unwrap();
    assert_eq!(r.decision(), Decision::Deny);
    assert_eq!(r.diagnostics().determining().count(), 0);
    assert!(
        r.diagnostics()
            .errors()
            .any(|e| e.contains("failed policy update")),
        "{:?}",
        r.diagnostics()
    );
}

#[test]
fn the_builder_sets_the_starting_generation() {
    let mut authz = Authorizer::builder(lower_annotated(R0_OPS_READ))
        .generation(7)
        .build()
        .unwrap();
    assert_eq!(authz.policy_set_version().generation(), 7);
    authz
        .update_policies(lower_annotated(R6_AUDIT_WRITE))
        .unwrap();
    let v = authz.policy_set_version();
    assert_eq!(v.generation(), 8);
    assert_eq!(v.hash(), lower_annotated(R6_AUDIT_WRITE).version_hash());
}

#[test]
fn updates_keep_partitioning() {
    // The default event schema has a universal pin, so partitioning is on.
    let mut authz = Authorizer::builder(lower_annotated(&v1()))
        .partition_temporal()
        .build()
        .unwrap();
    authz.is_authorized(&event("Login", 0, "x"));
    authz
        .update_policies(lower_annotated(&v2()))
        .expect("same keys");
    let r = authz.is_authorized(&event("Read", 10, "ops")).unwrap();
    assert_eq!(ids(&r), set(&["ops-read", "read-after-login"]));

    // An unpinned schema has no partition keys: switching would re-key history.
    let unpinned_service = ServiceSchema::builder()
        .event_schema_str(dogwood_language::UNPINNED_EVENT_SCHEMA)
        .build()
        .unwrap();
    let unpinned = ParsedPolicySet::parse(&v1(), &unpinned_service)
        .unwrap()
        .with_ids(IdSource::Annotation)
        .unwrap()
        .lower(&policy_schema())
        .unwrap();
    let err = authz.update_policies(unpinned).unwrap_err();
    assert!(matches!(err, Error::PartitionKeysChanged), "{err:?}");
}

// ─── validation ──────────────────────────────────────────────────────

#[test]
fn validation_locates_findings_under_stable_ids() {
    use dogwood_language::{ValidationError, Validator};
    // The second rule compares a String to a Long: Cedar's validator rejects
    // it, and the finding must still point at that rule's `.dw` text.
    let source = format!(
        "{R1_READ_AFTER_LOGIN}\n@id(\"bad-compare\")\npermit (principal, action == Drupe::Action::\"Read\", resource)\nwhen {{ context.input.doc == 3 }};\n"
    );
    let positional = Validator::new()
        .validate(&LoweredPolicySet::from_str(&source, &service(), &policy_schema()).unwrap());
    let stable = Validator::new().validate(&lower_annotated(&source));
    let spans = |r: &dogwood_language::ValidationResult| -> Vec<(usize, usize)> {
        r.validation_errors()
            .map(|e| match e {
                ValidationError::Cedar { span, .. } | ValidationError::Extension { span, .. } => {
                    (span.offset(), span.len())
                }
                _ => (0, 0),
            })
            .collect()
    };
    assert!(!stable.validation_passed());
    assert_eq!(spans(&stable), spans(&positional));
    let offset = source.find("@id(\"bad-compare\")").unwrap();
    assert!(
        spans(&stable).iter().all(|&(at, _)| at >= offset),
        "the finding points into the second rule: {:?}",
        spans(&stable)
    );
}

// ─── provider leaves ─────────────────────────────────────────────────

#[test]
fn revisions_cover_provider_leaves_and_ignore_their_positions() {
    use dogwood_language::ProviderDeclarations;
    const PROVIDERS: &str = r#"
{
  "availableProviders": {
    "Docs::Label": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": { "paramType": "string" },
      "implementation": { "kind": "rhai", "script": "fn evaluate(doc) { \"public\" }" }
    }
  }
}
"#;
    let service = ServiceSchema::builder()
        .providers(ProviderDeclarations::from_json(PROVIDERS).expect("providers parse"))
        .build()
        .expect("service builds");
    let rule = r#"
@id("public-read")
permit (principal, action == Drupe::Action::"Read", resource)
when { Docs::Label(context.input.doc) == "public" };
"#;
    let lower = |src: &str| {
        ParsedPolicySet::parse(src, &service)
            .unwrap()
            .with_ids(IdSource::Annotation)
            .unwrap()
            .lower(&policy_schema())
            .unwrap()
    };
    let alone = lower(rule);
    // Behind two other rules, the provider field is `policy_2_p_0`, not
    // `policy_0_p_0`; the revision must not notice.
    let moved = lower(&format!("{R0_OPS_READ}{R3_DENY_SECRET}{rule}"));
    assert_ne!(
        alone.provider_fields().next().unwrap().id,
        moved.provider_fields().next().unwrap().id
    );
    assert_eq!(
        revision(&alone, "public-read"),
        revision(&moved, "public-read")
    );
    // A different argument is a different rule.
    let edited = lower(&rule.replace("context.input.doc", "\"fixed\""));
    assert_ne!(
        revision(&alone, "public-read"),
        revision(&edited, "public-read")
    );
    // And the decision names it.
    let mut authz = Authorizer::new(moved);
    let r = authz.is_authorized(&event("Read", 0, "x")).unwrap();
    assert_eq!(ids(&r), set(&["public-read"]));
}
