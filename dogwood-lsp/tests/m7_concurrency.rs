#![cfg(feature = "test-control")]

#[path = "support/lsp_process.rs"]
mod lsp_process;

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use dogwood_lsp::project::path_to_file_uri;
use lsp_process::LspProcess;
use serde_json::{Value, json};

const POLICY: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/policy.dw");
const ACTION_SCHEMA: &str =
    include_str!("fixtures/dogwood/m3/all-optional-valid/schema.cedarschema");
const EVENT_SCHEMA: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/event.dwschema");
const PROVIDERS: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/providers.json");
const MACROS: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/macros.dw");
const SIMPLE_POLICY: &str = "permit(principal, action, resource);";
const EDITED_POLICY: &str = "forbid(principal,action,resource);";
const PUBLISH_DIAGNOSTICS: &str = "textDocument/publishDiagnostics";
const TEST_CONTROL: &str = "dogwood-lsp/testControl";
const TEST_BARRIER: &str = "dogwood/testBarrier";
const TEST_REACHED: &str = "dogwood-lsp/testReached";
const TEST_WATCH_OBSERVED: &str = "dogwood-lsp/testWatchObserved";
const LARGE_SOURCE_PADDING: usize = 64 * 1024;
const PARSER_BACKED_SIMPLE_TOKENS: &[u32] = &[
    0, 0, 6, 12, 0, 0, 6, 1, 17, 0, 0, 1, 9, 5, 0, 0, 9, 1, 17, 0, 0, 2, 6, 5, 0, 0, 6, 1, 17, 0,
    0, 2, 8, 5, 0, 0, 8, 1, 17, 0, 0, 1, 1, 17, 0,
];
const PARSER_BACKED_EDITED_TOKENS: &[u32] = &[
    0, 0, 6, 12, 0, 0, 6, 1, 17, 0, 0, 1, 9, 5, 0, 0, 9, 1, 17, 0, 0, 1, 6, 5, 0, 0, 6, 1, 17, 0,
    0, 1, 8, 5, 0, 0, 8, 1, 17, 0, 0, 1, 1, 17, 0,
];
const LEXICAL_SIMPLE_TOKENS: &[u32] = &[
    0, 0, 6, 12, 0, 0, 6, 1, 17, 0, 0, 1, 9, 12, 0, 0, 9, 1, 17, 0, 0, 2, 6, 12, 0, 0, 6, 1, 17, 0,
    0, 2, 8, 12, 0, 0, 8, 1, 17, 0, 0, 1, 1, 17, 0,
];

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn all_optional() -> Self {
        let workspace = Self::empty("bundle");
        workspace.write("actions.cedarschema", ACTION_SCHEMA);
        workspace.write("events.dwschema", EVENT_SCHEMA);
        workspace.write("providers.json", PROVIDERS);
        workspace.write("macros.dw", MACROS);
        workspace.write("policy.dw", POLICY);
        workspace
    }

    fn simple() -> Self {
        let workspace = Self::empty("simple");
        workspace.write("actions.cedarschema", ACTION_SCHEMA);
        workspace.write("policy.dw", SIMPLE_POLICY);
        workspace
    }

    fn empty(label: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "dogwood-lsp-m7-{label}-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).unwrap();
        Self { root }
    }

    fn write(&self, relative: &str, source: &str) {
        let path = self.root.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, source).unwrap();
    }

    fn uri(&self, relative: &str) -> String {
        uri(&self.root.join(relative))
    }

    fn root_uri(&self) -> String {
        uri(&self.root)
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

struct FanoutWorkspace {
    workspace: Workspace,
    policy_uris: Vec<String>,
    action_schema: String,
    shared_source_bytes: usize,
}

impl FanoutWorkspace {
    fn new(policy_count: usize) -> Self {
        let workspace = Workspace::empty("fanout");
        let action_schema = padded(ACTION_SCHEMA);
        let event_schema = padded(EVENT_SCHEMA);
        let providers = padded(PROVIDERS);
        let macros = padded(MACROS);
        workspace.write("actions.cedarschema", &action_schema);
        workspace.write("events.dwschema", &event_schema);
        workspace.write("providers.json", &providers);
        workspace.write("macros.dw", &macros);
        let policy_uris = (0..policy_count)
            .map(|index| {
                let relative = format!("policy-{index:02}.dw");
                workspace.write(&relative, POLICY);
                workspace.uri(&relative)
            })
            .collect();
        Self {
            workspace,
            policy_uris,
            shared_source_bytes: action_schema.len()
                + event_schema.len()
                + providers.len()
                + macros.len(),
            action_schema,
        }
    }

    fn open_policies(&self, server: &mut LspProcess) {
        for policy_uri in &self.policy_uris {
            open(server, policy_uri, "dogwood", 1, POLICY);
        }
    }
}

fn padded(source: &str) -> String {
    format!("{source}\n{}", " ".repeat(LARGE_SOURCE_PADDING))
}

#[test]
fn dependency_fanout_bounds_pending_snapshots_and_shares_large_disk_sources() {
    const POLICY_COUNT: usize = 9;
    let fanout = FanoutWorkspace::new(POLICY_COUNT);
    let action_uri = fanout.workspace.uri("actions.cedarschema");
    let mut server = controlled_server(&fanout.workspace);
    fanout.open_policies(&mut server);
    barrier(&mut server, 1);
    expect_policy_publications(&mut server, &fanout.policy_uris, 1, true);

    let initial = snapshot_stats(&mut server, 2);
    assert_eq!(initial["completedPolicySnapshots"], POLICY_COUNT);
    assert_eq!(initial["sharedDiskSources"], 4);
    assert_eq!(initial["sharedDiskSourceBytes"], fanout.shared_source_bytes);
    assert_eq!(initial["diskSourceReads"], 4);

    pause_next(&mut server, 3, "validation");
    let changed_action = format!("{}\n ", fanout.action_schema);
    fanout
        .workspace
        .write("actions.cedarschema", &changed_action);
    watched(&mut server, &action_uri, 2);
    let validation = reached(&mut server, "validation");

    let saturated = snapshot_stats(&mut server, 4);
    assert_eq!(saturated["retentionLimit"], 4);
    assert_eq!(saturated["queuedValidationSnapshots"], 4);
    assert_eq!(saturated["activeValidationSnapshots"], 1);
    assert_eq!(saturated["dirtyPolicies"], POLICY_COUNT - 5);
    assert_eq!(saturated["completedPolicySnapshots"], 0);
    assert_eq!(saturated["sharedDiskSources"], 4);
    assert_eq!(
        saturated["sharedDiskSourceBytes"],
        fanout.shared_source_bytes + 2
    );
    assert_eq!(saturated["diskSourceReads"], 5);

    server.send_request(5, "dogwood/responsive", Some(json!({})));
    assert_error(&mut server, 5, -32601);
    release(&mut server, 6, validation);
    barrier(&mut server, 7);
    expect_policy_publications(&mut server, &fanout.policy_uris, 1, true);

    let complete = snapshot_stats(&mut server, 8);
    assert_eq!(complete["queuedValidationSnapshots"], 0);
    assert_eq!(complete["activeValidationSnapshots"], 0);
    assert_eq!(complete["dirtyPolicies"], 0);
    assert_eq!(complete["completedPolicySnapshots"], POLICY_COUNT);
    assert_eq!(complete["diskSourceReads"], 5);
    server.assert_no_queued_server_messages();
    shutdown(server, 9);
}

#[test]
fn dependency_supersession_while_saturated_publishes_only_the_newest_fanout() {
    const POLICY_COUNT: usize = 9;
    let fanout = FanoutWorkspace::new(POLICY_COUNT);
    let action_uri = fanout.workspace.uri("actions.cedarschema");
    let mut server = controlled_server(&fanout.workspace);
    fanout.open_policies(&mut server);
    barrier(&mut server, 1);
    expect_policy_publications(&mut server, &fanout.policy_uris, 1, true);

    pause_next(&mut server, 2, "validation");
    fanout.workspace.write("actions.cedarschema", "{");
    watched(&mut server, &action_uri, 2);
    reached(&mut server, "validation");

    let invalid = snapshot_stats(&mut server, 3);
    assert_eq!(invalid["queuedValidationSnapshots"], 4);
    assert_eq!(invalid["dirtyPolicies"], POLICY_COUNT - 5);
    assert_eq!(invalid["diskSourceReads"], 5);

    let newest_action = format!("{}\n  ", fanout.action_schema);
    fanout
        .workspace
        .write("actions.cedarschema", &newest_action);
    watched(&mut server, &action_uri, 2);
    let superseded = snapshot_stats(&mut server, 4);
    assert!(
        superseded["queuedValidationSnapshots"]
            .as_u64()
            .is_some_and(|count| count <= 4)
    );
    assert_eq!(superseded["sharedDiskSources"], 4);
    assert_eq!(superseded["diskSourceReads"], 6);

    barrier(&mut server, 5);
    expect_policy_publications(&mut server, &fanout.policy_uris, 1, true);
    let complete = snapshot_stats(&mut server, 6);
    assert_eq!(complete["queuedValidationSnapshots"], 0);
    assert_eq!(complete["activeValidationSnapshots"], 0);
    assert_eq!(complete["dirtyPolicies"], 0);
    assert_eq!(complete["completedPolicySnapshots"], POLICY_COUNT);
    assert_eq!(complete["diskSourceReads"], 6);
    server.assert_no_queued_server_messages();
    shutdown(server, 7);
}

#[test]
fn close_cancels_validation_and_releases_policy_and_shared_snapshots() {
    let fanout = FanoutWorkspace::new(1);
    let policy_uri = &fanout.policy_uris[0];
    let action_uri = fanout.workspace.uri("actions.cedarschema");
    let mut server = controlled_server(&fanout.workspace);
    fanout.open_policies(&mut server);
    barrier(&mut server, 1);
    expect_policy_publications(&mut server, &fanout.policy_uris, 1, true);

    let initial = snapshot_stats(&mut server, 2);
    assert_eq!(initial["completedPolicySnapshots"], 1);
    assert_eq!(initial["sharedDiskSources"], 4);

    pause_next(&mut server, 3, "validation");
    fanout.workspace.write(
        "actions.cedarschema",
        &format!("{}\n ", fanout.action_schema),
    );
    watched(&mut server, &action_uri, 2);
    reached(&mut server, "validation");
    let active = snapshot_stats(&mut server, 4);
    assert_eq!(active["activeValidationSnapshots"], 1);
    assert_eq!(active["completedPolicySnapshots"], 0);

    close(&mut server, policy_uri);
    barrier(&mut server, 5);
    expect_empty(&mut server, policy_uri, 1);
    let released = snapshot_stats(&mut server, 6);
    assert_eq!(released["queuedValidationSnapshots"], 0);
    assert_eq!(released["activeValidationSnapshots"], 0);
    assert_eq!(released["dirtyPolicies"], 0);
    assert_eq!(released["completedPolicySnapshots"], 0);
    assert_eq!(released["sharedDiskSources"], 0);
    assert_eq!(released["sharedDiskSourceBytes"], 0);
    server.assert_no_queued_server_messages();
    shutdown(server, 7);
}

#[test]
fn shutdown_releases_a_saturated_validation_fanout() {
    let fanout = FanoutWorkspace::new(9);
    let mut server = controlled_server(&fanout.workspace);
    pause_next(&mut server, 1, "validation");
    fanout.open_policies(&mut server);
    reached(&mut server, "validation");

    let saturated = snapshot_stats(&mut server, 2);
    assert_eq!(saturated["queuedValidationSnapshots"], 4);
    assert_eq!(saturated["activeValidationSnapshots"], 1);
    assert_eq!(saturated["dirtyPolicies"], 4);
    assert_eq!(saturated["sharedDiskSources"], 4);

    server.send_request(3, "shutdown", None);
    server.expect_response(3, json!({"jsonrpc": "2.0", "id": 3, "result": null}));
    let released = snapshot_stats(&mut server, 4);
    assert_eq!(released["queuedValidationSnapshots"], 0);
    assert_eq!(released["dirtyPolicies"], 0);
    assert_eq!(released["completedPolicySnapshots"], 0);
    assert_eq!(released["sharedDiskSources"], 0);
    assert_eq!(released["sharedDiskSourceBytes"], 0);
    server.send_notification("exit", None);
    server.finish(0);
}

#[test]
fn initial_semantic_request_waits_for_exact_validated_snapshot() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let mut server = controlled_server(&workspace);

    pause_next(&mut server, 1, "validation");
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    let validation = reached(&mut server, "validation");
    request_tokens(&mut server, 10, &policy_uri);
    release(&mut server, 2, validation);

    let before_validation_response = server.receive_response(10)["result"]["data"].clone();
    assert_eq!(
        before_validation_response,
        json!(PARSER_BACKED_SIMPLE_TOKENS)
    );
    expect_empty(&mut server, &policy_uri, 1);

    let after_validation = token_data(&mut server, 11, &policy_uri);
    assert_eq!(after_validation, before_validation_response);
    barrier(&mut server, 3);
    server.assert_no_queued_server_messages();

    shutdown(server, 4);
}

#[test]
fn policy_edit_cancels_semantic_request_waiting_for_initial_validation() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let mut server = controlled_server(&workspace);

    pause_next(&mut server, 1, "validation");
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    reached(&mut server, "validation");
    request_tokens(&mut server, 10, &policy_uri);

    change(&mut server, &policy_uri, 2, EDITED_POLICY);
    assert_error(&mut server, 10, -32801);
    barrier(&mut server, 2);
    expect_empty(&mut server, &policy_uri, 2);
    let current = token_data(&mut server, 3, &policy_uri);
    assert_eq!(current, json!(PARSER_BACKED_EDITED_TOKENS));
    assert_ne!(current, json!(PARSER_BACKED_SIMPLE_TOKENS));
    server.assert_no_queued_server_messages();

    shutdown(server, 4);
}

#[test]
fn close_cancels_semantic_request_waiting_for_initial_validation() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let mut server = controlled_server(&workspace);

    pause_next(&mut server, 1, "validation");
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    reached(&mut server, "validation");
    request_tokens(&mut server, 10, &policy_uri);

    close(&mut server, &policy_uri);
    assert_error(&mut server, 10, -32801);
    barrier(&mut server, 2);
    expect_empty(&mut server, &policy_uri, 1);
    server.assert_no_queued_server_messages();

    shutdown(server, 3);
}

#[test]
fn explicit_cancellation_removes_semantic_request_waiting_for_validation() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let mut server = controlled_server(&workspace);

    pause_next(&mut server, 1, "validation");
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    let validation = reached(&mut server, "validation");
    request_tokens(&mut server, 10, &policy_uri);
    cancel(&mut server, 10);
    assert_error(&mut server, 10, -32800);

    release(&mut server, 2, validation);
    barrier(&mut server, 3);
    expect_empty(&mut server, &policy_uri, 1);
    server.assert_no_queued_server_messages();

    shutdown(server, 4);
}

#[test]
fn dependency_change_cancels_waiting_request_and_never_returns_stale_bundle() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let action_uri = workspace.uri("actions.cedarschema");
    let mut server = controlled_server(&workspace);

    pause_next(&mut server, 1, "validation");
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    reached(&mut server, "validation");
    request_tokens(&mut server, 10, &policy_uri);

    workspace.write("actions.cedarschema", "{");
    watched(&mut server, &action_uri, 2);
    assert_error(&mut server, 10, -32801);
    barrier(&mut server, 2);
    expect_nonempty(&mut server, &policy_uri, 1);
    assert_eq!(
        token_data(&mut server, 3, &policy_uri),
        json!(LEXICAL_SIMPLE_TOKENS)
    );
    server.assert_no_queued_server_messages();

    shutdown(server, 4);
}

#[test]
fn initial_invalid_bundle_waits_then_returns_complete_exact_lexical_fallback() {
    let workspace = Workspace::simple();
    workspace.write("actions.cedarschema", "{");
    let policy_uri = workspace.uri("policy.dw");
    let mut server = controlled_server(&workspace);

    pause_next(&mut server, 1, "validation");
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    let validation = reached(&mut server, "validation");
    request_tokens(&mut server, 10, &policy_uri);
    release(&mut server, 2, validation);

    let pending = server.receive_response(10)["result"]["data"].clone();
    assert_eq!(pending, json!(LEXICAL_SIMPLE_TOKENS));
    expect_nonempty(&mut server, &policy_uri, 1);
    assert_eq!(token_data(&mut server, 11, &policy_uri), pending);
    barrier(&mut server, 3);
    server.assert_no_queued_server_messages();

    shutdown(server, 4);
}

#[test]
fn semantic_edits_and_explicit_cancellation_are_single_response_and_responsive() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let mut server = controlled_server(&workspace);
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &policy_uri, 1);

    pause_next(&mut server, 2, "semantic");
    request_tokens(&mut server, 10, &policy_uri);
    reached(&mut server, "semantic");

    server.send_request(3, "dogwood/responsive", Some(json!({})));
    assert_error(&mut server, 3, -32601);

    change(
        &mut server,
        &policy_uri,
        2,
        "forbid(principal, action, resource);",
    );
    assert_error(&mut server, 10, -32801);
    barrier(&mut server, 4);
    expect_empty(&mut server, &policy_uri, 2);
    assert!(
        token_data(&mut server, 5, &policy_uri)
            .as_array()
            .is_some_and(|tokens| !tokens.is_empty())
    );

    pause_next(&mut server, 6, "semantic");
    request_tokens(&mut server, 20, &policy_uri);
    reached(&mut server, "semantic");
    request_tokens(&mut server, 21, &policy_uri);
    cancel(&mut server, 21);
    assert_error(&mut server, 21, -32800);
    cancel(&mut server, 20);
    assert_error(&mut server, 20, -32800);
    barrier(&mut server, 7);
    server.assert_no_queued_server_messages();

    shutdown(server, 8);
}

#[test]
fn close_cancels_running_paused_semantics_and_releases_the_barrier() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let mut server = controlled_server(&workspace);
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &policy_uri, 1);

    pause_next(&mut server, 2, "semantic");
    request_tokens(&mut server, 10, &policy_uri);
    let semantic_task = reached(&mut server, "semantic");
    close(&mut server, &policy_uri);
    assert_error(&mut server, 10, -32801);
    barrier(&mut server, 3);
    expect_empty(&mut server, &policy_uri, 1);

    let cancelled = snapshot_stats(&mut server, 4);
    assert_eq!(cancelled["pendingSemanticRequests"], json!([]));
    assert_eq!(
        cancelled["semanticTerminalOutcomes"],
        json!([{
            "task": semantic_task,
            "uri": policy_uri,
            "revision": 1,
            "outcome": "cancelled"
        }])
    );
    server.assert_no_queued_server_messages();
    shutdown(server, 5);
}

#[test]
fn every_dependency_edit_suppresses_paused_old_bundle_diagnostics() {
    let workspace = Workspace::all_optional();
    let policy_uri = workspace.uri("policy.dw");
    let action_uri = workspace.uri("actions.cedarschema");
    let event_uri = workspace.uri("events.dwschema");
    let providers_uri = workspace.uri("providers.json");
    let macros_uri = workspace.uri("macros.dw");
    let mut server = controlled_server(&workspace);

    open(&mut server, &action_uri, "dogwood", 1, ACTION_SCHEMA);
    open(
        &mut server,
        &event_uri,
        "dogwood-event-schema",
        1,
        EVENT_SCHEMA,
    );
    open(&mut server, &providers_uri, "dogwood", 1, PROVIDERS);
    barrier(&mut server, 1);
    expect_empty(&mut server, &event_uri, 1);

    open(&mut server, &policy_uri, "dogwood", 1, POLICY);
    barrier(&mut server, 2);
    expect_empty(&mut server, &policy_uri, 1);
    open(&mut server, &macros_uri, "dogwood", 1, MACROS);
    barrier(&mut server, 3);
    expect_empty(&mut server, &policy_uri, 1);

    let cases = [
        (&action_uri, "{", ACTION_SCHEMA, false),
        (
            &event_uri,
            "decision event <A>::attempt {",
            EVENT_SCHEMA,
            true,
        ),
        (&providers_uri, "{", PROVIDERS, false),
        (&macros_uri, "def cedar broken(", MACROS, false),
    ];
    let mut request_id = 10i64;
    let mut policy_version = 1i32;
    for (dependency_uri, invalid, repaired, schema_publication) in cases {
        policy_version += 1;
        pause_next(&mut server, request_id, "validation");
        request_id += 1;
        change(&mut server, &policy_uri, policy_version, POLICY);
        reached(&mut server, "validation");

        change(&mut server, dependency_uri, 2, invalid);
        barrier(&mut server, request_id);
        request_id += 1;
        if schema_publication {
            expect_nonempty(&mut server, dependency_uri, 2);
        }
        expect_nonempty(&mut server, &policy_uri, policy_version);
        server.assert_no_queued_server_messages();

        change(&mut server, dependency_uri, 3, repaired);
        barrier(&mut server, request_id);
        request_id += 1;
        if schema_publication {
            expect_empty(&mut server, dependency_uri, 3);
        }
        expect_empty(&mut server, &policy_uri, policy_version);
        server.assert_no_queued_server_messages();
    }

    shutdown(server, request_id);
}

#[test]
fn resolution_change_while_validation_is_paused_publishes_only_new_bundle() {
    let workspace = Workspace::simple();
    workspace.write("nested/policy.dw", SIMPLE_POLICY);
    let policy_uri = workspace.uri("nested/policy.dw");
    let nested_schema_uri = workspace.uri("nested/actions.cedarschema");
    let mut server = controlled_server(&workspace);

    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &policy_uri, 1);

    pause_next(&mut server, 2, "validation");
    change(&mut server, &policy_uri, 2, SIMPLE_POLICY);
    reached(&mut server, "validation");
    workspace.write("nested/actions.cedarschema", "{");
    watched(&mut server, &nested_schema_uri, 1);
    barrier(&mut server, 3);
    expect_nonempty(&mut server, &policy_uri, 2);
    server.assert_no_queued_server_messages();

    fs::remove_file(workspace.root.join("nested/actions.cedarschema")).unwrap();
    watched(&mut server, &nested_schema_uri, 3);
    barrier(&mut server, 4);
    expect_empty(&mut server, &policy_uri, 2);

    shutdown(server, 5);
}

#[test]
fn close_cancels_paused_validation_and_reopen_has_no_stale_edges() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let action_uri = workspace.uri("actions.cedarschema");
    let mut server = controlled_server(&workspace);
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &policy_uri, 1);

    pause_next(&mut server, 2, "validation");
    change(&mut server, &policy_uri, 2, SIMPLE_POLICY);
    reached(&mut server, "validation");
    close(&mut server, &policy_uri);
    barrier(&mut server, 3);
    expect_empty(&mut server, &policy_uri, 2);
    server.assert_no_queued_server_messages();

    watched(&mut server, &action_uri, 2);
    barrier(&mut server, 4);
    server.assert_no_queued_notifications();

    open(&mut server, &policy_uri, "dogwood", 3, SIMPLE_POLICY);
    barrier(&mut server, 5);
    expect_empty(&mut server, &policy_uri, 3);
    shutdown(server, 6);
}

#[test]
fn shutdown_cleans_running_queued_and_cancelled_semantic_work() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let mut server = controlled_server(&workspace);
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &policy_uri, 1);

    pause_next(&mut server, 2, "semantic");
    request_tokens(&mut server, 10, &policy_uri);
    reached(&mut server, "semantic");
    request_tokens(&mut server, 11, &policy_uri);
    cancel(&mut server, 11);
    assert_error(&mut server, 11, -32800);
    request_tokens(&mut server, 12, &policy_uri);

    server.send_request(3, "shutdown", None);
    server.expect_response(3, json!({"jsonrpc": "2.0", "id": 3, "result": null}));
    assert_error(&mut server, 12, -32800);
    assert_error(&mut server, 10, -32800);
    server.send_notification("exit", None);
    server.finish(0);
}

#[test]
fn saturated_diagnostic_queue_retries_latest_schema_and_policy_state() {
    let workspace = Workspace::all_optional();
    let policy_uri = workspace.uri("policy.dw");
    let event_uri = workspace.uri("events.dwschema");
    let mut server = controlled_server(&workspace);

    open(
        &mut server,
        &event_uri,
        "dogwood-event-schema",
        1,
        EVENT_SCHEMA,
    );
    open(&mut server, &policy_uri, "dogwood", 1, POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &event_uri, 1);
    expect_empty(&mut server, &policy_uri, 1);

    pause_next(&mut server, 2, "validation");
    change(&mut server, &policy_uri, 2, POLICY);
    reached(&mut server, "validation");

    let invalid_schema = "decision event <A>::attempt {";
    let queued_schema_uris: Vec<_> = (0..4)
        .map(|index| workspace.uri(&format!("queued-{index}.dwschema")))
        .collect();
    for uri in &queued_schema_uris {
        open(&mut server, uri, "dogwood-event-schema", 1, invalid_schema);
    }

    change(&mut server, &event_uri, 2, invalid_schema);
    barrier(&mut server, 3);
    for uri in &queued_schema_uris {
        expect_nonempty(&mut server, uri, 1);
    }
    expect_nonempty(&mut server, &event_uri, 2);
    expect_nonempty(&mut server, &policy_uri, 2);
    server.assert_no_queued_server_messages();

    shutdown(server, 4);
}

#[test]
fn semantic_queue_rejection_and_diagnostic_eviction_are_single_response() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let scratch_uri = workspace.uri("scratch.dwschema");
    let mut server = controlled_server(&workspace);
    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &policy_uri, 1);

    pause_next(&mut server, 2, "semantic");
    request_tokens_id(&mut server, json!("running"), &policy_uri);
    reached(&mut server, "semantic");
    for id in 11..=14 {
        request_tokens(&mut server, id, &policy_uri);
    }

    request_tokens(&mut server, 15, &policy_uri);
    assert_error(&mut server, 15, -32802);

    server.send_notification("$/cancelRequest", Some(json!({"id": true})));
    server.send_request(16, "dogwood/responsive", Some(json!({})));
    assert_error(&mut server, 16, -32601);

    open(
        &mut server,
        &scratch_uri,
        "dogwood-event-schema",
        1,
        "decision event <A>::attempt {",
    );
    assert_error(&mut server, 11, -32802);

    for id in 12..=14 {
        cancel(&mut server, id);
        assert_error(&mut server, i64::from(id), -32800);
    }
    server.send_notification("$/cancelRequest", Some(json!({"id": "running"})));
    assert_error_id(&mut server, json!("running"), -32800);

    barrier(&mut server, 17);
    expect_nonempty(&mut server, &scratch_uri, 1);
    server.assert_no_queued_server_messages();

    shutdown(server, 18);
}

#[test]
fn ancestor_action_schema_change_revalidates_only_policies_resolving_to_it() {
    let workspace = Workspace::simple();
    workspace.write("nested/actions.cedarschema", ACTION_SCHEMA);
    workspace.write("nested/policy.dw", SIMPLE_POLICY);
    let root_action_uri = workspace.uri("actions.cedarschema");
    let nested_action_uri = workspace.uri("nested/actions.cedarschema");
    let root_policy_uri = workspace.uri("policy.dw");
    let nested_policy_uri = workspace.uri("nested/policy.dw");
    let mut server = controlled_server(&workspace);

    open(&mut server, &root_action_uri, "dogwood", 1, ACTION_SCHEMA);
    open(&mut server, &nested_action_uri, "dogwood", 1, ACTION_SCHEMA);
    open(&mut server, &root_policy_uri, "dogwood", 1, SIMPLE_POLICY);
    open(&mut server, &nested_policy_uri, "dogwood", 1, SIMPLE_POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &root_policy_uri, 1);
    expect_empty(&mut server, &nested_policy_uri, 1);

    change(&mut server, &root_action_uri, 2, "{");
    barrier(&mut server, 2);
    expect_nonempty(&mut server, &root_policy_uri, 1);
    server.assert_no_queued_server_messages();

    shutdown(server, 3);
}

#[test]
fn test_control_observes_policy_watcher_and_semantic_lifecycle() {
    let workspace = Workspace::simple();
    let policy_uri = workspace.uri("policy.dw");
    let action_uri = workspace.uri("actions.cedarschema");
    let policy_path = workspace.root.join("policy.dw");
    let action_path = workspace.root.join("actions.cedarschema");
    let mut server = controlled_server(&workspace);
    server.send_request(
        9,
        TEST_CONTROL,
        Some(json!({"command": "enableWatchNotifications"})),
    );
    server.expect_response(9, json!({"jsonrpc": "2.0", "id": 9, "result": null}));

    open(&mut server, &policy_uri, "dogwood", 1, SIMPLE_POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &policy_uri, 1);
    let initial = snapshot_stats(&mut server, 2);
    assert_eq!(initial["watchRegistration"], "unsupported");
    assert_eq!(initial["watchEvents"], json!([]));
    assert_eq!(initial["policies"].as_array().unwrap().len(), 1);
    assert_eq!(
        initial["policies"][0]["path"],
        json!(policy_path.display().to_string())
    );
    assert_eq!(initial["policies"][0]["validationPending"], false);
    assert_eq!(initial["policies"][0]["parserBacked"], true);
    assert_eq!(
        initial["policies"][0]["identity"]["actionSchema"]["path"],
        json!(action_path.display().to_string())
    );
    let initial_generation = initial["policies"][0]["generation"].as_u64().unwrap();

    pause_next(&mut server, 3, "semantic");
    request_tokens(&mut server, 30, &policy_uri);
    let semantic_task = reached(&mut server, "semantic");
    let pending = snapshot_stats(&mut server, 4);
    assert_eq!(
        pending["pendingSemanticRequests"],
        json!([{
            "task": semantic_task,
            "uri": policy_uri,
            "revision": 1,
            "state": "running"
        }])
    );
    cancel(&mut server, 30);
    assert_error(&mut server, 30, -32800);
    let cancelled = snapshot_stats(&mut server, 5);
    assert_eq!(cancelled["pendingSemanticRequests"], json!([]));
    assert_eq!(
        cancelled["semanticTerminalOutcomes"],
        json!([{
            "task": semantic_task,
            "uri": policy_uri,
            "revision": 1,
            "outcome": "cancelled"
        }])
    );

    workspace.write("actions.cedarschema", &format!("{ACTION_SCHEMA}\n"));
    watched(&mut server, &action_uri, 2);
    server.expect_notification(
        TEST_WATCH_OBSERVED,
        json!({
            "sequence": 1,
            "uri": action_uri,
            "path": action_path.to_string_lossy(),
            "kind": "changed"
        }),
    );
    barrier(&mut server, 6);
    expect_empty(&mut server, &policy_uri, 1);
    let changed = snapshot_stats(&mut server, 7);
    assert_eq!(
        changed["watchEvents"],
        json!([{
            "sequence": 1,
            "uri": action_uri,
            "path": action_path.to_string_lossy(),
            "kind": "changed"
        }])
    );
    assert!(
        changed["policies"][0]["generation"]
            .as_u64()
            .is_some_and(|generation| generation > initial_generation)
    );
    assert_eq!(changed["policies"][0]["validationPending"], false);
    assert_eq!(changed["policies"][0]["parserBacked"], true);

    shutdown(server, 8);
}

#[test]
fn test_control_and_barrier_are_unavailable_without_the_explicit_environment_switch() {
    let mut server = LspProcess::spawn();
    server.send_request(0, "initialize", Some(json!({"capabilities": {}})));
    server.receive_response(0);
    server.send_notification("initialized", Some(json!({})));
    server.send_notification(
        "workspace/didChangeWatchedFiles",
        Some(json!({
            "changes": [{
                "uri": "file:///workspace/actions.cedarschema",
                "type": 2
            }]
        })),
    );
    server.send_request(
        1,
        TEST_CONTROL,
        Some(json!({"command": "pauseNext", "point": "semantic"})),
    );
    assert_error(&mut server, 1, -32601);
    server.assert_no_queued_notifications();
    server.send_request(2, TEST_BARRIER, Some(json!({})));
    assert_error(&mut server, 2, -32601);
    server.assert_no_queued_notifications();
    shutdown(server, 3);
}

fn controlled_server(workspace: &Workspace) -> LspProcess {
    let mut server = LspProcess::spawn_with_test_control();
    server.send_request(
        0,
        "initialize",
        Some(json!({"capabilities": {}, "rootUri": workspace.root_uri()})),
    );
    server.receive_response(0);
    server.send_notification("initialized", Some(json!({})));
    server
}

fn open(server: &mut LspProcess, uri: &str, language_id: &str, version: i32, text: &str) {
    server.send_notification(
        "textDocument/didOpen",
        Some(json!({
            "textDocument": {
                "uri": uri,
                "languageId": language_id,
                "version": version,
                "text": text
            }
        })),
    );
}

fn change(server: &mut LspProcess, uri: &str, version: i32, text: &str) {
    server.send_notification(
        "textDocument/didChange",
        Some(json!({
            "textDocument": {"uri": uri, "version": version},
            "contentChanges": [{"text": text}]
        })),
    );
}

fn close(server: &mut LspProcess, uri: &str) {
    server.send_notification(
        "textDocument/didClose",
        Some(json!({"textDocument": {"uri": uri}})),
    );
}

fn watched(server: &mut LspProcess, uri: &str, typ: i32) {
    server.send_notification(
        "workspace/didChangeWatchedFiles",
        Some(json!({"changes": [{"uri": uri, "type": typ}]})),
    );
}

fn pause_next(server: &mut LspProcess, id: i64, point: &str) {
    server.send_request(
        id,
        TEST_CONTROL,
        Some(json!({"command": "pauseNext", "point": point})),
    );
    server.expect_response(id, json!({"jsonrpc": "2.0", "id": id, "result": null}));
}

fn reached(server: &mut LspProcess, point: &str) -> u64 {
    let notification = server.receive_notification(TEST_REACHED);
    assert_eq!(notification["params"]["point"], point);
    notification["params"]["task"].as_u64().unwrap()
}

fn release(server: &mut LspProcess, id: i64, task: u64) {
    server.send_request(
        id,
        TEST_CONTROL,
        Some(json!({"command": "release", "task": task})),
    );
    server.expect_response(id, json!({"jsonrpc": "2.0", "id": id, "result": null}));
}

fn snapshot_stats(server: &mut LspProcess, id: i64) -> Value {
    server.send_request(id, TEST_CONTROL, Some(json!({"command": "snapshotStats"})));
    server.receive_response(id)["result"].clone()
}

fn request_tokens(server: &mut LspProcess, id: i64, uri: &str) {
    request_tokens_id(server, Value::from(id), uri);
}

fn request_tokens_id(server: &mut LspProcess, id: Value, uri: &str) {
    server.send_request_id(
        id,
        "textDocument/semanticTokens/full",
        Some(json!({"textDocument": {"uri": uri}})),
    );
}

fn token_data(server: &mut LspProcess, id: i64, uri: &str) -> Value {
    request_tokens(server, id, uri);
    server.receive_response(id)["result"]["data"].clone()
}

fn cancel(server: &mut LspProcess, id: i32) {
    server.send_notification("$/cancelRequest", Some(json!({"id": id})));
}

fn barrier(server: &mut LspProcess, id: i64) {
    server.send_request(id, TEST_BARRIER, Some(json!({})));
    let response = server.receive_response(id);
    assert_eq!(response["error"]["code"], -32601);
}

fn expect_empty(server: &mut LspProcess, uri: &str, version: i32) {
    server.expect_notification(
        PUBLISH_DIAGNOSTICS,
        json!({"uri": uri, "version": version, "diagnostics": []}),
    );
}

fn expect_nonempty(server: &mut LspProcess, uri: &str, version: i32) {
    let notification = server.receive_notification(PUBLISH_DIAGNOSTICS);
    assert_eq!(notification["params"]["uri"], uri);
    assert_eq!(notification["params"]["version"], version);
    assert!(
        notification["params"]["diagnostics"]
            .as_array()
            .is_some_and(|diagnostics| !diagnostics.is_empty()),
        "{notification}"
    );
}

fn expect_policy_publications(
    server: &mut LspProcess,
    policy_uris: &[String],
    version: i32,
    expect_empty: bool,
) {
    let mut remaining: BTreeSet<_> = policy_uris.iter().cloned().collect();
    for _ in policy_uris {
        let notification = server.receive_notification(PUBLISH_DIAGNOSTICS);
        let params = &notification["params"];
        let uri = params["uri"]
            .as_str()
            .expect("diagnostic URI should be a string");
        assert!(
            remaining.remove(uri),
            "unexpected or duplicate policy publication: {notification}"
        );
        assert_eq!(params["version"], version);
        assert_eq!(
            params["diagnostics"]
                .as_array()
                .expect("diagnostics should be an array")
                .is_empty(),
            expect_empty,
            "{notification}"
        );
    }
    assert!(remaining.is_empty());
}

fn assert_error(server: &mut LspProcess, id: i64, code: i64) {
    let response = server.receive_response(id);
    assert_eq!(response["error"]["code"], code, "{response}");
}

fn assert_error_id(server: &mut LspProcess, id: Value, code: i64) {
    let response = server.receive_response_id(id);
    assert_eq!(response["error"]["code"], code, "{response}");
}

fn shutdown(mut server: LspProcess, id: i64) {
    server.send_request(id, "shutdown", None);
    server.expect_response(id, json!({"jsonrpc": "2.0", "id": id, "result": null}));
    server.send_notification("exit", None);
    server.finish(0);
}

fn uri(path: &Path) -> String {
    path_to_file_uri(path).unwrap().as_str().to_owned()
}
