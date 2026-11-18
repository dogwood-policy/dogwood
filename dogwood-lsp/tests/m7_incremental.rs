#![cfg(feature = "test-control")]

#[path = "support/lsp_process.rs"]
mod lsp_process;

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use dogwood_lsp::project::path_to_file_uri;
use lsp_process::LspProcess;
use serde_json::{Value, json};

const ACTION_SCHEMA: &str = include_str!("fixtures/dogwood/m3/default-valid/schema.cedarschema");
const INITIAL: &str = "// x\r\nperXXmit(principal, action, resource);trash\r\n";
const FINAL: &str = "// 😀 policy\r\npermit(principal, action, resource);\r\n";
const LONE_CR_POLICY_INITIAL: &str = "// header\rperXXmit(principal, action, resource);\r";
const LONE_CR_POLICY_FINAL: &str = "// header\rpermit(principal, action, resource);\r";
const LONE_CR_SCHEMA_INITIAL: &str = "// header\reXXvent <A>::audit {\r    ...inputs(A),\r}\r";
const LONE_CR_SCHEMA_FINAL: &str = "// header\revent <A>::audit {\r    ...inputs(A),\r}\r";
const PUBLISH_DIAGNOSTICS: &str = "textDocument/publishDiagnostics";

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "dogwood-lsp-m7-incremental-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("actions.cedarschema"), ACTION_SCHEMA).unwrap();
        Self { root }
    }

    fn uri(&self, relative: &str) -> String {
        path_to_file_uri(&self.root.join(relative))
            .unwrap()
            .as_str()
            .to_owned()
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn incremental_utf16_changes_match_equivalent_full_documents_atomically() {
    let workspace = Workspace::new();
    let root_uri = uri(&workspace.root);
    let incremental_uri = workspace.uri("incremental.dw");
    let full_uri = workspace.uri("full.dw");
    let mut server = LspProcess::spawn_with_test_control();
    initialize(&mut server, &root_uri);

    open(&mut server, &incremental_uri, "dogwood", 1, INITIAL);
    barrier(&mut server, 1);
    expect_nonempty(&mut server, &incremental_uri, 1);

    server.send_notification(
        "textDocument/didChange",
        Some(json!({
            "textDocument": {"uri": incremental_uri, "version": 2},
            "contentChanges": [
                {
                    "range": {
                        "start": {"line": 0, "character": 3},
                        "end": {"line": 0, "character": 4}
                    },
                    "rangeLength": 1,
                    "text": "😀"
                },
                {
                    "range": {
                        "start": {"line": 0, "character": 5},
                        "end": {"line": 0, "character": 5}
                    },
                    "rangeLength": 0,
                    "text": " policy"
                },
                {
                    "range": {
                        "start": {"line": 1, "character": 3},
                        "end": {"line": 1, "character": 5}
                    },
                    "rangeLength": 2,
                    "text": ""
                },
                {
                    "range": {
                        "start": {"line": 1, "character": 36},
                        "end": {"line": 2, "character": 0}
                    },
                    "rangeLength": 7,
                    "text": "\r\n"
                }
            ]
        })),
    );
    barrier(&mut server, 2);
    expect_empty(&mut server, &incremental_uri, 2);
    let incremental_tokens = request_tokens(&mut server, 3, &incremental_uri);

    open(&mut server, &full_uri, "dogwood", 1, FINAL);
    barrier(&mut server, 4);
    expect_empty(&mut server, &full_uri, 1);
    assert_eq!(
        request_tokens(&mut server, 5, &full_uri),
        incremental_tokens
    );

    server.send_notification(
        "textDocument/didChange",
        Some(json!({
            "textDocument": {"uri": incremental_uri, "version": 3},
            "contentChanges": [
                {
                    "range": {
                        "start": {"line": 0, "character": 0},
                        "end": {"line": 0, "character": 0}
                    },
                    "text": "partial "
                },
                {
                    "range": {
                        "start": {"line": 0, "character": 12},
                        "end": {"line": 0, "character": 13}
                    },
                    "text": "invalid-surrogate-split"
                }
            ]
        })),
    );
    barrier(&mut server, 6);
    server.assert_no_queued_notifications();
    assert_eq!(
        request_tokens(&mut server, 7, &incremental_uri),
        incremental_tokens,
        "a later invalid range must roll back every earlier change in the notification"
    );

    server.send_notification(
        "textDocument/didChange",
        Some(json!({
            "textDocument": {"uri": incremental_uri, "version": 3},
            "contentChanges": [{"text": FINAL}]
        })),
    );
    barrier(&mut server, 8);
    expect_empty(&mut server, &incremental_uri, 3);
    assert_eq!(
        request_tokens(&mut server, 9, &incremental_uri),
        incremental_tokens
    );

    shutdown(server, 10);
}

#[test]
fn lone_cr_ranged_edits_match_full_replacements_for_policy_and_schema() {
    assert_lone_cr_incremental_parity(
        "dw",
        "dogwood",
        LONE_CR_POLICY_INITIAL,
        LONE_CR_POLICY_FINAL,
        (1, 3),
        (1, 5),
    );
    assert_lone_cr_incremental_parity(
        "dwschema",
        "dogwood-event-schema",
        LONE_CR_SCHEMA_INITIAL,
        LONE_CR_SCHEMA_FINAL,
        (1, 1),
        (1, 3),
    );
}

fn assert_lone_cr_incremental_parity(
    extension: &str,
    language_id: &str,
    initial: &str,
    final_text: &str,
    start: (u32, u32),
    end: (u32, u32),
) {
    let workspace = Workspace::new();
    let root_uri = uri(&workspace.root);
    let incremental_uri = workspace.uri(&format!("incremental.{extension}"));
    let full_uri = workspace.uri(&format!("full.{extension}"));
    let mut server = LspProcess::spawn_with_test_control();
    initialize(&mut server, &root_uri);

    open(&mut server, &incremental_uri, language_id, 1, initial);
    barrier(&mut server, 1);
    expect_nonempty(&mut server, &incremental_uri, 1);
    server.send_notification(
        "textDocument/didChange",
        Some(json!({
            "textDocument": {"uri": incremental_uri, "version": 2},
            "contentChanges": [{
                "range": {
                    "start": {"line": start.0, "character": start.1},
                    "end": {"line": end.0, "character": end.1}
                },
                "rangeLength": 2,
                "text": ""
            }]
        })),
    );
    barrier(&mut server, 2);
    expect_empty(&mut server, &incremental_uri, 2);
    let incremental_tokens = request_tokens(&mut server, 3, &incremental_uri);

    open(&mut server, &full_uri, language_id, 1, initial);
    barrier(&mut server, 4);
    expect_nonempty(&mut server, &full_uri, 1);
    server.send_notification(
        "textDocument/didChange",
        Some(json!({
            "textDocument": {"uri": full_uri, "version": 2},
            "contentChanges": [{"text": final_text}]
        })),
    );
    barrier(&mut server, 5);
    expect_empty(&mut server, &full_uri, 2);
    assert_eq!(
        request_tokens(&mut server, 6, &full_uri),
        incremental_tokens,
        "{extension} lone-CR ranged edit must match a full replacement"
    );

    shutdown(server, 7);
}

fn initialize(server: &mut LspProcess, root_uri: &str) {
    server.send_request(
        0,
        "initialize",
        Some(json!({"capabilities": {}, "rootUri": root_uri})),
    );
    let response = server.receive_response(0);
    assert_eq!(
        response["result"]["capabilities"]["textDocumentSync"]["change"],
        2
    );
    server.send_notification("initialized", Some(json!({})));
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

fn barrier(server: &mut LspProcess, id: i64) {
    server.send_request(id, "dogwood/testBarrier", Some(json!({})));
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
            .is_some_and(|diagnostics| !diagnostics.is_empty())
    );
}

fn request_tokens(server: &mut LspProcess, id: i64, uri: &str) -> Value {
    server.send_request(
        id,
        "textDocument/semanticTokens/full",
        Some(json!({"textDocument": {"uri": uri}})),
    );
    server.receive_response(id)["result"]["data"].clone()
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
