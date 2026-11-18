// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#![cfg(all(unix, feature = "test-control"))]

#[path = "support/lsp_process.rs"]
mod lsp_process;
#[path = "support/temp_root.rs"]
mod temp_root;

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use dogwood_lsp::project::path_to_file_uri;
use lsp_process::LspProcess;
use serde_json::{Value, json};

const ACTION_SCHEMA: &str = include_str!("fixtures/dogwood/m3/default-valid/schema.cedarschema");
const FIRST: &str = "permit(";
const SECOND: &str = "permit(principal, action, resource);";
const CONFIGURED_POLICY: &str = r#"permit(principal, action == Drupe::Action::"GetStockInfo", resource)
when { configured(true) }
when temporal { happened(1h, Drupe::Action::"GetStockInfo"::request{}) };"#;
const CONFIGURED_MACROS: &str = r#"def cedar configured(?value) { ?value == true };
def temporal happened(?window, ?event) { formerly within ?window ?event };"#;
const COMMENT_WINDOW_POLICY: &str = r#"permit(principal, action, resource) when temporal {
formerly within 1 // window gap
h Drupe::Action::"GetStockInfo"::request{}
};"#;
const PUBLISH_DIAGNOSTICS: &str = "textDocument/publishDiagnostics";
const REGISTER_CAPABILITY: &str = "client/registerCapability";
const FIRST_TOKENS: &[u32] = &[0, 0, 6, 12, 0, 0, 6, 1, 17, 0];
const SECOND_TOKENS: &[u32] = &[
    0, 0, 6, 12, 0, 0, 6, 1, 17, 0, 0, 1, 9, 5, 0, 0, 9, 1, 17, 0, 0, 2, 6, 5, 0, 0, 6, 1, 17, 0,
    0, 2, 8, 5, 0, 0, 8, 1, 17, 0, 0, 1, 1, 17, 0,
];
const COMMENT_WINDOW_TOKENS: &[u32] = &[
    0, 0, 6, 12, 0, 0, 6, 1, 17, 0, 0, 1, 9, 5, 0, 0, 9, 1, 17, 0, 0, 2, 6, 5, 0, 0, 6, 1, 17, 0,
    0, 2, 8, 5, 0, 0, 8, 1, 17, 0, 0, 2, 4, 12, 0, 0, 5, 8, 12, 0, 0, 9, 1, 17, 0, 1, 0, 8, 12, 0,
    0, 9, 6, 12, 0, 0, 7, 1, 16, 0, 0, 2, 13, 14, 0, 1, 0, 1, 16, 0, 0, 2, 5, 0, 0, 0, 5, 2, 17, 0,
    0, 2, 6, 1, 0, 0, 6, 2, 17, 0, 0, 2, 14, 15, 0, 0, 14, 2, 17, 0, 0, 2, 7, 8, 0, 0, 7, 1, 17, 0,
    0, 1, 1, 17, 0, 1, 0, 1, 17, 0, 0, 1, 1, 17, 0,
];

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "dogwood-lsp-m5-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).expect("temporary workspace should be created");
        let root = temp_root::canonical(&root);
        fs::write(root.join("actions.cedarschema"), ACTION_SCHEMA)
            .expect("action schema should be written");
        fs::write(root.join("policy.dw"), FIRST).expect("policy fixture should be written");
        Self { root }
    }

    fn root_uri(&self) -> String {
        path_to_file_uri(&self.root)
            .expect("temporary root should have a file URI")
            .as_str()
            .to_owned()
    }

    fn policy_uri(&self) -> String {
        path_to_file_uri(&self.root.join("policy.dw"))
            .expect("temporary policy should have a file URI")
            .as_str()
            .to_owned()
    }

    fn uri(&self, relative: &str) -> String {
        path_to_file_uri(&self.root.join(relative))
            .expect("temporary source should have a file URI")
            .as_str()
            .to_owned()
    }

    fn write(&self, relative: &str, source: &str) {
        fs::write(self.root.join(relative), source).expect("fixture source should be written");
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = make_tree_readable(&self.root);
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[cfg(unix)]
fn make_tree_readable(root: &Path) -> std::io::Result<()> {
    use std::os::unix::fs::PermissionsExt;

    for entry in fs::read_dir(root)? {
        let path = entry?.path();
        let metadata = fs::symlink_metadata(&path)?;
        if metadata.is_dir() {
            make_tree_readable(&path)?;
        } else {
            fs::set_permissions(path, fs::Permissions::from_mode(0o600))?;
        }
    }
    Ok(())
}

#[cfg(not(unix))]
fn make_tree_readable(_root: &Path) -> std::io::Result<()> {
    Ok(())
}

#[test]
fn compiled_server_uses_the_current_full_document_for_diagnostics_and_tokens() {
    let workspace = Workspace::new();
    let root_uri = workspace.root_uri();
    let policy_uri = workspace.policy_uri();
    let mut server = LspProcess::spawn_with_test_control();

    server.send_request(
        0,
        "initialize",
        Some(json!({
            "capabilities": {},
            "workspaceFolders": [{"uri": root_uri, "name": "m5"}]
        })),
    );
    let initialize = server.receive_response(0);
    assert_eq!(
        initialize["result"]["capabilities"]["positionEncoding"],
        "utf-16"
    );
    assert_eq!(
        initialize["result"]["capabilities"]["textDocumentSync"]["change"],
        2
    );
    server.send_notification("initialized", Some(json!({})));

    open(&mut server, &policy_uri, 1, FIRST);
    barrier(&mut server, 1);
    assert_invalid_diagnostics(&mut server, &policy_uri, 1);
    let first = request_tokens(&mut server, 2, &policy_uri);
    assert_eq!(first, FIRST_TOKENS);
    let repeated_first = request_tokens(&mut server, 3, &policy_uri);
    assert_eq!(repeated_first, first);

    change(&mut server, &policy_uri, 2, SECOND);
    barrier(&mut server, 4);
    assert_empty_diagnostics(&mut server, &policy_uri, 2);
    let second = request_tokens(&mut server, 5, &policy_uri);
    assert_eq!(second, SECOND_TOKENS);
    assert_ne!(second, first);
    let repeated_second = request_tokens(&mut server, 6, &policy_uri);
    assert_eq!(repeated_second, second);

    server.send_request(7, "shutdown", None);
    server.expect_response(7, json!({"jsonrpc": "2.0", "id": 7, "result": null}));
    server.send_notification("exit", Some(Value::Null));
    server.finish(0);
}

#[test]
fn compiled_server_preserves_comment_between_temporal_interval_components() {
    let workspace = Workspace::new();
    workspace.write("policy.dw", COMMENT_WINDOW_POLICY);
    let root_uri = workspace.root_uri();
    let policy_uri = workspace.policy_uri();
    let mut server = LspProcess::spawn_with_test_control();

    server.send_request(
        0,
        "initialize",
        Some(json!({
            "capabilities": {},
            "workspaceFolders": [{"uri": root_uri, "name": "m5-interval-comment"}]
        })),
    );
    server.receive_response(0);
    server.send_notification("initialized", Some(json!({})));

    open(&mut server, &policy_uri, 1, COMMENT_WINDOW_POLICY);
    barrier(&mut server, 1);
    assert_empty_diagnostics(&mut server, &policy_uri, 1);
    let tokens = request_tokens(&mut server, 2, &policy_uri);
    assert_eq!(tokens, COMMENT_WINDOW_TOKENS);
    assert_eq!(request_tokens(&mut server, 3, &policy_uri), tokens);

    server.send_request(4, "shutdown", None);
    server.expect_response(4, json!({"jsonrpc": "2.0", "id": 4, "result": null}));
    server.send_notification("exit", Some(Value::Null));
    server.finish(0);
}

#[test]
fn compiled_server_uses_open_configured_macro_snapshot_for_structural_tokens() {
    let workspace = Workspace::new();
    workspace.write("policy.dw", CONFIGURED_POLICY);
    workspace.write("macros.dw", "def cedar broken(");
    let root_uri = workspace.root_uri();
    let policy_uri = workspace.policy_uri();
    let macros_uri = workspace.uri("macros.dw");
    let mut server = LspProcess::spawn_with_test_control();

    server.send_request(
        0,
        "initialize",
        Some(json!({
            "capabilities": {},
            "workspaceFolders": [{"uri": root_uri, "name": "m5-macros"}]
        })),
    );
    server.receive_response(0);
    server.send_notification("initialized", Some(json!({})));

    open(&mut server, &policy_uri, 1, CONFIGURED_POLICY);
    barrier(&mut server, 1);
    let invalid = server.receive_notification(PUBLISH_DIAGNOSTICS);
    assert_eq!(invalid["params"]["uri"], policy_uri);
    assert_eq!(invalid["params"]["version"], 1);
    assert!(
        invalid["params"]["diagnostics"]
            .as_array()
            .is_some_and(|diagnostics| !diagnostics.is_empty())
    );
    let fallback = request_tokens(&mut server, 2, &policy_uri);
    assert!(
        !fallback
            .as_chunks::<5>()
            .0
            .iter()
            .any(|token| token[3] == 11),
        "broken configured macros must not manufacture a structural macro token"
    );
    assert_eq!(request_tokens(&mut server, 3, &policy_uri), fallback);

    open(&mut server, &macros_uri, 4, CONFIGURED_MACROS);
    barrier(&mut server, 4);
    assert_empty_diagnostics(&mut server, &policy_uri, 1);
    let structural = request_tokens(&mut server, 5, &policy_uri);
    assert!(
        structural.as_chunks::<5>().0.contains(&[0, 2, 10, 11, 0]),
        "configured Cedar macro call must be structural"
    );
    assert!(
        structural.as_chunks::<5>().0.contains(&[0, 2, 8, 11, 0]),
        "configured temporal macro call must be structural"
    );
    assert!(
        structural
            .windows(10)
            .any(|tokens| tokens == [0, 1, 1, 16, 0, 0, 1, 1, 16, 0]),
        "configured temporal interval components must remain present"
    );
    assert_ne!(structural, fallback);
    assert_eq!(request_tokens(&mut server, 6, &policy_uri), structural);

    server.send_request(7, "shutdown", None);
    server.expect_response(7, json!({"jsonrpc": "2.0", "id": 7, "result": null}));
    server.send_notification("exit", Some(Value::Null));
    server.finish(0);
}

#[test]
fn compiled_server_retains_validated_external_macro_snapshot_until_notification() {
    let workspace = Workspace::new();
    let external = Workspace::new();
    workspace.write("policy.dw", CONFIGURED_POLICY);
    external.write("macros.dw", CONFIGURED_MACROS);
    let root_uri = workspace.root_uri();
    let policy_uri = workspace.policy_uri();
    let action_schema = workspace.root.join("actions.cedarschema");
    let macros_path = external.root.join("macros.dw");
    let macros_uri = external.uri("macros.dw");
    let mut server = LspProcess::spawn_with_test_control();

    server.send_request(
        0,
        "initialize",
        Some(json!({
            "capabilities": {
                "workspace": {
                    "didChangeWatchedFiles": {
                        "dynamicRegistration": true,
                        "relativePatternSupport": true
                    }
                }
            },
            "workspaceFolders": [{"uri": root_uri, "name": "m5-external-macros"}],
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": action_schema.to_string_lossy(),
                    "macros": macros_path.to_string_lossy()
                }]
            }
        })),
    );
    server.receive_response(0);
    server.send_notification("initialized", Some(json!({})));
    let registration = server.receive_server_request(REGISTER_CAPABILITY);
    server.send_success_response(registration["id"].clone(), Value::Null);

    open(&mut server, &policy_uri, 1, CONFIGURED_POLICY);
    barrier(&mut server, 1);
    assert_empty_diagnostics(&mut server, &policy_uri, 1);
    let validated = request_tokens(&mut server, 2, &policy_uri);
    assert!(
        validated
            .as_chunks::<5>()
            .0
            .iter()
            .any(|token| token[3] == 11),
        "validated configured macro calls must be structurally classified"
    );
    assert_eq!(request_tokens(&mut server, 3, &policy_uri), validated);

    external.write("macros.dw", "def cedar broken(");
    assert_eq!(
        request_tokens(&mut server, 4, &policy_uri),
        validated,
        "an unnotified disk mutation must not skew tokens from published diagnostics"
    );
    assert_eq!(request_tokens(&mut server, 5, &policy_uri), validated);

    watched(&mut server, &macros_uri, 2);
    barrier(&mut server, 6);
    let invalid = server.receive_notification(PUBLISH_DIAGNOSTICS);
    assert_eq!(invalid["params"]["uri"], policy_uri);
    assert_eq!(invalid["params"]["version"], 1);
    assert!(
        invalid["params"]["diagnostics"]
            .as_array()
            .is_some_and(|diagnostics| !diagnostics.is_empty())
    );
    let fallback = request_tokens(&mut server, 7, &policy_uri);
    assert_ne!(fallback, validated);
    assert!(
        !fallback
            .as_chunks::<5>()
            .0
            .iter()
            .any(|token| token[3] == 11),
        "notified invalid macros must clear the structural snapshot"
    );
    assert_eq!(request_tokens(&mut server, 8, &policy_uri), fallback);

    server.send_request(9, "shutdown", None);
    server.expect_response(9, json!({"jsonrpc": "2.0", "id": 9, "result": null}));
    server.send_notification("exit", Some(Value::Null));
    server.finish(0);
}

fn open(server: &mut LspProcess, uri: &str, version: i32, text: &str) {
    server.send_notification(
        "textDocument/didOpen",
        Some(json!({
            "textDocument": {
                "uri": uri,
                "languageId": "dogwood",
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

fn watched(server: &mut LspProcess, uri: &str, typ: i32) {
    server.send_notification(
        "workspace/didChangeWatchedFiles",
        Some(json!({"changes": [{"uri": uri, "type": typ}]})),
    );
}

fn barrier(server: &mut LspProcess, id: i64) {
    server.send_request(id, "dogwood/testBarrier", Some(json!({})));
    let response = server.receive_response(id);
    assert_eq!(response["error"]["code"], -32601);
}

fn assert_empty_diagnostics(server: &mut LspProcess, uri: &str, version: i32) {
    server.expect_notification(
        PUBLISH_DIAGNOSTICS,
        json!({"uri": uri, "version": version, "diagnostics": []}),
    );
}

fn assert_invalid_diagnostics(server: &mut LspProcess, uri: &str, version: i32) {
    server.expect_notification(
        PUBLISH_DIAGNOSTICS,
        json!({
            "uri": uri,
            "version": version,
            "diagnostics": [{
                "range": {
                    "start": {"line": 0, "character": 7},
                    "end": {"line": 0, "character": 7}
                },
                "severity": 1,
                "source": "dogwood",
                "message": "unexpected end of input, expected identifier"
            }]
        }),
    );
}

fn request_tokens(server: &mut LspProcess, id: i64, uri: &str) -> Vec<u32> {
    server.send_request(
        id,
        "textDocument/semanticTokens/full",
        Some(json!({"textDocument": {"uri": uri}})),
    );
    let response = server.receive_response(id);
    response["result"]["data"]
        .as_array()
        .unwrap_or_else(|| panic!("semantic response has no data: {response}"))
        .iter()
        .map(|word| {
            u32::try_from(
                word.as_u64()
                    .unwrap_or_else(|| panic!("semantic word is not unsigned: {word}")),
            )
            .expect("semantic word should fit u32")
        })
        .collect()
}
