#![cfg(feature = "test-control")]

#[path = "support/lsp_process.rs"]
mod lsp_process;

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use dogwood_lsp::project::path_to_file_uri;
use lsp_process::LspProcess;
use serde_json::{Value, json};

const PUBLISH_DIAGNOSTICS: &str = "textDocument/publishDiagnostics";
const ACTION_SCHEMA: &str = r#"namespace App {
  type LoginInput = { user: String };
  type LoginOutput = { ok: Bool };
  type ReadInput = { user: String };
  type ReadOutput = { ok: Bool };
  entity User;
  entity Resource;
  action "Login" appliesTo {
    principal: [User],
    resource: [Resource],
    context: { input: LoginInput, output?: LoginOutput }
  };
  action "Read" appliesTo {
    principal: [User],
    resource: [Resource],
    context: { input: ReadInput, output?: ReadOutput }
  };
}"#;
const POLICY: &str = "permit(principal, action == App::Action::\"Read\", resource) when temporal {\n\
                      formerly within 1h App::Action::\"Login\"::attempt{input.user: context.input.user}\n\
                      };";
const INITIAL_SCHEMA: &str = "decision event <A>::attempt {\n    ...inputs(A),\n}\n\
                             event <A>::outcome {\n    ...outputs(A),\n}\n";
const INVALID_SCHEMA: &str = "decision event <A>::attempt {";
const REPAIRED_SCHEMA: &str = "max_window = 2h\n\
                              decision event <A>::attempt {\n    ...inputs(A),\n    tag: String,\n}\n\
                              event <A>::audit {\n    ...inputs(A),\n}\n";
const INVALID_MESSAGE: &str = "event schema error: event schema parse error:  --> 1:30\n  |\n\
                              1 | decision event <A>::attempt {\n  |                              ^---\n  |\n  = expected field";

const INITIAL_SCHEMA_TOKENS: &[u32] = &[
    0, 0, 8, 12, 0, 0, 9, 5, 12, 0, 0, 6, 1, 17, 0, 0, 1, 1, 3, 1, 0, 1, 1, 17, 0, 0, 1, 2, 17, 0,
    0, 2, 7, 8, 1, 0, 8, 1, 17, 0, 1, 4, 1, 17, 0, 0, 1, 1, 17, 0, 0, 1, 1, 17, 0, 0, 1, 6, 9, 0,
    0, 6, 1, 17, 0, 0, 1, 1, 3, 0, 0, 1, 1, 17, 0, 0, 1, 1, 17, 0, 1, 0, 1, 17, 0, 1, 0, 5, 12, 0,
    0, 6, 1, 17, 0, 0, 1, 1, 3, 1, 0, 1, 1, 17, 0, 0, 1, 2, 17, 0, 0, 2, 7, 8, 1, 0, 8, 1, 17, 0,
    1, 4, 1, 17, 0, 0, 1, 1, 17, 0, 0, 1, 1, 17, 0, 0, 1, 7, 9, 0, 0, 7, 1, 17, 0, 0, 1, 1, 3, 0,
    0, 1, 1, 17, 0, 0, 1, 1, 17, 0, 1, 0, 1, 17, 0,
];
const REPAIRED_SCHEMA_TOKENS: &[u32] = &[
    0, 0, 10, 12, 0, 0, 11, 1, 17, 0, 0, 2, 1, 16, 0, 0, 1, 1, 16, 0, 1, 0, 8, 12, 0, 0, 9, 5, 12,
    0, 0, 6, 1, 17, 0, 0, 1, 1, 3, 1, 0, 1, 1, 17, 0, 0, 1, 2, 17, 0, 0, 2, 7, 8, 1, 0, 8, 1, 17,
    0, 1, 4, 1, 17, 0, 0, 1, 1, 17, 0, 0, 1, 1, 17, 0, 0, 1, 6, 9, 0, 0, 6, 1, 17, 0, 0, 1, 1, 3,
    0, 0, 1, 1, 17, 0, 0, 1, 1, 17, 0, 1, 4, 3, 6, 1, 0, 3, 1, 17, 0, 0, 2, 6, 1, 0, 0, 6, 1, 17,
    0, 1, 0, 1, 17, 0, 1, 0, 5, 12, 0, 0, 6, 1, 17, 0, 0, 1, 1, 3, 1, 0, 1, 1, 17, 0, 0, 1, 2, 17,
    0, 0, 2, 5, 8, 1, 0, 6, 1, 17, 0, 1, 4, 1, 17, 0, 0, 1, 1, 17, 0, 0, 1, 1, 17, 0, 0, 1, 6, 9,
    0, 0, 6, 1, 17, 0, 0, 1, 1, 3, 0, 0, 1, 1, 17, 0, 0, 1, 1, 17, 0, 1, 0, 1, 17, 0,
];
const INVALID_SCHEMA_TOKENS: &[u32] = &[
    0, 15, 1, 17, 0, 0, 2, 1, 17, 0, 0, 1, 2, 17, 0, 0, 10, 1, 17, 0,
];
const POLICY_TOKENS: &[u32] = &[
    0, 0, 6, 12, 0, 0, 6, 1, 17, 0, 0, 1, 9, 5, 0, 0, 9, 1, 17, 0, 0, 2, 6, 5, 0, 0, 7, 2, 17, 0,
    0, 3, 3, 0, 0, 0, 3, 2, 17, 0, 0, 2, 6, 1, 0, 0, 6, 2, 17, 0, 0, 2, 6, 15, 0, 0, 6, 1, 17, 0,
    0, 2, 8, 5, 0, 0, 8, 1, 17, 0, 0, 2, 4, 12, 0, 0, 5, 8, 12, 0, 0, 9, 1, 17, 0, 1, 0, 8, 12, 0,
    0, 9, 6, 12, 0, 0, 7, 1, 16, 0, 0, 1, 1, 16, 0, 0, 2, 3, 0, 0, 0, 3, 2, 17, 0, 0, 2, 6, 1, 0,
    0, 6, 2, 17, 0, 0, 2, 7, 15, 0, 0, 7, 2, 17, 0, 0, 2, 7, 8, 0, 0, 7, 1, 17, 0, 0, 1, 5, 6, 0,
    0, 5, 1, 17, 0, 0, 1, 4, 6, 0, 0, 4, 1, 17, 0, 0, 2, 7, 5, 0, 0, 7, 1, 17, 0, 0, 1, 5, 6, 0, 0,
    5, 1, 17, 0, 0, 1, 4, 6, 0, 0, 4, 1, 17, 0, 1, 0, 1, 17, 0, 0, 1, 1, 17, 0,
];

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "dogwood-lsp-m6-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("actions.cedarschema"), ACTION_SCHEMA).unwrap();
        fs::write(root.join("events.dwschema"), INITIAL_SCHEMA).unwrap();
        fs::write(root.join("policy.dw"), POLICY).unwrap();
        Self { root }
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

#[test]
fn compiled_server_tracks_schema_diagnostics_tokens_and_policy_snapshots_end_to_end() {
    let workspace = Workspace::new();
    let root_uri = workspace.root_uri();
    let policy_uri = workspace.uri("policy.dw");
    let schema_uri = workspace.uri("events.dwschema");
    let mut server = LspProcess::spawn_with_test_control();
    initialize(&mut server, &[(&root_uri, "m6")], None);

    open(&mut server, &policy_uri, "dogwood", 1, POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &policy_uri, 1);
    assert_eq!(request_tokens(&mut server, 2, &policy_uri), POLICY_TOKENS);

    open(
        &mut server,
        &schema_uri,
        "dogwood-event-schema",
        4,
        INITIAL_SCHEMA,
    );
    barrier(&mut server, 3);
    expect_empty(&mut server, &schema_uri, 4);
    expect_empty(&mut server, &policy_uri, 1);
    assert_eq!(
        request_tokens(&mut server, 4, &schema_uri),
        INITIAL_SCHEMA_TOKENS
    );
    assert_eq!(
        request_tokens(&mut server, 5, &schema_uri),
        INITIAL_SCHEMA_TOKENS
    );

    change(&mut server, &schema_uri, 5, INVALID_SCHEMA);
    barrier(&mut server, 6);
    expect_invalid_schema(&mut server, &schema_uri, 5);
    expect_policy_schema_failure(&mut server, &policy_uri, 1, &schema_uri);
    assert_eq!(
        request_tokens(&mut server, 7, &schema_uri),
        INVALID_SCHEMA_TOKENS
    );
    assert_eq!(
        request_tokens(&mut server, 8, &schema_uri),
        INVALID_SCHEMA_TOKENS
    );

    change(&mut server, &schema_uri, 6, REPAIRED_SCHEMA);
    barrier(&mut server, 9);
    expect_empty(&mut server, &schema_uri, 6);
    expect_empty(&mut server, &policy_uri, 1);
    assert_eq!(
        request_tokens(&mut server, 10, &schema_uri),
        REPAIRED_SCHEMA_TOKENS
    );
    assert_eq!(request_tokens(&mut server, 11, &policy_uri), POLICY_TOKENS);
    assert_eq!(request_tokens(&mut server, 12, &policy_uri), POLICY_TOKENS);

    close(&mut server, &schema_uri);
    barrier(&mut server, 13);
    expect_empty(&mut server, &schema_uri, 6);
    expect_empty(&mut server, &policy_uri, 1);
    assert_eq!(request_tokens(&mut server, 14, &policy_uri), POLICY_TOKENS);

    close(&mut server, &policy_uri);
    barrier(&mut server, 15);
    expect_empty(&mut server, &policy_uri, 1);
    server.assert_no_queued_server_messages();
    shutdown(server, 16);
}

#[test]
fn compiled_server_freezes_document_kind_precedence_and_dependency_rejection() {
    let workspace = Workspace::new();
    fs::write(workspace.root.join("schema.input"), ACTION_SCHEMA).unwrap();
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        &[(&root_uri, "precedence")],
        Some(json!({
            "bundles": [{
                "workspaceFolder": root_uri.clone(),
                "actionSchema": "schema.input"
            }]
        })),
    );

    let schema_cases = [
        ("extension.dwschema", "plaintext"),
        ("specific", "dogwood-event-schema"),
        ("specific.txt", "dogwood-event-schema"),
        ("unknown.dwschema", "unknown-language"),
    ];
    let mut request_id = 1;
    for (relative, language_id) in schema_cases {
        let document_uri = workspace.uri(relative);
        open(
            &mut server,
            &document_uri,
            language_id,
            request_id as i32,
            INITIAL_SCHEMA,
        );
        barrier(&mut server, request_id);
        request_id += 1;
        expect_empty(&mut server, &document_uri, (request_id - 1) as i32);
        assert_eq!(
            request_tokens(&mut server, request_id, &document_uri),
            INITIAL_SCHEMA_TOKENS,
            "{relative} with {language_id}"
        );
        request_id += 1;
    }

    for (relative, language_id) in [
        ("mismatch.dw", "dogwood-event-schema"),
        ("unknown.dw", "unknown-language"),
    ] {
        let document_uri = workspace.uri(relative);
        open(
            &mut server,
            &document_uri,
            language_id,
            request_id as i32,
            "permit(principal, action, resource);",
        );
        barrier(&mut server, request_id);
        request_id += 1;
        expect_empty(&mut server, &document_uri, (request_id - 1) as i32);
        let tokens = request_tokens(&mut server, request_id, &document_uri);
        assert!(
            tokens.as_chunks::<5>().0.iter().all(|token| token[3] != 8),
            ".dw extension must select policy analysis"
        );
        request_id += 1;
    }

    for (relative, language_id) in [("generic", "dogwood"), ("unknown.txt", "unknown-language")] {
        let document_uri = workspace.uri(relative);
        open(
            &mut server,
            &document_uri,
            language_id,
            request_id as i32,
            INITIAL_SCHEMA,
        );
        barrier(&mut server, request_id);
        request_id += 1;
        server.assert_no_queued_notifications();
        assert_tokens_rejected(&mut server, request_id, &document_uri);
        request_id += 1;
    }

    for relative in ["actions.cedarschema", "schema.input"] {
        let document_uri = workspace.uri(relative);
        open(
            &mut server,
            &document_uri,
            "dogwood-event-schema",
            request_id as i32,
            ACTION_SCHEMA,
        );
        barrier(&mut server, request_id);
        request_id += 1;
        if relative == "schema.input" {
            expect_empty(&mut server, &workspace.uri("mismatch.dw"), 9);
            expect_empty(&mut server, &workspace.uri("unknown.dw"), 11);
        } else {
            server.assert_no_queued_notifications();
        }
        assert_tokens_rejected(&mut server, request_id, &document_uri);
        request_id += 1;
    }

    shutdown(server, request_id);
}

#[test]
fn separate_workspaces_do_not_cross_publish_or_cross_classify() {
    let first = Workspace::new();
    let second = Workspace::new();
    let first_root = first.root_uri();
    let second_root = second.root_uri();
    let first_policy = first.uri("policy.dw");
    let second_policy = second.uri("policy.dw");
    let first_schema = first.uri("events.dwschema");
    let second_schema = second.uri("events.dwschema");
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        &[(&first_root, "first"), (&second_root, "second")],
        None,
    );

    open(&mut server, &first_policy, "dogwood", 1, POLICY);
    barrier(&mut server, 1);
    expect_empty(&mut server, &first_policy, 1);
    open(&mut server, &second_policy, "dogwood", 2, POLICY);
    barrier(&mut server, 2);
    expect_empty(&mut server, &second_policy, 2);

    open(
        &mut server,
        &first_schema,
        "dogwood-event-schema",
        3,
        INVALID_SCHEMA,
    );
    barrier(&mut server, 3);
    expect_invalid_schema(&mut server, &first_schema, 3);
    expect_policy_schema_failure(&mut server, &first_policy, 1, &first_schema);
    server.assert_no_queued_notifications();

    open(
        &mut server,
        &second_schema,
        "dogwood-event-schema",
        4,
        INITIAL_SCHEMA,
    );
    barrier(&mut server, 4);
    expect_empty(&mut server, &second_schema, 4);
    expect_empty(&mut server, &second_policy, 2);
    server.assert_no_queued_notifications();
    assert_eq!(
        request_tokens(&mut server, 5, &first_schema),
        INVALID_SCHEMA_TOKENS
    );
    assert_eq!(
        request_tokens(&mut server, 6, &second_schema),
        INITIAL_SCHEMA_TOKENS
    );

    change(&mut server, &first_schema, 5, REPAIRED_SCHEMA);
    barrier(&mut server, 7);
    expect_empty(&mut server, &first_schema, 5);
    expect_empty(&mut server, &first_policy, 1);
    server.assert_no_queued_notifications();
    assert_eq!(
        request_tokens(&mut server, 8, &second_policy),
        POLICY_TOKENS
    );

    shutdown(server, 9);
}

fn initialize(
    server: &mut LspProcess,
    workspaces: &[(&str, &str)],
    initialization_options: Option<Value>,
) {
    let folders = workspaces
        .iter()
        .map(|(uri, name)| json!({"uri": uri, "name": name}))
        .collect::<Vec<_>>();
    let mut params = json!({"capabilities": {}, "workspaceFolders": folders});
    if let Some(options) = initialization_options {
        params["initializationOptions"] = options;
    }
    server.send_request(0, "initialize", Some(params));
    let response = server.receive_response(0);
    assert_eq!(
        response["result"]["capabilities"]["positionEncoding"],
        "utf-16"
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

fn expect_invalid_schema(server: &mut LspProcess, schema_uri: &str, version: i32) {
    server.expect_notification(
        PUBLISH_DIAGNOSTICS,
        json!({
            "uri": schema_uri,
            "version": version,
            "diagnostics": [{
                "range": zero_range(),
                "severity": 1,
                "source": "dogwood",
                "message": INVALID_MESSAGE
            }]
        }),
    );
}

fn expect_policy_schema_failure(
    server: &mut LspProcess,
    policy_uri: &str,
    version: i32,
    schema_uri: &str,
) {
    server.expect_notification(
        PUBLISH_DIAGNOSTICS,
        json!({
            "uri": policy_uri,
            "version": version,
            "diagnostics": [{
                "range": zero_range(),
                "severity": 1,
                "source": "dogwood",
                "message": INVALID_MESSAGE,
                "relatedInformation": [{
                    "location": {
                        "uri": schema_uri,
                        "range": zero_range()
                    },
                    "message": INVALID_MESSAGE
                }]
            }]
        }),
    );
}

fn zero_range() -> Value {
    json!({
        "start": {"line": 0, "character": 0},
        "end": {"line": 0, "character": 0}
    })
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
        .map(|word| u32::try_from(word.as_u64().unwrap()).unwrap())
        .collect()
}

fn assert_tokens_rejected(server: &mut LspProcess, id: i64, uri: &str) {
    server.send_request(
        id,
        "textDocument/semanticTokens/full",
        Some(json!({"textDocument": {"uri": uri}})),
    );
    let response = server.receive_response(id);
    assert_eq!(response["error"]["code"], -32803);
    assert_eq!(response["error"]["message"], "Document is not open");
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
