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
const REGISTER_CAPABILITY: &str = "client/registerCapability";
const WATCH_REGISTRATION_REQUEST_ID: &str = "dogwood-lsp/register-watched-files";
const WATCH_REGISTRATION_ID: &str = "dogwood-lsp/watched-files";
const EXTERNAL_WATCH_MESSAGE: &str = "Dogwood project configuration error: external explicit \
    dependencies require successful dynamic watched-file registration with \
    relativePatternSupport";
const VALID_POLICY: &str = include_str!("fixtures/dogwood/m3/default-valid/policy.dw");
const VALID_ACTION_SCHEMA: &str =
    include_str!("fixtures/dogwood/m3/default-valid/schema.cedarschema");
const INVALID_POLICY: &str =
    include_str!("fixtures/dogwood/m3/schema-aware-validation-failure/policy.dw");
const INVALID_POLICY_SCHEMA: &str =
    include_str!("fixtures/dogwood/m3/schema-aware-validation-failure/schema.cedarschema");
const ALL_OPTIONAL_POLICY: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/policy.dw");
const ALL_OPTIONAL_SCHEMA: &str =
    include_str!("fixtures/dogwood/m3/all-optional-valid/schema.cedarschema");
const ALL_OPTIONAL_EVENTS: &str =
    include_str!("fixtures/dogwood/m3/all-optional-valid/event.dwschema");
const ALL_OPTIONAL_PROVIDERS: &str =
    include_str!("fixtures/dogwood/m3/all-optional-valid/providers.json");
const ALL_OPTIONAL_MACROS: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/macros.dw");
const MACRO_FAILURE_POLICY: &str =
    include_str!("fixtures/dogwood/m3/macro-source-failure/policy.dw");
const MACRO_FAILURE_SCHEMA: &str =
    include_str!("fixtures/dogwood/m3/macro-source-failure/schema.cedarschema");
const MACRO_FAILURE_SOURCE: &str =
    include_str!("fixtures/dogwood/m3/macro-source-failure/macros.dw");
const WARNING_POLICY: &str = include_str!("fixtures/dogwood/m3/validation-warning/policy.dw");
const WARNING_SCHEMA: &str =
    include_str!("fixtures/dogwood/m3/validation-warning/schema.cedarschema");

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "dogwood-lsp-m4-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).expect("temporary workspace should be created");
        Self { root }
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.root.join(relative)
    }

    fn write(&self, relative: &str, contents: impl AsRef<[u8]>) -> PathBuf {
        let path = self.path(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be created");
        }
        fs::write(&path, contents).expect("fixture should be written");
        path
    }

    fn uri(&self, relative: &str) -> String {
        uri(&self.path(relative))
    }

    fn root_uri(&self) -> String {
        uri(&self.root)
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
fn explicit_configuration_publishes_exact_dogwood_finding_and_close_clears_tracking() {
    let workspace = Workspace::new();
    workspace.write("config/schema.cedarschema", INVALID_POLICY_SCHEMA);
    let policy_path = workspace.write("policies/policy.dw", INVALID_POLICY);
    let policy_uri = uri(&policy_path);
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {},
            "workspaceFolders": [{"uri": root_uri, "name": "workspace"}],
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "config/schema.cedarschema"
                }]
            }
        }),
    );

    open(&mut server, &policy_uri, 4, INVALID_POLICY);
    barrier(&mut server, 1);
    server.expect_notification(
        PUBLISH_DIAGNOSTICS,
        json!({
            "uri": policy_uri,
            "version": 4,
            "diagnostics": [{
                "range": {
                    "start": {"line": 5, "character": 4},
                    "end": {"line": 6, "character": 0}
                },
                "severity": 1,
                "code": "extension",
                "source": "dogwood",
                "message": "predicate `Drupe::Action::\"Login\"::request` mentions field \
                            `input.usre`, which is not declared on that event (declared fields: \
                            callerPrincipal, callerResource, input.server, input.user, requestId, \
                            sessionId)"
            }]
        }),
    );

    server.send_request(
        2,
        "textDocument/semanticTokens/full",
        Some(json!({"textDocument": {"uri": policy_uri}})),
    );
    let response = server.receive_response(2);
    assert!(
        response
            .get("result")
            .and_then(|result| result.get("data"))
            .is_some_and(Value::is_array),
        "semantic tokens must remain available for an invalid policy: {response}"
    );

    let unrelated_conventional =
        workspace.write("policies/actions.cedarschema", INVALID_POLICY_SCHEMA);
    watched(&mut server, &uri(&unrelated_conventional), 1);
    barrier(&mut server, 3);
    server.assert_no_queued_notifications();

    server.send_notification(
        "textDocument/didClose",
        Some(json!({"textDocument": {"uri": policy_uri}})),
    );
    barrier(&mut server, 4);
    server.expect_notification(
        PUBLISH_DIAGNOSTICS,
        json!({"uri": policy_uri, "version": 4, "diagnostics": []}),
    );

    server.send_notification(
        "workspace/didChangeWatchedFiles",
        Some(json!({"changes": [{
            "uri": workspace.uri("config/schema.cedarschema"),
            "type": 2
        }]})),
    );
    barrier(&mut server, 5);
    server.assert_no_queued_notifications();
    shutdown(server, 6);
}

#[test]
fn dynamic_client_registers_exact_watchers_and_watched_change_revalidates() {
    let workspace = Workspace::new();
    let nested = workspace.path("nested");
    fs::create_dir_all(&nested).unwrap();
    let outside = Workspace::new();
    let action_path = outside.write("schema.txt", ALL_OPTIONAL_SCHEMA);
    let event_path = outside.write("events.input", ALL_OPTIONAL_EVENTS);
    let providers_path = outside.write("providers.data", ALL_OPTIONAL_PROVIDERS);
    let macros_path = outside.write("macros.source", ALL_OPTIONAL_MACROS);
    let explicit_paths = [
        action_path.clone(),
        event_path.clone(),
        providers_path.clone(),
        macros_path.clone(),
    ];
    let root_uri = workspace.root_uri();
    let nested_uri = uri(&nested);
    let policy_uri = workspace.uri("policy.dw");
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {
                "workspace": {
                    "didChangeWatchedFiles": {
                        "dynamicRegistration": true,
                        "relativePatternSupport": true
                    }
                }
            },
            "workspaceFolders": [
                {"uri": root_uri, "name": "root"},
                {"uri": nested_uri, "name": "nested"}
            ],
            "initializationOptions": {
                "bundles": [
                    {
                        "workspaceFolder": root_uri,
                        "actionSchema": action_path.to_string_lossy(),
                        "eventSchema": event_path.to_string_lossy(),
                        "providers": providers_path.to_string_lossy(),
                        "macros": macros_path.to_string_lossy()
                    },
                    {
                        "workspaceFolder": nested_uri,
                        "actionSchema": action_path.to_string_lossy(),
                        "eventSchema": event_path.to_string_lossy(),
                        "providers": providers_path.to_string_lossy(),
                        "macros": macros_path.to_string_lossy()
                    }
                ]
            }
        }),
    );

    let registration = server.receive_server_request(REGISTER_CAPABILITY);
    assert_eq!(
        registration,
        json!({
            "jsonrpc": "2.0",
            "id": WATCH_REGISTRATION_REQUEST_ID,
            "method": REGISTER_CAPABILITY,
            "params": {
                "registrations": [{
                    "id": WATCH_REGISTRATION_ID,
                    "method": "workspace/didChangeWatchedFiles",
                    "registerOptions": {
                        "watchers": expected_external_watchers(&workspace.root, &explicit_paths)
                    }
                }]
            }
        })
    );

    open(&mut server, &policy_uri, 8, ALL_OPTIONAL_POLICY);
    assert_external_watch_diagnostic(&publication_after_barrier(&mut server, 1), &policy_uri, 8);
    server.assert_no_queued_server_messages();

    server.send_success_response(
        Value::String(WATCH_REGISTRATION_REQUEST_ID.to_owned()),
        Value::Null,
    );
    assert_empty_publication(&publication_after_barrier(&mut server, 2), &policy_uri, 8);
    server.assert_no_queued_server_messages();

    fs::write(&providers_path, "{").unwrap();
    watched(&mut server, &uri(&providers_path), 2);
    assert_nonempty_publication(&publication_after_barrier(&mut server, 3), &policy_uri, 8);
    server.assert_no_queued_server_messages();

    shutdown(server, 4);
}

#[test]
fn unanswered_registration_keeps_external_bundle_non_clean_but_not_internal_bundle() {
    let internal = Workspace::new();
    let explicit = Workspace::new();
    let outside = Workspace::new();
    internal.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let external_action = outside.write("schema.txt", VALID_ACTION_SCHEMA);
    let internal_policy_uri = internal.uri("policy.dw");
    let external_policy_uri = explicit.uri("policy.dw");
    let explicit_root_uri = explicit.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {
                "workspace": {
                    "didChangeWatchedFiles": {
                        "dynamicRegistration": true,
                        "relativePatternSupport": true
                    }
                }
            },
            "workspaceFolders": [
                {"uri": internal.root_uri(), "name": "internal"},
                {"uri": explicit_root_uri, "name": "explicit"}
            ],
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": explicit_root_uri,
                    "actionSchema": external_action.to_string_lossy()
                }]
            }
        }),
    );

    let registration = server.receive_server_request(REGISTER_CAPABILITY);
    assert_eq!(registration["id"], WATCH_REGISTRATION_REQUEST_ID);

    open(&mut server, &internal_policy_uri, 3, VALID_POLICY);
    assert_empty_publication(
        &publication_after_barrier(&mut server, 1),
        &internal_policy_uri,
        3,
    );
    open(&mut server, &external_policy_uri, 4, VALID_POLICY);
    assert_external_watch_diagnostic(
        &publication_after_barrier(&mut server, 2),
        &external_policy_uri,
        4,
    );

    fs::write(&external_action, "!").unwrap();
    watched(&mut server, &uri(&external_action), 2);
    assert_external_watch_diagnostic(
        &publication_after_barrier(&mut server, 3),
        &external_policy_uri,
        4,
    );
    server.assert_no_queued_server_messages();

    shutdown(server, 4);
}

#[test]
fn absent_or_false_dynamic_registration_fails_closed_external_bundles() {
    for dynamic_registration in [None, Some(false)] {
        let internal = Workspace::new();
        let explicit = Workspace::new();
        let outside = Workspace::new();
        let internal_action = internal.write("actions.cedarschema", VALID_ACTION_SCHEMA);
        let external_action = outside.write("schema.txt", VALID_ACTION_SCHEMA);
        let internal_policy_uri = internal.uri("policy.dw");
        let external_policy_uri = explicit.uri("policy.dw");
        let external_action_uri = uri(&external_action);
        let explicit_root_uri = explicit.root_uri();
        let capabilities = dynamic_registration.map_or_else(
            || json!({}),
            |value| {
                json!({
                    "workspace": {
                        "didChangeWatchedFiles": {
                            "dynamicRegistration": value
                        }
                    }
                })
            },
        );
        let mut server = LspProcess::spawn_with_test_control();
        initialize(
            &mut server,
            0,
            json!({
                "capabilities": capabilities,
                "workspaceFolders": [
                    {"uri": internal.root_uri(), "name": "internal"},
                    {"uri": explicit_root_uri, "name": "explicit"}
                ],
                "initializationOptions": {
                    "bundles": [{
                        "workspaceFolder": explicit_root_uri,
                        "actionSchema": external_action.to_string_lossy()
                    }]
                }
            }),
        );

        barrier(&mut server, 1);
        server.assert_no_queued_server_messages();

        open(&mut server, &internal_policy_uri, 3, VALID_POLICY);
        assert_empty_publication(
            &publication_after_barrier(&mut server, 2),
            &internal_policy_uri,
            3,
        );
        server.assert_no_queued_server_messages();

        open(&mut server, &external_policy_uri, 7, VALID_POLICY);
        assert_external_watch_diagnostic(
            &publication_after_barrier(&mut server, 3),
            &external_policy_uri,
            7,
        );
        server.assert_no_queued_server_messages();

        open(&mut server, &external_action_uri, 1, "!");
        assert_external_watch_diagnostic(
            &publication_after_barrier(&mut server, 4),
            &external_policy_uri,
            7,
        );
        change(&mut server, &external_action_uri, 2, VALID_ACTION_SCHEMA);
        assert_external_watch_diagnostic(
            &publication_after_barrier(&mut server, 5),
            &external_policy_uri,
            7,
        );
        server.send_notification(
            "textDocument/didClose",
            Some(json!({"textDocument": {"uri": external_action_uri}})),
        );
        assert_external_watch_diagnostic(
            &publication_after_barrier(&mut server, 6),
            &external_policy_uri,
            7,
        );
        server.assert_no_queued_server_messages();

        fs::write(&internal_action, "!").unwrap();
        watched(&mut server, &uri(&internal_action), 2);
        assert_nonempty_publication(
            &publication_after_barrier(&mut server, 7),
            &internal_policy_uri,
            3,
        );
        server.assert_no_queued_server_messages();

        shutdown(server, 8);
    }
}

#[test]
fn missing_or_false_relative_pattern_support_fails_closed_external_bundles() {
    for relative_pattern_support in [None, Some(false)] {
        let internal = Workspace::new();
        let explicit = Workspace::new();
        let outside = Workspace::new();
        internal.write("actions.cedarschema", VALID_ACTION_SCHEMA);
        let external_action = outside.write("schema.txt", VALID_ACTION_SCHEMA);
        let internal_policy_uri = internal.uri("policy.dw");
        let external_policy_uri = explicit.uri("policy.dw");
        let explicit_root_uri = explicit.root_uri();
        let mut watched_capability =
            serde_json::Map::from_iter([("dynamicRegistration".to_owned(), Value::Bool(true))]);
        if let Some(value) = relative_pattern_support {
            watched_capability.insert("relativePatternSupport".to_owned(), Value::Bool(value));
        }
        let mut server = LspProcess::spawn_with_test_control();
        initialize(
            &mut server,
            0,
            json!({
                "capabilities": {
                    "workspace": {
                        "didChangeWatchedFiles": Value::Object(watched_capability)
                    }
                },
                "workspaceFolders": [
                    {"uri": internal.root_uri(), "name": "internal"},
                    {"uri": explicit_root_uri, "name": "explicit"}
                ],
                "initializationOptions": {
                    "bundles": [{
                        "workspaceFolder": explicit_root_uri,
                        "actionSchema": external_action.to_string_lossy()
                    }]
                }
            }),
        );

        let registration = server.receive_server_request(REGISTER_CAPABILITY);
        assert_eq!(registration["id"], WATCH_REGISTRATION_REQUEST_ID);
        let watchers = registration["params"]["registrations"][0]["registerOptions"]["watchers"]
            .as_array()
            .expect("watchers must be an array");
        assert!(
            watchers
                .iter()
                .all(|watcher| watcher["globPattern"].is_string()),
            "unsupported relative patterns must not be registered: {registration}"
        );
        server.send_success_response(
            Value::String(WATCH_REGISTRATION_REQUEST_ID.to_owned()),
            Value::Null,
        );

        open(&mut server, &internal_policy_uri, 2, VALID_POLICY);
        assert_empty_publication(
            &publication_after_barrier(&mut server, 1),
            &internal_policy_uri,
            2,
        );
        open(&mut server, &external_policy_uri, 9, VALID_POLICY);
        assert_external_watch_diagnostic(
            &publication_after_barrier(&mut server, 2),
            &external_policy_uri,
            9,
        );
        server.assert_no_queued_server_messages();

        shutdown(server, 3);
    }
}

#[test]
fn registration_error_fails_closed_external_bundle_and_unmatched_response_is_ignored() {
    let workspace = Workspace::new();
    let outside = Workspace::new();
    let external_action = outside.write("schema.txt", VALID_ACTION_SCHEMA);
    let policy_uri = workspace.uri("policy.dw");
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {
                "workspace": {
                    "didChangeWatchedFiles": {
                        "dynamicRegistration": true,
                        "relativePatternSupport": true
                    }
                }
            },
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": external_action.to_string_lossy()
                }]
            }
        }),
    );

    let registration = server.receive_server_request(REGISTER_CAPABILITY);
    assert_eq!(registration["id"], WATCH_REGISTRATION_REQUEST_ID);

    open(&mut server, &policy_uri, 12, VALID_POLICY);
    assert_external_watch_diagnostic(&publication_after_barrier(&mut server, 1), &policy_uri, 12);
    server.assert_no_queued_server_messages();

    server.send_error_response(
        Value::String(WATCH_REGISTRATION_REQUEST_ID.to_owned()),
        -32000,
        "watch registration denied",
    );
    server.send_success_response(Value::from(999), Value::Null);
    barrier(&mut server, 2);
    server.assert_no_queued_server_messages();
    server.assert_running();

    fs::write(&external_action, "!").unwrap();
    watched(&mut server, &uri(&external_action), 2);
    assert_external_watch_diagnostic(&publication_after_barrier(&mut server, 3), &policy_uri, 12);
    server.assert_no_queued_server_messages();

    server.send_request(4, "shutdown", None);
    server.expect_response(4, json!({"jsonrpc": "2.0", "id": 4, "result": null}));
    server.send_notification("exit", None);
    server.finish_with_stderr_fragments(
        0,
        &[
            "client/registerCapability failed with code -32000: watch registration denied",
            "ignoring unexpected client response: 999",
        ],
    );
}

#[test]
fn non_null_registration_response_keeps_external_bundle_non_clean() {
    let workspace = Workspace::new();
    let outside = Workspace::new();
    let external_action = outside.write("schema.txt", VALID_ACTION_SCHEMA);
    let policy_uri = workspace.uri("policy.dw");
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {
                "workspace": {
                    "didChangeWatchedFiles": {
                        "dynamicRegistration": true,
                        "relativePatternSupport": true
                    }
                }
            },
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": external_action.to_string_lossy()
                }]
            }
        }),
    );

    let registration = server.receive_server_request(REGISTER_CAPABILITY);
    assert_eq!(registration["id"], WATCH_REGISTRATION_REQUEST_ID);
    open(&mut server, &policy_uri, 13, VALID_POLICY);
    assert_external_watch_diagnostic(&publication_after_barrier(&mut server, 1), &policy_uri, 13);

    server.send_success_response(
        Value::String(WATCH_REGISTRATION_REQUEST_ID.to_owned()),
        json!({}),
    );
    barrier(&mut server, 2);
    server.assert_no_queued_server_messages();

    fs::write(&external_action, "!").unwrap();
    watched(&mut server, &uri(&external_action), 2);
    assert_external_watch_diagnostic(&publication_after_barrier(&mut server, 3), &policy_uri, 13);

    server.send_request(4, "shutdown", None);
    server.expect_response(4, json!({"jsonrpc": "2.0", "id": 4, "result": null}));
    server.send_notification("exit", None);
    server.finish_with_stderr(
        0,
        "client/registerCapability returned an unexpected non-null result",
    );
}

#[test]
fn nonexistent_external_dependency_remains_load_error_and_recovers_on_watched_creation() {
    let workspace = Workspace::new();
    let outside = Workspace::new();
    let missing = outside.path("future/schema.txt");
    let policy_uri = workspace.uri("policy.dw");
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {
                "workspace": {
                    "didChangeWatchedFiles": {
                        "dynamicRegistration": true,
                        "relativePatternSupport": true
                    }
                }
            },
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": missing.to_string_lossy()
                }]
            }
        }),
    );
    accept_watch_registration(&mut server);

    open(&mut server, &policy_uri, 14, VALID_POLICY);
    let missing_publication = publication_after_barrier(&mut server, 1);
    assert_server_diagnostic(
        &missing_publication,
        &policy_uri,
        14,
        "dogwood.input",
        "action schema does not exist",
    );

    outside.write("future/schema.txt", VALID_ACTION_SCHEMA);
    watched(&mut server, &uri(&missing), 1);
    assert_empty_publication(&publication_after_barrier(&mut server, 2), &policy_uri, 14);
    server.assert_no_queued_server_messages();

    shutdown(server, 3);
}

#[cfg(unix)]
#[test]
fn conventional_discovery_reports_missing_unreadable_non_utf8_and_watched_recovery() {
    use std::os::unix::fs::PermissionsExt;

    let workspace = Workspace::new();
    let policy_path = workspace.write("policy.dw", VALID_POLICY);
    let policy_uri = uri(&policy_path);
    let action_path = workspace.path("actions.cedarschema");
    let action_uri = uri(&action_path);
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 1, VALID_POLICY);
    let missing = publication_after_barrier(&mut server, 1);
    assert_server_diagnostic(
        &missing,
        &policy_uri,
        1,
        "dogwood.project",
        "no `.cedarschema` action schema was found",
    );

    fs::write(&action_path, VALID_ACTION_SCHEMA).unwrap();
    fs::set_permissions(&action_path, fs::Permissions::from_mode(0o000)).unwrap();
    watched(&mut server, &action_uri, 1);
    let unreadable = publication_after_barrier(&mut server, 2);
    assert_server_diagnostic(
        &unreadable,
        &policy_uri,
        1,
        "dogwood.input",
        "action schema is not readable",
    );

    fs::set_permissions(&action_path, fs::Permissions::from_mode(0o600)).unwrap();
    fs::write(&action_path, [0xff, 0xfe]).unwrap();
    watched(&mut server, &action_uri, 2);
    let non_utf8 = publication_after_barrier(&mut server, 3);
    assert_server_diagnostic(
        &non_utf8,
        &policy_uri,
        1,
        "dogwood.input",
        "action schema is not valid UTF-8",
    );

    fs::write(
        &action_path,
        vec![b' '; dogwood_lsp::frontend::MAX_FRONTEND_SOURCE_BYTES + 1],
    )
    .unwrap();
    watched(&mut server, &action_uri, 2);
    let oversized = publication_after_barrier(&mut server, 4);
    assert_server_diagnostic(
        &oversized,
        &policy_uri,
        1,
        "dogwood.input",
        "exceeds the 1048576-byte source limit",
    );

    fs::write(&action_path, VALID_ACTION_SCHEMA).unwrap();
    watched(&mut server, &action_uri, 2);
    assert_empty_publication(&publication_after_barrier(&mut server, 5), &policy_uri, 1);

    fs::remove_file(&action_path).unwrap();
    watched(&mut server, &action_uri, 3);
    let deleted = publication_after_barrier(&mut server, 6);
    assert_server_diagnostic(
        &deleted,
        &policy_uri,
        1,
        "dogwood.project",
        "no `.cedarschema` action schema was found",
    );

    shutdown(server, 7);
}

#[test]
fn arbitrary_conventional_schema_name_revalidates_on_ambiguity_and_recovery() {
    let workspace = Workspace::new();
    workspace.write("schema.cedarschema", VALID_ACTION_SCHEMA);
    let policy_uri = workspace.uri("policy.dw");
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 1, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 1), &policy_uri, 1);

    let second_path = workspace.write("other.cedarschema", VALID_ACTION_SCHEMA);
    let second_uri = uri(&second_path);
    watched(&mut server, &second_uri, 1);
    let ambiguous = publication_after_barrier(&mut server, 2);
    assert_server_diagnostic(
        &ambiguous,
        &policy_uri,
        1,
        "dogwood.project",
        "multiple `.cedarschema` action schemas",
    );

    fs::remove_file(second_path).unwrap();
    watched(&mut server, &second_uri, 3);
    assert_empty_publication(&publication_after_barrier(&mut server, 3), &policy_uri, 1);

    workspace.write("actions.cedarschema", "!");
    watched(&mut server, &workspace.uri("actions.cedarschema"), 1);
    let preferred = publication_after_barrier(&mut server, 4);
    assert_nonempty_publication(&preferred, &policy_uri, 1);

    shutdown(server, 5);
}

#[test]
fn deepest_workspace_and_nearest_ancestor_take_precedence_with_optional_defaults() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", "!");
    let nested = workspace.path("nested");
    fs::create_dir_all(nested.join("policies/deeper")).unwrap();
    fs::write(nested.join("actions.cedarschema"), VALID_ACTION_SCHEMA).unwrap();
    let policy_path = nested.join("policies/deeper/policy.dw");
    fs::write(&policy_path, VALID_POLICY).unwrap();
    let policy_uri = uri(&policy_path);
    let root_uri = workspace.root_uri();
    let nested_uri = uri(&nested);
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {},
            "workspaceFolders": [
                {"uri": root_uri, "name": "root"},
                {"uri": nested_uri, "name": "nested"}
            ]
        }),
    );
    open(&mut server, &policy_uri, 1, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 1), &policy_uri, 1);
    shutdown(server, 2);
}

#[test]
fn ordinary_nested_policy_named_macros_dw_publishes_and_clears_diagnostics() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let policy_uri = workspace.uri("nested/macros.dw");
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 7, "permit (");
    let publication = publication_after_barrier(&mut server, 1);
    assert_eq!(publication["uri"], policy_uri);
    assert_eq!(publication["version"], 7);
    assert!(
        publication["diagnostics"]
            .as_array()
            .is_some_and(|diagnostics| !diagnostics.is_empty()),
        "an ordinary policy named macros.dw must be validated: {publication}"
    );

    server.send_notification(
        "textDocument/didClose",
        Some(json!({"textDocument": {"uri": policy_uri}})),
    );
    assert_empty_publication(&publication_after_barrier(&mut server, 2), &policy_uri, 7);

    watched(&mut server, &workspace.uri("actions.cedarschema"), 2);
    barrier(&mut server, 3);
    server.assert_no_queued_notifications();
    shutdown(server, 4);
}

#[test]
fn policy_role_is_cleared_when_open_dw_becomes_a_dependency_and_close_uses_disk() {
    let workspace = Workspace::new();
    let outside = Workspace::new();
    workspace.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let macro_path = outside.write("macros.dw", "def cedar broken(");
    let macro_uri = uri(&macro_path);
    let policy_uri = workspace.uri("policy.dw");
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {
                "workspace": {
                    "didChangeWatchedFiles": {
                        "dynamicRegistration": true,
                        "relativePatternSupport": true
                    }
                }
            },
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "actions.cedarschema",
                    "macros": macro_path.to_string_lossy()
                }]
            }
        }),
    );
    accept_watch_registration(&mut server);

    open(&mut server, &macro_uri, 5, ALL_OPTIONAL_MACROS);
    let macro_policy = publication_after_barrier(&mut server, 1);
    assert_server_diagnostic(
        &macro_policy,
        &macro_uri,
        5,
        "dogwood.project",
        "outside every configured workspace",
    );
    server.assert_no_queued_notifications();

    open(&mut server, &policy_uri, 9, VALID_POLICY);
    barrier(&mut server, 2);
    let cleared_macro = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    let clean_policy = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    assert_empty_publication(&cleared_macro, &macro_uri, 5);
    assert_empty_publication(&clean_policy, &policy_uri, 9);
    server.assert_no_queued_notifications();

    server.send_notification(
        "textDocument/didClose",
        Some(json!({"textDocument": {"uri": macro_uri}})),
    );
    let invalid_policy = publication_after_barrier(&mut server, 3);
    assert_nonempty_publication(&invalid_policy, &policy_uri, 9);
    server.assert_no_queued_notifications();

    shutdown(server, 4);
}

#[test]
fn dependency_role_promotes_open_dw_to_policy_after_last_dependent_closes() {
    let workspace = Workspace::new();
    let outside = Workspace::new();
    workspace.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let macro_path = outside.write("macros.dw", ALL_OPTIONAL_MACROS);
    let macro_uri = uri(&macro_path);
    let policy_uri = workspace.uri("policy.dw");
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {
                "workspace": {
                    "didChangeWatchedFiles": {
                        "dynamicRegistration": true,
                        "relativePatternSupport": true
                    }
                }
            },
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "actions.cedarschema",
                    "macros": macro_path.to_string_lossy()
                }]
            }
        }),
    );
    accept_watch_registration(&mut server);

    open(&mut server, &policy_uri, 11, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 1), &policy_uri, 11);
    server.assert_no_queued_notifications();

    open(&mut server, &macro_uri, 4, "def cedar broken(");
    let invalid_policy = publication_after_barrier(&mut server, 2);
    assert_nonempty_publication(&invalid_policy, &policy_uri, 11);
    server.assert_no_queued_notifications();

    server.send_notification(
        "textDocument/didClose",
        Some(json!({"textDocument": {"uri": policy_uri}})),
    );
    barrier(&mut server, 3);
    let cleared_policy = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    let promoted_macro = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    assert_empty_publication(&cleared_policy, &policy_uri, 11);
    assert_server_diagnostic(
        &promoted_macro,
        &macro_uri,
        4,
        "dogwood.project",
        "outside every configured workspace",
    );
    server.assert_no_queued_notifications();

    server.send_notification(
        "textDocument/didClose",
        Some(json!({"textDocument": {"uri": macro_uri}})),
    );
    assert_empty_publication(&publication_after_barrier(&mut server, 4), &macro_uri, 4);
    server.assert_no_queued_notifications();

    shutdown(server, 5);
}

#[test]
fn arbitrary_explicit_dependency_uses_open_changes_then_falls_back_to_disk() {
    let workspace = Workspace::new();
    workspace.write("schema.txt", VALID_ACTION_SCHEMA);
    let schema_uri = workspace.uri("schema.txt");
    let policy_uri = workspace.uri("policy.dw");
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "schema.txt"
                }]
            }
        }),
    );

    open(&mut server, &policy_uri, 17, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 1), &policy_uri, 17);
    server.assert_no_queued_notifications();

    open(&mut server, &schema_uri, 2, "!");
    let invalid_open = publication_after_barrier(&mut server, 2);
    assert_nonempty_publication(&invalid_open, &policy_uri, 17);
    server.assert_no_queued_notifications();

    change(&mut server, &schema_uri, 3, VALID_ACTION_SCHEMA);
    assert_empty_publication(&publication_after_barrier(&mut server, 3), &policy_uri, 17);
    server.assert_no_queued_notifications();

    change(&mut server, &schema_uri, 4, "!");
    let invalid_change = publication_after_barrier(&mut server, 4);
    assert_nonempty_publication(&invalid_change, &policy_uri, 17);
    server.assert_no_queued_notifications();

    server.send_notification(
        "textDocument/didClose",
        Some(json!({"textDocument": {"uri": schema_uri}})),
    );
    assert_empty_publication(&publication_after_barrier(&mut server, 5), &policy_uri, 17);
    server.assert_no_queued_notifications();

    shutdown(server, 6);
}

#[test]
fn policy_valid_invalid_valid_sequence_uses_current_versions() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", INVALID_POLICY_SCHEMA);
    let policy_path = workspace.write("policy.dw", "");
    let policy_uri = uri(&policy_path);
    let valid = "permit (principal, action == Drupe::Action::\"Read\", resource);";
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 1, valid);
    assert_empty_publication(&publication_after_barrier(&mut server, 1), &policy_uri, 1);

    change(&mut server, &policy_uri, 2, "permit (");
    let invalid = publication_after_barrier(&mut server, 2);
    assert_eq!(invalid["uri"], policy_uri);
    assert_eq!(invalid["version"], 2);
    assert!(
        invalid["diagnostics"]
            .as_array()
            .is_some_and(|diagnostics| !diagnostics.is_empty())
    );

    server.send_request(
        3,
        "textDocument/semanticTokens/full",
        Some(json!({"textDocument": {"uri": policy_uri}})),
    );
    assert!(server.receive_response(3).get("result").is_some());

    change(&mut server, &policy_uri, 3, valid);
    assert_empty_publication(&publication_after_barrier(&mut server, 4), &policy_uri, 3);
    shutdown(server, 5);
}

#[test]
fn every_dependency_kind_revalidates_from_open_memory_change_and_close_to_disk() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", ALL_OPTIONAL_SCHEMA);
    workspace.write("events.dwschema", ALL_OPTIONAL_EVENTS);
    workspace.write("providers.json", ALL_OPTIONAL_PROVIDERS);
    workspace.write("macros.dw", ALL_OPTIONAL_MACROS);
    let policy_path = workspace.write("policy.dw", ALL_OPTIONAL_POLICY);
    let policy_uri = uri(&policy_path);
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 1, ALL_OPTIONAL_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 1), &policy_uri, 1);

    let dependencies = [
        ("actions.cedarschema", "!", ALL_OPTIONAL_SCHEMA),
        (
            "events.dwschema",
            "decision event <A>::attempt {",
            ALL_OPTIONAL_EVENTS,
        ),
        ("providers.json", "{", ALL_OPTIONAL_PROVIDERS),
        ("macros.dw", "def cedar broken(", ALL_OPTIONAL_MACROS),
    ];
    let mut request_id = 2;
    for (relative, invalid, valid) in dependencies {
        let dependency_uri = workspace.uri(relative);
        open(&mut server, &dependency_uri, 1, invalid);
        barrier(&mut server, request_id);
        request_id += 1;
        if relative == "events.dwschema" {
            let schema = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
            assert_nonempty_publication(&schema, &dependency_uri, 1);
        }
        let publication = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
        assert_eq!(publication["uri"], policy_uri);
        assert_eq!(publication["version"], 1);
        assert!(
            publication["diagnostics"]
                .as_array()
                .is_some_and(|diagnostics| !diagnostics.is_empty()),
            "{relative} invalidation must publish a finding: {publication}"
        );

        change(&mut server, &dependency_uri, 2, valid);
        barrier(&mut server, request_id);
        request_id += 1;
        if relative == "events.dwschema" {
            let schema = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
            assert_empty_publication(&schema, &dependency_uri, 2);
        }
        let policy = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
        assert_empty_publication(&policy, &policy_uri, 1);

        server.send_notification(
            "textDocument/didClose",
            Some(json!({"textDocument": {"uri": dependency_uri}})),
        );
        barrier(&mut server, request_id);
        request_id += 1;
        if relative == "events.dwschema" {
            let schema = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
            assert_empty_publication(&schema, &dependency_uri, 2);
        }
        let policy = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
        assert_empty_publication(&policy, &policy_uri, 1);
    }

    shutdown(server, request_id);
}

#[test]
fn watched_optional_conventional_inputs_revalidate_on_creation_and_deletion() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let policy_uri = workspace.uri("policy.dw");
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 1, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 1), &policy_uri, 1);

    let optional_inputs = [
        ("events.dwschema", "decision event <A>::request {"),
        ("providers.json", "{"),
        ("macros.dw", "def cedar broken("),
    ];
    let mut request_id = 2;
    for (relative, invalid) in optional_inputs {
        let path = workspace.write(relative, invalid);
        watched(&mut server, &uri(&path), 1);
        let created = publication_after_barrier(&mut server, request_id);
        request_id += 1;
        assert_eq!(created["uri"], policy_uri);
        assert!(
            created["diagnostics"]
                .as_array()
                .is_some_and(|diagnostics| !diagnostics.is_empty()),
            "creating invalid {relative} must invalidate the policy: {created}"
        );

        fs::remove_file(&path).unwrap();
        watched(&mut server, &uri(&path), 3);
        assert_empty_publication(
            &publication_after_barrier(&mut server, request_id),
            &policy_uri,
            1,
        );
        request_id += 1;
    }

    shutdown(server, request_id);
}

#[test]
fn watched_batch_publishes_only_final_state_when_policy_becomes_dependency() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let macro_uri = workspace.uri("nested/macros.dw");
    let policy_uri = workspace.uri("nested/z.dw");
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &macro_uri, 6, "permit (");
    assert_nonempty_publication(&publication_after_barrier(&mut server, 1), &macro_uri, 6);
    server.assert_no_queued_notifications();

    open(&mut server, &policy_uri, 7, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 2), &policy_uri, 7);
    server.assert_no_queued_notifications();

    let nearer = workspace.write("nested/actions.cedarschema", VALID_ACTION_SCHEMA);
    watched(&mut server, &uri(&nearer), 1);
    barrier(&mut server, 3);
    let cleared_macro = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    let invalid_policy = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    assert_empty_publication(&cleared_macro, &macro_uri, 6);
    assert_nonempty_publication(&invalid_policy, &policy_uri, 7);
    server.assert_no_queued_notifications();

    shutdown(server, 4);
}

#[test]
fn watched_nearer_action_schema_creation_and_deletion_revalidates_all_policies_in_order() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let first_uri = workspace.uri("nested/a.dw");
    let second_uri = workspace.uri("nested/z.dw");
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &second_uri, 3, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 1), &second_uri, 3);
    open(&mut server, &first_uri, 4, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 2), &first_uri, 4);

    let nearer = workspace.write("nested/actions.cedarschema", "!");
    watched(&mut server, &uri(&nearer), 1);
    barrier(&mut server, 3);
    let first = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    let second = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    assert_eq!(first["uri"], first_uri);
    assert_eq!(first["version"], 4);
    assert_eq!(second["uri"], second_uri);
    assert_eq!(second["version"], 3);
    assert!(!first["diagnostics"].as_array().unwrap().is_empty());
    assert!(!second["diagnostics"].as_array().unwrap().is_empty());

    fs::remove_file(&nearer).unwrap();
    watched(&mut server, &uri(&nearer), 3);
    barrier(&mut server, 4);
    let first = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    let second = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    assert_empty_publication(&first, &first_uri, 4);
    assert_empty_publication(&second, &second_uri, 3);

    shutdown(server, 5);
}

#[cfg(unix)]
#[test]
fn conventional_symlinks_outside_workspace_are_diagnostic_for_required_and_optional_inputs() {
    use std::os::unix::fs::symlink;

    let workspace = Workspace::new();
    let outside = Workspace::new();
    let external_action = outside.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    symlink(&external_action, workspace.path("actions.cedarschema")).unwrap();
    let policy_uri = workspace.uri("policy.dw");
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 1, VALID_POLICY);
    let required = publication_after_barrier(&mut server, 1);
    assert_server_diagnostic(
        &required,
        &policy_uri,
        1,
        "dogwood.project",
        "symlink resolves outside the workspace",
    );
    shutdown(server, 2);

    let workspace = Workspace::new();
    let outside = Workspace::new();
    workspace.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let external_providers = outside.write("providers.json", r#"{"availableProviders": {}}"#);
    symlink(&external_providers, workspace.path("providers.json")).unwrap();
    let policy_uri = workspace.uri("policy.dw");
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 1, VALID_POLICY);
    let optional = publication_after_barrier(&mut server, 1);
    assert_server_diagnostic(
        &optional,
        &policy_uri,
        1,
        "dogwood.project",
        "symlink resolves outside the workspace",
    );
    shutdown(server, 2);
}

#[test]
fn explicit_relative_paths_accept_contained_parent_components_and_reject_escapes() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let policy_uri = workspace.uri("policy.dw");
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "config/../actions.cedarschema"
                }]
            }
        }),
    );

    open(&mut server, &policy_uri, 1, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 1), &policy_uri, 1);
    shutdown(server, 2);

    let workspace = Workspace::new();
    let outside = Workspace::new();
    outside.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let outside_name = outside.root.file_name().unwrap().to_str().unwrap();
    let configured = format!("../{outside_name}/actions.cedarschema");
    let policy_uri = workspace.uri("policy.dw");
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": configured
                }]
            }
        }),
    );

    open(&mut server, &policy_uri, 1, VALID_POLICY);
    let escaped = publication_after_barrier(&mut server, 1);
    assert_server_diagnostic(&escaped, &policy_uri, 1, "dogwood.project", "escapes");
    shutdown(server, 2);
}

#[cfg(unix)]
#[test]
fn explicit_relative_symlink_escape_is_a_process_diagnostic() {
    use std::os::unix::fs::symlink;

    let workspace = Workspace::new();
    let outside = Workspace::new();
    outside.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    symlink(&outside.root, workspace.path("config")).unwrap();
    let policy_uri = workspace.uri("policy.dw");
    let root_uri = workspace.root_uri();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "config/actions.cedarschema"
                }]
            }
        }),
    );

    open(&mut server, &policy_uri, 1, VALID_POLICY);
    let publication = publication_after_barrier(&mut server, 1);
    assert_server_diagnostic(
        &publication,
        &policy_uri,
        1,
        "dogwood.project",
        "symlink resolves outside the workspace",
    );
    shutdown(server, 2);
}

#[cfg(unix)]
#[test]
fn explicit_absolute_file_and_parent_symlink_aliases_fail_closed() {
    use std::os::unix::fs::symlink;

    for parent_alias in [false, true] {
        let workspace = Workspace::new();
        let outside = Workspace::new();
        let target = outside.write("schema.txt", VALID_ACTION_SCHEMA);
        let alias = if parent_alias {
            let parent = workspace.path("external-parent");
            symlink(&outside.root, &parent).unwrap();
            parent.join("schema.txt")
        } else {
            let alias = workspace.path("schema.txt");
            symlink(&target, &alias).unwrap();
            alias
        };
        let alias_uri = uri(&alias);
        let policy_uri = workspace.uri("policy.dw");
        let root_uri = workspace.root_uri();
        let mut server = LspProcess::spawn_with_test_control();
        initialize(
            &mut server,
            0,
            json!({
                "capabilities": {},
                "rootUri": root_uri,
                "initializationOptions": {
                    "bundles": [{
                        "workspaceFolder": root_uri,
                        "actionSchema": alias.to_string_lossy()
                    }]
                }
            }),
        );

        open(&mut server, &policy_uri, 21, VALID_POLICY);
        let publication = publication_after_barrier(&mut server, 1);
        assert_explicit_alias_diagnostic(
            &publication,
            &policy_uri,
            21,
            &alias,
            &alias_uri,
            &root_uri,
        );

        fs::write(&target, "!").unwrap();
        watched(&mut server, &uri(&target), 2);
        barrier(&mut server, 2);
        server.assert_no_queued_server_messages();

        change(&mut server, &policy_uri, 22, VALID_POLICY);
        let current = publication_after_barrier(&mut server, 3);
        assert_explicit_alias_diagnostic(&current, &policy_uri, 22, &alias, &alias_uri, &root_uri);
        server.assert_no_queued_server_messages();
        shutdown(server, 4);

        let symlink_path = if parent_alias {
            alias.parent().unwrap()
        } else {
            alias.as_path()
        };
        fs::remove_file(symlink_path).unwrap();
    }
}

#[test]
fn macro_source_finding_is_related_to_exact_dependency_range() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", MACRO_FAILURE_SCHEMA);
    workspace.write("macros.dw", MACRO_FAILURE_SOURCE);
    let policy_path = workspace.write("policy.dw", MACRO_FAILURE_POLICY);
    let policy_uri = uri(&policy_path);
    let macros_uri = workspace.uri("macros.dw");
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 8, MACRO_FAILURE_POLICY);
    barrier(&mut server, 1);
    server.expect_notification(
        PUBLISH_DIAGNOSTICS,
        json!({
            "uri": policy_uri,
            "version": 8,
            "diagnostics": [{
                "range": {
                    "start": {"line": 0, "character": 0},
                    "end": {"line": 0, "character": 0}
                },
                "severity": 1,
                "source": "dogwood",
                "message": "unexpected token `def`, expected end of input, macro definition, policy",
                "relatedInformation": [{
                    "location": {
                        "uri": macros_uri,
                        "range": {
                            "start": {"line": 1, "character": 0},
                            "end": {"line": 1, "character": 1}
                        }
                    },
                    "message": "unexpected token `def`, expected end of input, macro definition, policy"
                }]
            }]
        }),
    );
    shutdown(server, 2);
}

#[test]
fn validation_warning_is_nonempty_and_preserves_exact_warning_fields() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", WARNING_SCHEMA);
    let policy_path = workspace.write("policy.dw", WARNING_POLICY);
    let policy_uri = uri(&policy_path);
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 6, WARNING_POLICY);
    barrier(&mut server, 1);
    server.expect_notification(
        PUBLISH_DIAGNOSTICS,
        json!({
            "uri": policy_uri,
            "version": 6,
            "diagnostics": [{
                "range": {
                    "start": {"line": 2, "character": 29},
                    "end": {"line": 2, "character": 39}
                },
                "severity": 2,
                "source": "dogwood",
                "message": "for policy `policy_0`, string `\"pаssword\"` contains mixed scripts"
            }]
        }),
    );
    shutdown(server, 2);
}

#[test]
fn policy_outside_workspace_publishes_configuration_diagnostic_and_clears() {
    let workspace = Workspace::new();
    let outside = Workspace::new();
    let policy_uri = outside.uri("policy.dw");
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &policy_uri, 2, VALID_POLICY);
    let publication = publication_after_barrier(&mut server, 1);
    assert_server_diagnostic(
        &publication,
        &policy_uri,
        2,
        "dogwood.project",
        "outside every configured workspace folder",
    );

    server.send_notification(
        "textDocument/didClose",
        Some(json!({"textDocument": {"uri": policy_uri}})),
    );
    assert_empty_publication(&publication_after_barrier(&mut server, 2), &policy_uri, 2);
    shutdown(server, 3);
}

#[test]
fn one_dependency_change_revalidates_all_open_policies_in_path_order() {
    let workspace = Workspace::new();
    workspace.write("actions.cedarschema", VALID_ACTION_SCHEMA);
    let first_uri = workspace.uri("a.dw");
    let second_uri = workspace.uri("z.dw");
    let mut server = configured_server(&workspace, 0);

    open(&mut server, &second_uri, 3, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 1), &second_uri, 3);
    open(&mut server, &first_uri, 4, VALID_POLICY);
    assert_empty_publication(&publication_after_barrier(&mut server, 2), &first_uri, 4);

    let action_uri = workspace.uri("actions.cedarschema");
    open(&mut server, &action_uri, 1, "!");
    barrier(&mut server, 3);
    let first = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    let second = notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS));
    assert_eq!(first["uri"], first_uri);
    assert_eq!(first["version"], 4);
    assert_eq!(second["uri"], second_uri);
    assert_eq!(second["version"], 3);
    assert!(!first["diagnostics"].as_array().unwrap().is_empty());
    assert!(!second["diagnostics"].as_array().unwrap().is_empty());
    shutdown(server, 4);
}

#[test]
fn non_file_policy_and_ambiguous_explicit_configuration_are_diagnostic_states() {
    let workspace = Workspace::new();
    let root_uri = workspace.root_uri();
    let policy_uri = workspace.uri("policy.dw");
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        0,
        json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [
                    {"workspaceFolder": root_uri, "actionSchema": "one.cedarschema"},
                    {"workspaceFolder": root_uri, "actionSchema": "two.cedarschema"}
                ]
            }
        }),
    );

    open(&mut server, &policy_uri, 1, VALID_POLICY);
    let ambiguous = publication_after_barrier(&mut server, 1);
    assert_server_diagnostic(
        &ambiguous,
        &policy_uri,
        1,
        "dogwood.project",
        "at most one bundle entry",
    );

    let remote_uri = "https://example.com/policy.dw";
    open(&mut server, remote_uri, 9, VALID_POLICY);
    let remote = publication_after_barrier(&mut server, 2);
    assert_server_diagnostic(
        &remote,
        remote_uri,
        9,
        "dogwood.project",
        "not an unambiguous absolute file URI",
    );
    server.send_notification(
        "textDocument/didClose",
        Some(json!({"textDocument": {"uri": remote_uri}})),
    );
    assert_empty_publication(&publication_after_barrier(&mut server, 3), remote_uri, 9);
    shutdown(server, 4);
}

fn expected_external_watchers(workspace_root: &Path, explicit_paths: &[PathBuf]) -> Vec<Value> {
    let root = workspace_root.display();
    let mut patterns = vec![
        format!("{root}/**/*.cedarschema"),
        format!("{root}/**/events.dwschema"),
        format!("{root}/**/providers.json"),
        format!("{root}/**/macros.dw"),
    ];
    patterns.sort();
    patterns.dedup();
    let mut watchers: Vec<_> = patterns
        .into_iter()
        .map(|glob_pattern| json!({"globPattern": glob_pattern, "kind": 7}))
        .collect();

    let mut relative_patterns: Vec<_> = explicit_paths
        .iter()
        .map(|path| {
            (
                uri(path
                    .parent()
                    .expect("external test dependency has a parent")),
                path.file_name()
                    .and_then(|name| name.to_str())
                    .expect("external test dependency has a UTF-8 filename")
                    .to_owned(),
            )
        })
        .collect();
    relative_patterns.sort();
    relative_patterns.dedup();
    watchers.extend(relative_patterns.into_iter().map(|(base_uri, pattern)| {
        json!({
            "globPattern": {
                "baseUri": base_uri,
                "pattern": pattern
            },
            "kind": 7
        })
    }));
    watchers
}

fn accept_watch_registration(server: &mut LspProcess) {
    let registration = server.receive_server_request(REGISTER_CAPABILITY);
    assert_eq!(registration["id"], WATCH_REGISTRATION_REQUEST_ID);
    server.send_success_response(
        Value::String(WATCH_REGISTRATION_REQUEST_ID.to_owned()),
        Value::Null,
    );
}

fn configured_server(workspace: &Workspace, initialize_id: i64) -> LspProcess {
    let mut server = LspProcess::spawn_with_test_control();
    initialize(
        &mut server,
        initialize_id,
        json!({
            "capabilities": {},
            "rootUri": workspace.root_uri()
        }),
    );
    server
}

fn initialize(server: &mut LspProcess, id: i64, params: Value) {
    server.send_request(id, "initialize", Some(params));
    let response = server.receive_response(id);
    assert!(
        response.get("error").is_none(),
        "initialize failed: {response}"
    );
    assert_eq!(
        response["result"]["capabilities"]["positionEncoding"],
        "utf-16"
    );
    server.send_notification("initialized", Some(json!({})));
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
    server.expect_response(
        id,
        json!({
            "jsonrpc": "2.0",
            "id": id,
            "error": {"code": -32601, "message": "Method not found"}
        }),
    );
}

fn publication_after_barrier(server: &mut LspProcess, id: i64) -> Value {
    barrier(server, id);
    notification_params(server.receive_notification(PUBLISH_DIAGNOSTICS))
}

fn notification_params(notification: Value) -> Value {
    notification
        .get("params")
        .cloned()
        .expect("publishDiagnostics must contain params")
}

fn assert_empty_publication(publication: &Value, uri: &str, version: i32) {
    assert_eq!(
        publication,
        &json!({"uri": uri, "version": version, "diagnostics": []})
    );
}

fn assert_nonempty_publication(publication: &Value, uri: &str, version: i32) {
    assert_eq!(publication["uri"], uri);
    assert_eq!(publication["version"], version);
    assert!(
        publication["diagnostics"]
            .as_array()
            .is_some_and(|diagnostics| !diagnostics.is_empty()),
        "expected nonempty diagnostics: {publication}"
    );
}

fn assert_explicit_alias_diagnostic(
    publication: &Value,
    policy_uri: &str,
    version: i32,
    configured_path: &Path,
    configured_uri: &str,
    workspace_uri: &str,
) {
    let message = format!(
        "Dogwood project configuration error: action schema path `{}` for workspace \
         `{workspace_uri}` cannot be used: an existing path component resolves through a \
         symlink alias",
        configured_path.display()
    );
    assert_server_diagnostic(
        publication,
        policy_uri,
        version,
        "dogwood.project",
        &message,
    );
    assert_eq!(publication["diagnostics"][0]["message"], message);
    assert_eq!(
        publication["diagnostics"][0]["relatedInformation"],
        json!([{
            "location": {
                "uri": configured_uri,
                "range": {
                    "start": {"line": 0, "character": 0},
                    "end": {"line": 0, "character": 0}
                }
            },
            "message": "Dogwood project input location"
        }])
    );
}

fn assert_external_watch_diagnostic(publication: &Value, uri: &str, version: i32) {
    assert_server_diagnostic(
        publication,
        uri,
        version,
        "dogwood.project",
        EXTERNAL_WATCH_MESSAGE,
    );
    assert_eq!(
        publication["diagnostics"][0]["message"],
        EXTERNAL_WATCH_MESSAGE
    );
}

fn assert_server_diagnostic(
    publication: &Value,
    uri: &str,
    version: i32,
    code: &str,
    message_fragment: &str,
) {
    assert_eq!(publication["uri"], uri);
    assert_eq!(publication["version"], version);
    let diagnostics = publication["diagnostics"].as_array().unwrap();
    assert_eq!(diagnostics.len(), 1, "{publication}");
    assert_eq!(diagnostics[0]["severity"], 1);
    assert_eq!(diagnostics[0]["code"], code);
    assert_eq!(diagnostics[0]["source"], "dogwood");
    assert!(
        diagnostics[0]["message"]
            .as_str()
            .is_some_and(|message| message.contains(message_fragment)),
        "{publication}"
    );
}

fn shutdown(mut server: LspProcess, id: i64) {
    server.send_request(id, "shutdown", None);
    server.expect_response(id, json!({"jsonrpc": "2.0", "id": id, "result": null}));
    server.send_notification("exit", None);
    server.finish(0);
}

fn uri(path: &Path) -> String {
    path_to_file_uri(path)
        .expect("test path should convert to a file URI")
        .as_str()
        .to_owned()
}
