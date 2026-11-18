#![cfg(not(feature = "test-control"))]

#[path = "support/lsp_process.rs"]
mod lsp_process;

use std::fs;

use lsp_process::LspProcess;
use serde_json::json;

const HIDDEN_SURFACE: [&str; 5] = [
    "DOGWOOD_LSP_TEST_CONTROL",
    "dogwood/testBarrier",
    "dogwood-lsp/testControl",
    "dogwood-lsp/testReached",
    "dogwood-lsp/testWatchObserved",
];

#[test]
fn production_binary_omits_and_ignores_test_control() {
    let binary = env!("CARGO_BIN_EXE_dogwood-lsp");
    let artifact = fs::read(binary).expect("compiled server artifact should be readable");
    for hidden in HIDDEN_SURFACE {
        assert!(
            !artifact
                .windows(hidden.len())
                .any(|window| window == hidden.as_bytes()),
            "production server artifact contains hidden test-control surface {hidden:?}"
        );
    }

    let mut server = LspProcess::spawn_with_environment(&[("DOGWOOD_LSP_TEST_CONTROL", "1")]);
    server.send_request(0, "initialize", Some(json!({"capabilities": {}})));
    server.receive_response(0);
    server.send_notification("initialized", Some(json!({})));
    for (id, method) in [(1, "dogwood-lsp/testControl"), (2, "dogwood/testBarrier")] {
        server.send_request(id, method, Some(json!({"command": "snapshotStats"})));
        let response = server.receive_response(id);
        assert_eq!(response["error"]["code"], -32601, "{response}");
        assert_eq!(
            response["error"]["message"], "Method not found",
            "{response}"
        );
    }
    server.send_request(3, "shutdown", None);
    server.receive_response(3);
    server.send_notification("exit", None);
    server.finish(0);
}
