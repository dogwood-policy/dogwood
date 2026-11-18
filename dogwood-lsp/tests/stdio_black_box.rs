#[path = "support/lsp_process.rs"]
mod lsp_process;

use dogwood_lsp::analysis::MAX_SEMANTIC_TOKENS;
use lsp_process::{LspProcess, MAX_CONTENT_LENGTH, MAX_HEADER_BYTES};
use serde_json::{Value, json};

const TOKEN_TYPES: [&str; 19] = [
    "namespace",
    "type",
    "struct",
    "typeParameter",
    "parameter",
    "variable",
    "property",
    "enumMember",
    "event",
    "function",
    "method",
    "macro",
    "keyword",
    "modifier",
    "comment",
    "string",
    "number",
    "operator",
    "decorator",
];
const TOKEN_MODIFIERS: [&str; 1] = ["declaration"];
const PUBLISH_DIAGNOSTICS: &str = "textDocument/publishDiagnostics";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ExpectedToken {
    line: u32,
    start: u32,
    length: u32,
    token_type: &'static str,
    modifiers: &'static [&'static str],
}

#[derive(Debug, Eq, PartialEq)]
struct SemanticTokenResponse {
    encoded: Vec<u32>,
    decoded: Vec<ExpectedToken>,
}

const fn token(
    line: u32,
    start: u32,
    length: u32,
    token_type: &'static str,
    modifiers: &'static [&'static str],
) -> ExpectedToken {
    ExpectedToken {
        line,
        start,
        length,
        token_type,
        modifiers,
    }
}

const LEXICAL_BASIC_TOKENS: &[ExpectedToken] = &[
    token(0, 0, 31, "comment", &[]),
    token(1, 0, 1, "operator", &[]),
    token(1, 1, 2, "decorator", &[]),
    token(1, 3, 1, "operator", &[]),
    token(1, 4, 8, "string", &[]),
    token(1, 12, 1, "operator", &[]),
    token(2, 0, 6, "keyword", &[]),
    token(2, 6, 1, "operator", &[]),
    token(2, 7, 9, "keyword", &[]),
    token(2, 16, 1, "operator", &[]),
    token(2, 18, 6, "keyword", &[]),
    token(2, 25, 2, "operator", &[]),
    token(2, 28, 4, "namespace", &[]),
    token(2, 32, 2, "operator", &[]),
    token(2, 34, 6, "type", &[]),
    token(2, 40, 2, "operator", &[]),
    token(2, 42, 6, "string", &[]),
    token(2, 48, 1, "operator", &[]),
    token(2, 50, 8, "keyword", &[]),
    token(2, 58, 1, "operator", &[]),
    token(3, 0, 4, "keyword", &[]),
    token(3, 5, 1, "operator", &[]),
    token(3, 7, 4, "keyword", &[]),
    token(3, 12, 2, "operator", &[]),
    token(3, 15, 1, "operator", &[]),
    token(3, 16, 5, "keyword", &[]),
    token(3, 22, 2, "operator", &[]),
    token(3, 25, 7, "keyword", &[]),
    token(3, 32, 1, "operator", &[]),
    token(3, 39, 2, "operator", &[]),
    token(3, 42, 2, "number", &[]),
    token(3, 45, 1, "operator", &[]),
    token(4, 0, 6, "keyword", &[]),
    token(4, 7, 1, "operator", &[]),
    token(4, 9, 3, "number", &[]),
    token(4, 13, 2, "operator", &[]),
    token(4, 16, 3, "number", &[]),
    token(4, 20, 1, "operator", &[]),
    token(4, 22, 1, "operator", &[]),
    token(4, 23, 1, "number", &[]),
    token(4, 25, 1, "operator", &[]),
    token(4, 27, 1, "number", &[]),
    token(4, 29, 1, "operator", &[]),
    token(4, 31, 1, "number", &[]),
    token(4, 33, 1, "operator", &[]),
    token(4, 35, 1, "number", &[]),
    token(4, 37, 2, "operator", &[]),
    token(4, 40, 1, "number", &[]),
    token(4, 42, 1, "operator", &[]),
    token(4, 43, 1, "operator", &[]),
];

const LEXICAL_INCOMPLETE_TOKENS: &[ExpectedToken] = &[
    token(0, 0, 6, "keyword", &[]),
    token(0, 6, 1, "operator", &[]),
    token(1, 2, 9, "keyword", &[]),
    token(1, 11, 1, "operator", &[]),
    token(2, 2, 6, "keyword", &[]),
    token(2, 9, 1, "operator", &[]),
    token(2, 11, 1, "operator", &[]),
    token(2, 17, 1, "operator", &[]),
    token(3, 0, 4, "keyword", &[]),
    token(3, 5, 1, "operator", &[]),
    token(3, 7, 2, "number", &[]),
    token(3, 11, 1, "operator", &[]),
    token(3, 13, 1, "operator", &[]),
    token(3, 15, 17, "comment", &[]),
    token(4, 2, 15, "string", &[]),
];

const LEXICAL_UNICODE_TOKENS: &[ExpectedToken] = &[
    token(0, 3, 6, "keyword", &[]),
    token(0, 10, 6, "comment", &[]),
    token(1, 0, 4, "keyword", &[]),
    token(1, 5, 1, "operator", &[]),
    token(1, 7, 8, "string", &[]),
    token(1, 16, 2, "operator", &[]),
    token(1, 19, 4, "keyword", &[]),
    token(1, 24, 1, "operator", &[]),
    token(1, 26, 10, "comment", &[]),
];

#[test]
fn compiled_server_obeys_the_m1_stdio_contract() {
    let pre_initialize_uri = "file:///pre-initialize.dw";
    let document_uri = "file:///policy.dw";
    let mut server = LspProcess::spawn();

    server.send_notification(
        "textDocument/didOpen",
        Some(open_params(pre_initialize_uri, 1, "ignored")),
    );
    server.send_request(
        0,
        "textDocument/semanticTokens/full",
        Some(tokens_params(pre_initialize_uri)),
    );
    assert_error(&mut server, 0, -32002, "Server not initialized");

    initialize(&mut server, 1);

    server.send_request(2, "initialize", Some(initialize_params()));
    assert_error(
        &mut server,
        2,
        -32600,
        "Initialize request may only be sent once",
    );

    server.send_notification("initialized", Some(json!({})));

    server.send_request(
        3,
        "textDocument/semanticTokens/full",
        Some(tokens_params(pre_initialize_uri)),
    );
    assert_error(&mut server, 3, -32803, "Document is not open");

    server.send_request(4, "dogwood/unknown", Some(json!({})));
    assert_error(&mut server, 4, -32601, "Method not found");

    server.send_request(
        5,
        "textDocument/semanticTokens/full",
        Some(json!({"textDocument": 42})),
    );
    assert_error(&mut server, 5, -32602, "Invalid params");

    server.send_notification(
        "textDocument/didOpen",
        Some(open_params(document_uri, 1, " \n\t")),
    );
    server.send_request(
        6,
        "textDocument/semanticTokens/full",
        Some(tokens_params(document_uri)),
    );
    assert_empty_tokens(&mut server, 6);
    assert_project_diagnostics(&mut server, document_uri, 1);

    server.send_notification(
        "textDocument/didChange",
        Some(json!({
            "textDocument": {
                "uri": document_uri,
                "version": 2
            },
            "contentChanges": [{
                "text": ""
            }]
        })),
    );
    server.send_request(
        7,
        "textDocument/semanticTokens/full",
        Some(tokens_params(document_uri)),
    );
    assert_empty_tokens(&mut server, 7);
    assert_project_diagnostics(&mut server, document_uri, 2);

    server.send_notification(
        "textDocument/didClose",
        Some(json!({"textDocument": {"uri": document_uri}})),
    );
    server.send_request(
        8,
        "textDocument/semanticTokens/full",
        Some(tokens_params(document_uri)),
    );
    assert_error(&mut server, 8, -32803, "Document is not open");
    assert_empty_diagnostics(&mut server, document_uri, 2);

    server.send_notification("exit", Some(json!({"invalid": true})));
    server.send_request(9, "dogwood/still-running", Some(json!({})));
    assert_error(&mut server, 9, -32601, "Method not found");
    server.assert_running();

    server.send_request(10, "shutdown", Some(Value::Null));
    server.expect_response(10, json!({"jsonrpc": "2.0", "id": 10, "result": null}));
    server.assert_running();

    server.send_request(
        11,
        "textDocument/semanticTokens/full",
        Some(tokens_params(document_uri)),
    );
    assert_error(&mut server, 11, -32600, "Server has shut down");

    server.send_notification("exit", None);
    server.finish(0);
}

#[test]
fn exit_before_shutdown_returns_status_one() {
    let document_uri = "file:///exit-before-shutdown.dw";
    let mut server = LspProcess::spawn();

    initialize(&mut server, 0);
    server.send_notification("initialized", Some(json!({})));
    server.send_notification(
        "textDocument/didOpen",
        Some(open_params(document_uri, 1, "")),
    );
    server.send_request(
        1,
        "textDocument/semanticTokens/full",
        Some(tokens_params(document_uri)),
    );
    assert_empty_tokens(&mut server, 1);
    assert_project_diagnostics(&mut server, document_uri, 1);

    server.send_notification("exit", Some(Value::Null));
    server.finish(1);
}

#[test]
fn oversized_declared_body_is_rejected_without_sending_the_body() {
    let mut server = LspProcess::spawn();
    let declared_length = MAX_CONTENT_LENGTH + 1;

    server.send_raw(format!("Content-Length: {declared_length}\r\n\r\n").into_bytes());
    server.finish_with_stderr(
        1,
        &format!(
            "failed to read LSP message: Content-Length {declared_length} exceeds the \
             {MAX_CONTENT_LENGTH}-byte limit"
        ),
    );
}

#[test]
fn malformed_and_boundary_frames_fail_closed_in_the_compiled_server() {
    struct Case {
        name: &'static str,
        frame: Vec<u8>,
        expected_error: &'static str,
        close_stdin: bool,
    }

    let cases = [
        Case {
            name: "duplicate content length",
            frame: b"Content-Length: 2\r\ncontent-length: 2\r\n\r\n{}".to_vec(),
            expected_error: "duplicate Content-Length header",
            close_stdin: false,
        },
        Case {
            name: "missing content length",
            frame: b"Content-Type: application/json\r\n\r\n{}".to_vec(),
            expected_error: "missing Content-Length header",
            close_stdin: false,
        },
        Case {
            name: "invalid content length",
            frame: b"Content-Length: invalid\r\n\r\n{}".to_vec(),
            expected_error: "invalid Content-Length header",
            close_stdin: false,
        },
        Case {
            name: "unsupported header",
            frame: b"Transfer-Encoding: chunked\r\n\r\n".to_vec(),
            expected_error: "unsupported LSP header `Transfer-Encoding`",
            close_stdin: false,
        },
        Case {
            name: "malformed header field",
            frame: b"Content-Length 2\r\n\r\n{}".to_vec(),
            expected_error: "malformed LSP header field",
            close_stdin: false,
        },
        Case {
            name: "malformed header name",
            frame: b"Content Length: 2\r\n\r\n{}".to_vec(),
            expected_error: "malformed LSP header name",
            close_stdin: false,
        },
        Case {
            name: "non-ASCII header",
            frame: b"Content-Length: 2\r\nX-\xff: value\r\n\r\n{}".to_vec(),
            expected_error: "LSP header contains non-ASCII bytes",
            close_stdin: false,
        },
        Case {
            name: "malformed JSON",
            frame: b"Content-Length: 1\r\n\r\n{".to_vec(),
            expected_error: "malformed LSP JSON body:",
            close_stdin: false,
        },
        Case {
            name: "incomplete header EOF",
            frame: b"Content-Length: 2\r\n".to_vec(),
            expected_error: "incomplete LSP header",
            close_stdin: true,
        },
        Case {
            name: "incomplete body EOF",
            frame: b"Content-Length: 2\r\n\r\n{".to_vec(),
            expected_error: "incomplete LSP body: expected 2 bytes",
            close_stdin: true,
        },
        Case {
            name: "oversized header",
            frame: vec![b'x'; MAX_HEADER_BYTES + 1],
            expected_error: "LSP header exceeds the 8192-byte limit",
            close_stdin: false,
        },
    ];

    for case in cases {
        let mut server = LspProcess::spawn();
        server.send_raw(case.frame);
        if case.close_stdin {
            server.close_stdin();
        }
        server.finish_with_stderr(
            1,
            &format!("failed to read LSP message: {}", case.expected_error),
        );
        eprintln!("validated malformed frame case: {}", case.name);
    }
}

#[test]
fn exact_eight_kibibyte_header_reaches_normal_protocol_handling() {
    let body = serde_json::to_vec(&json!({
        "jsonrpc": "2.0",
        "id": 0,
        "method": "initialize",
        "params": initialize_params()
    }))
    .expect("initialize request should serialize");
    let prefix = format!("Content-Length: {}\r\nContent-Type:", body.len()).into_bytes();
    let suffix = b"\r\n\r\n";
    let padding = MAX_HEADER_BYTES - prefix.len() - suffix.len();
    let mut frame = Vec::with_capacity(MAX_HEADER_BYTES + body.len());
    frame.extend(prefix);
    frame.extend(std::iter::repeat_n(b'x', padding));
    frame.extend_from_slice(suffix);
    assert_eq!(frame.len(), MAX_HEADER_BYTES);
    frame.extend(body);

    let mut server = LspProcess::spawn();
    server.send_raw(frame);
    assert_initialize_response(&mut server, 0);
    server.send_notification("exit", None);
    server.finish(1);
}

#[test]
fn compiled_server_returns_exact_m2_semantic_tokens() {
    let document_uri = "file:///lexical-current.dw";
    let incomplete_uri = "file:///lexical-incomplete.dw";
    let basic_source = include_str!("fixtures/lexical-basic.dw");
    let unicode_source = include_str!("fixtures/lexical-unicode.dw");
    let incomplete_source = include_str!("fixtures/lexical-incomplete.dw");
    let mut server = LspProcess::spawn();

    initialize(&mut server, 0);
    server.send_notification("initialized", Some(json!({})));
    server.send_notification(
        "textDocument/didOpen",
        Some(open_params(document_uri, 1, basic_source)),
    );

    server.send_request(
        1,
        "textDocument/semanticTokens/full",
        Some(tokens_params(document_uri)),
    );
    let first_basic = assert_semantic_tokens(&mut server, 1, LEXICAL_BASIC_TOKENS);
    assert_project_diagnostics(&mut server, document_uri, 1);

    server.send_request(
        2,
        "textDocument/semanticTokens/full",
        Some(tokens_params(document_uri)),
    );
    let second_basic = assert_semantic_tokens(&mut server, 2, LEXICAL_BASIC_TOKENS);
    assert_eq!(second_basic.encoded, first_basic.encoded);
    assert_eq!(second_basic.decoded, first_basic.decoded);

    server.send_notification(
        "textDocument/didChange",
        Some(json!({
            "textDocument": {
                "uri": document_uri,
                "version": 2
            },
            "contentChanges": [{
                "text": unicode_source
            }]
        })),
    );
    server.send_request(
        3,
        "textDocument/semanticTokens/full",
        Some(tokens_params(document_uri)),
    );
    let unicode = assert_semantic_tokens(&mut server, 3, LEXICAL_UNICODE_TOKENS);
    assert_project_diagnostics(&mut server, document_uri, 2);
    assert_ne!(unicode.encoded, first_basic.encoded);
    assert_ne!(unicode.decoded, first_basic.decoded);

    server.send_notification(
        "textDocument/didOpen",
        Some(open_params(incomplete_uri, 1, incomplete_source)),
    );
    server.send_request(
        4,
        "textDocument/semanticTokens/full",
        Some(tokens_params(incomplete_uri)),
    );
    assert_semantic_tokens(&mut server, 4, LEXICAL_INCOMPLETE_TOKENS);
    assert_project_diagnostics(&mut server, incomplete_uri, 1);

    server.send_request(5, "shutdown", None);
    server.expect_response(5, json!({"jsonrpc": "2.0", "id": 5, "result": null}));
    server.send_notification("exit", Some(Value::Null));
    server.finish(0);
}

#[test]
fn compiled_server_rejects_the_token_limit_and_recovers_after_change() {
    let document_uri = "file:///lexical-limit.dw";
    let oversized_source = "+".repeat(MAX_SEMANTIC_TOKENS + 1);
    let recovered_tokens = [token(0, 0, 6, "keyword", &[])];
    let mut server = LspProcess::spawn();

    initialize(&mut server, 0);
    server.send_notification("initialized", Some(json!({})));
    server.send_notification(
        "textDocument/didOpen",
        Some(open_params(document_uri, 1, &oversized_source)),
    );
    server.send_request(
        1,
        "textDocument/semanticTokens/full",
        Some(tokens_params(document_uri)),
    );
    assert_error(&mut server, 1, -32803, "Semantic token limit exceeded");
    assert_project_diagnostics(&mut server, document_uri, 1);
    server.assert_running();

    server.send_notification(
        "textDocument/didChange",
        Some(json!({
            "textDocument": {
                "uri": document_uri,
                "version": 2
            },
            "contentChanges": [{
                "text": "permit"
            }]
        })),
    );
    server.send_request(
        2,
        "textDocument/semanticTokens/full",
        Some(tokens_params(document_uri)),
    );
    assert_semantic_tokens(&mut server, 2, &recovered_tokens);
    assert_project_diagnostics(&mut server, document_uri, 2);

    server.send_request(3, "shutdown", None);
    server.expect_response(3, json!({"jsonrpc": "2.0", "id": 3, "result": null}));
    server.send_notification("exit", Some(Value::Null));
    server.finish(0);
}

fn open_params(uri: &str, version: i32, text: &str) -> Value {
    json!({
        "textDocument": {
            "uri": uri,
            "languageId": "dogwood",
            "version": version,
            "text": text
        }
    })
}

fn tokens_params(uri: &str) -> Value {
    json!({"textDocument": {"uri": uri}})
}

fn initialize_params() -> Value {
    json!({
        "capabilities": {
            "general": {
                "positionEncodings": ["utf-8", "utf-16"]
            },
            "textDocument": {
                "semanticTokens": {
                    "dynamicRegistration": false,
                    "requests": {
                        "range": false,
                        "full": true
                    },
                    "tokenTypes": [],
                    "tokenModifiers": [],
                    "formats": ["relative"]
                }
            }
        }
    })
}

fn initialize(server: &mut LspProcess, id: i64) {
    server.send_request(id, "initialize", Some(initialize_params()));
    assert_initialize_response(server, id);
}

fn assert_initialize_response(server: &mut LspProcess, id: i64) {
    server.expect_response(
        id,
        json!({
            "jsonrpc": "2.0",
            "id": id,
            "result": {
                "capabilities": {
                    "positionEncoding": "utf-16",
                    "textDocumentSync": {
                        "openClose": true,
                        "change": 2
                    },
                    "semanticTokensProvider": {
                        "legend": {
                            "tokenTypes": TOKEN_TYPES,
                            "tokenModifiers": TOKEN_MODIFIERS
                        },
                        "range": false,
                        "full": true
                    }
                }
            }
        }),
    );
}

fn assert_empty_tokens(server: &mut LspProcess, id: i64) {
    server.expect_response(
        id,
        json!({"jsonrpc": "2.0", "id": id, "result": {"data": []}}),
    );
}

fn assert_semantic_tokens(
    server: &mut LspProcess,
    id: i64,
    expected: &[ExpectedToken],
) -> SemanticTokenResponse {
    let actual = semantic_token_response(server, id);
    assert_eq!(actual.decoded, expected);
    assert_eq!(actual.encoded, encode_expected_tokens(expected));
    actual
}

fn semantic_token_response(server: &mut LspProcess, id: i64) -> SemanticTokenResponse {
    let response = server.receive_response(id);
    let result = response
        .get("result")
        .unwrap_or_else(|| panic!("semantic-token request returned an error: {response}"));
    let data = result
        .as_object()
        .and_then(|object| object.get("data"))
        .and_then(Value::as_array)
        .unwrap_or_else(|| panic!("semantic-token result.data must be a flat array: {response}"));
    assert_eq!(
        data.len() % 5,
        0,
        "semantic-token result.data must contain five-word groups"
    );

    let encoded = data
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let word = value.as_u64().unwrap_or_else(|| {
                panic!("semantic-token word {index} is not an unsigned integer")
            });
            u32::try_from(word)
                .unwrap_or_else(|_| panic!("semantic-token word {index} exceeds u32"))
        })
        .collect::<Vec<_>>();
    let decoded = decode_semantic_tokens(&encoded);

    SemanticTokenResponse { encoded, decoded }
}

fn decode_semantic_tokens(encoded: &[u32]) -> Vec<ExpectedToken> {
    let known_modifier_mask = (0..TOKEN_MODIFIERS.len()).fold(0u32, |mask, index| {
        mask | 1u32
            .checked_shl(u32::try_from(index).expect("modifier index should fit u32"))
            .expect("test legend cannot contain more than 32 modifiers")
    });
    let mut previous_line = 0u32;
    let mut previous_start = 0u32;

    encoded
        .as_chunks::<5>()
        .0
        .iter()
        .enumerate()
        .map(|(index, words)| {
            let [
                delta_line,
                delta_start,
                length,
                token_type_index,
                modifier_bits,
            ] = *words;
            let line = previous_line.checked_add(delta_line).unwrap_or_else(|| {
                panic!("semantic token {index} overflows its absolute line position")
            });
            let start = if delta_line == 0 {
                previous_start.checked_add(delta_start).unwrap_or_else(|| {
                    panic!("semantic token {index} overflows its absolute start position")
                })
            } else {
                delta_start
            };
            let token_type = usize::try_from(token_type_index)
                .ok()
                .and_then(|token_type_index| TOKEN_TYPES.get(token_type_index))
                .copied()
                .unwrap_or_else(|| {
                    panic!("semantic token {index} uses unknown type index {token_type_index}")
                });
            assert_eq!(
                modifier_bits & !known_modifier_mask,
                0,
                "semantic token {index} uses unknown modifier bits {modifier_bits:#x}"
            );
            let modifiers = TOKEN_MODIFIERS
                .iter()
                .enumerate()
                .filter_map(|(modifier_index, modifier)| {
                    let bit = 1u32
                        .checked_shl(
                            u32::try_from(modifier_index).expect("modifier index should fit u32"),
                        )
                        .expect("test legend cannot contain more than 32 modifiers");
                    (modifier_bits & bit != 0).then_some(*modifier)
                })
                .collect::<Vec<_>>();
            let modifiers = match modifiers.as_slice() {
                [] => &[][..],
                ["declaration"] => &["declaration"][..],
                _ => unreachable!("all modifier combinations are covered by the frozen legend"),
            };

            previous_line = line;
            previous_start = start;
            ExpectedToken {
                line,
                start,
                length,
                token_type,
                modifiers,
            }
        })
        .collect()
}

fn encode_expected_tokens(tokens: &[ExpectedToken]) -> Vec<u32> {
    let mut encoded = Vec::with_capacity(tokens.len() * 5);
    let mut previous_line = 0u32;
    let mut previous_start = 0u32;

    for (index, token) in tokens.iter().enumerate() {
        assert!(token.length > 0, "expected token {index} must be non-empty");
        let delta_line = token
            .line
            .checked_sub(previous_line)
            .unwrap_or_else(|| panic!("expected token {index} is not sorted by line"));
        let delta_start = if delta_line == 0 {
            token
                .start
                .checked_sub(previous_start)
                .unwrap_or_else(|| panic!("expected token {index} is not sorted by start"))
        } else {
            token.start
        };
        let token_type = TOKEN_TYPES
            .iter()
            .position(|candidate| candidate == &token.token_type)
            .and_then(|token_type| u32::try_from(token_type).ok())
            .unwrap_or_else(|| {
                panic!(
                    "expected token {index} uses unknown type {}",
                    token.token_type
                )
            });
        let mut modifier_bits = 0u32;
        for modifier in token.modifiers {
            let modifier_index = TOKEN_MODIFIERS
                .iter()
                .position(|candidate| candidate == modifier)
                .unwrap_or_else(|| {
                    panic!("expected token {index} uses unknown modifier {modifier}")
                });
            let bit = 1u32
                .checked_shl(u32::try_from(modifier_index).expect("modifier index should fit u32"))
                .expect("test legend cannot contain more than 32 modifiers");
            assert_eq!(
                modifier_bits & bit,
                0,
                "expected token {index} repeats modifier {modifier}"
            );
            modifier_bits |= bit;
        }

        encoded.extend_from_slice(&[
            delta_line,
            delta_start,
            token.length,
            token_type,
            modifier_bits,
        ]);
        previous_line = token.line;
        previous_start = token.start;
    }

    encoded
}

fn assert_error(server: &mut LspProcess, id: i64, code: i64, message: &str) {
    server.expect_response(
        id,
        json!({
            "jsonrpc": "2.0",
            "id": id,
            "error": {
                "code": code,
                "message": message
            }
        }),
    );
}

fn assert_project_diagnostics(server: &mut LspProcess, uri: &str, version: i32) {
    let notification = server.receive_notification(PUBLISH_DIAGNOSTICS);
    let params = &notification["params"];
    assert_eq!(params["uri"], uri);
    assert_eq!(params["version"], version);
    let diagnostics = params["diagnostics"].as_array().unwrap();
    assert_eq!(diagnostics.len(), 1, "{notification}");
    assert_eq!(diagnostics[0]["code"], "dogwood.project");
}

fn assert_empty_diagnostics(server: &mut LspProcess, uri: &str, version: i32) {
    let notification = server.receive_notification(PUBLISH_DIAGNOSTICS);
    assert_eq!(
        notification["params"],
        json!({"uri": uri, "version": version, "diagnostics": []})
    );
}
