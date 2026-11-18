# Protocol Conformance Matrix

Every evidence cell begins with `process:` and names a compiled-process
assertion. Supplemental unit evidence is labeled separately. `LspProcess`
launches the built `dogwood-lsp` binary, exchanges framed JSON-RPC over its real
standard streams, rejects duplicate response IDs, and requires clean framed
stdout through process exit.

## Advertised and Dynamic Capabilities

| ID | Contract | Compiled-process evidence |
| --- | --- | --- |
| `CAP-UTF16` | `positionEncoding` is exactly `utf-16` | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `CAP-SYNC` | `textDocumentSync` advertises open/close and incremental change (`2`) | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract`; `m7_incremental::incremental_utf16_changes_match_equivalent_full_documents_atomically` |
| `CAP-SEMANTIC-LEGEND` | Frozen 19 token types and one `declaration` modifier | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `CAP-SEMANTIC-FULL` | Full-document semantic tokens only; range is false and delta/refresh are absent | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `CAP-NO-EXTRA` | Initialize result contains no other user-facing capability | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `DYN-WATCH` | Dynamic watched-file registration is requested only when supported, with exact conventional and explicit patterns | process: `m4_diagnostics::dynamic_client_registers_exact_watchers_and_watched_change_revalidates`; `m4_diagnostics::absent_or_false_dynamic_registration_fails_closed_external_bundles` |
| `TEST-GATE` | Test control and barrier methods are unadvertised and unavailable without the explicit environment gate | process: `m7_concurrency::test_control_and_barrier_are_unavailable_without_the_explicit_environment_switch` |

The final user-facing language surface is therefore diagnostics notifications
and full semantic highlighting. There is no formatting, completion, hover,
navigation, code-action, schema-editing, diagnostic-pull, semantic-delta, or
semantic-refresh capability.

## Lifecycle and Error Paths

All errors omit `error.data`.

| ID | Condition and exact result | Compiled-process evidence |
| --- | --- | --- |
| `ERR-PREINIT` | Request before initialization: `-32002`, `Server not initialized` | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `ERR-DUPINIT` | Duplicate initialize: `-32600`, `Initialize request may only be sent once` | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `ERR-INVALID-PARAMS` | Malformed request params: `-32602`, `Invalid params` | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `ERR-UNKNOWN` | Unknown running method: `-32601`, `Method not found` | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `ERR-DOC-UNOPENED` | Semantic request for an unopened document: `-32803`, `Document is not open` | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `ERR-DOC-CLOSED` | Semantic request after close: `-32803`, `Document is not open` | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `ERR-DOC-DEPENDENCY` | Semantic request for action/provider/macro dependency: `-32803`, `Document is not open` | process: `m6_process::compiled_server_freezes_document_kind_precedence_and_dependency_rejection` |
| `ERR-TOKEN-LIMIT` | Semantic token resource limit: `-32803`, `Semantic token limit exceeded` | process: `stdio_black_box::compiled_server_rejects_the_token_limit_and_recovers_after_change` |
| `ERR-REQUEST-CANCELLED` | Explicit semantic cancellation: `-32800`, `Request cancelled` | process: `m7_concurrency::semantic_edits_and_explicit_cancellation_are_single_response_and_responsive` |
| `ERR-CONTENT-MODIFIED` | Accepted edit/close supersedes semantic request: `-32801`, `Content modified` | process: `m7_concurrency::semantic_edits_and_explicit_cancellation_are_single_response_and_responsive` |
| `ERR-SERVER-CANCELLED` | Queue rejection or diagnostic eviction: `-32802`, `Server cancelled` | process: `m7_concurrency::semantic_queue_rejection_and_diagnostic_eviction_are_single_response` |
| `ERR-SHUTDOWN` | Request after shutdown: `-32600`, `Server has shut down` | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `LIFE-SHUTDOWN-EXIT` | Shutdown returns null; subsequent exit returns status 0 | process: `stdio_black_box::compiled_server_obeys_the_m1_stdio_contract` |
| `LIFE-EARLY-EXIT` | Exit before shutdown returns status 1 | process: `stdio_black_box::exit_before_shutdown_returns_status_one` |
| `RESP-SINGLE` | Every request ID receives at most one terminal response, including cancellation races | process: `m7_concurrency::semantic_edits_and_explicit_cancellation_are_single_response_and_responsive`; `m7_concurrency::semantic_queue_rejection_and_diagnostic_eviction_are_single_response`; supplemental harness: `support::lsp_process::LspProcess::validate_response` |

## Framing

| ID | Contract | Evidence |
| --- | --- | --- |
| `FRAME-HEADER` | Headers are bounded at 8 KiB; malformed, unsupported, incomplete, and oversized headers fail closed | process: `stdio_black_box::malformed_and_boundary_frames_fail_closed_in_the_compiled_server`; `stdio_black_box::exact_eight_kibibyte_header_reaches_normal_protocol_handling`; supplemental unit: `transport::tests::exact_header_and_body_limits_are_accepted` and adversarial transport tests |
| `FRAME-BODY` | Bodies are bounded at 16 MiB; oversized declarations, incomplete bodies, and malformed JSON fail closed | process: `stdio_black_box::oversized_declared_body_is_rejected_without_sending_the_body`; `stdio_black_box::malformed_and_boundary_frames_fail_closed_in_the_compiled_server`; supplemental unit: `transport::tests::exact_header_and_body_limits_are_accepted` |
| `FRAME-STDOUT` | Standard output contains framed protocol messages only through process exit | process: `stdio_black_box::malformed_and_boundary_frames_fail_closed_in_the_compiled_server`; supplemental harness: `support::lsp_process::LspProcess::finish` rejects trailing messages and malformed stdout |
