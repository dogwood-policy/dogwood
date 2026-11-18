use dogwood_lsp::legend::{TOKEN_MODIFIERS, TOKEN_TYPES};
use lsp_types::{
    InitializeResult, PositionEncodingKind, SemanticTokenModifier, SemanticTokenType,
    SemanticTokensFullOptions, SemanticTokensLegend, SemanticTokensOptions,
    SemanticTokensServerCapabilities, ServerCapabilities, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextDocumentSyncOptions, WorkDoneProgressOptions,
};

pub(crate) fn initialize_result() -> InitializeResult {
    InitializeResult {
        capabilities: server_capabilities(),
        server_info: None,
    }
}

fn server_capabilities() -> ServerCapabilities {
    let token_types = TOKEN_TYPES
        .into_iter()
        .map(SemanticTokenType::from)
        .collect();
    let token_modifiers = TOKEN_MODIFIERS
        .into_iter()
        .map(SemanticTokenModifier::from)
        .collect();

    ServerCapabilities {
        position_encoding: Some(PositionEncodingKind::UTF16),
        text_document_sync: Some(TextDocumentSyncCapability::Options(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(TextDocumentSyncKind::INCREMENTAL),
                ..TextDocumentSyncOptions::default()
            },
        )),
        semantic_tokens_provider: Some(SemanticTokensServerCapabilities::SemanticTokensOptions(
            SemanticTokensOptions {
                work_done_progress_options: WorkDoneProgressOptions::default(),
                legend: SemanticTokensLegend {
                    token_types,
                    token_modifiers,
                },
                range: Some(false),
                full: Some(SemanticTokensFullOptions::Bool(true)),
            },
        )),
        ..ServerCapabilities::default()
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::initialize_result;

    #[test]
    fn initialize_result_serializes_the_exact_frozen_capabilities() {
        assert_eq!(
            serde_json::to_value(initialize_result()).expect("capabilities should serialize"),
            json!({
                "capabilities": {
                    "positionEncoding": "utf-16",
                    "textDocumentSync": {
                        "openClose": true,
                        "change": 2
                    },
                    "semanticTokensProvider": {
                        "legend": {
                            "tokenTypes": [
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
                                "decorator"
                            ],
                            "tokenModifiers": ["declaration"]
                        },
                        "range": false,
                        "full": true
                    }
                }
            })
        );
    }
}
