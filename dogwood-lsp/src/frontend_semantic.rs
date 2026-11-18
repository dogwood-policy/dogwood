//! LSP legend adapter for parser-backed Dogwood policy syntax spans.

use dogwood_language::syntax::{SyntaxKind, SyntaxModifier, SyntaxSpan};

use crate::frontend::{FrontendOutcome, PolicyParseInput, parse_policy};
use crate::legend::{TokenKind, TokenModifier};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SemanticSpan {
    pub start: usize,
    pub end: usize,
    pub kind: TokenKind,
    pub modifier: Option<TokenModifier>,
}

/// Immutable borrowed source inputs for one strict semantic classification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SemanticInput<'a> {
    pub policy: &'a str,
    pub event_schema: Option<&'a str>,
    pub providers: Option<&'a str>,
    pub macros: Option<&'a str>,
}

impl<'a> SemanticInput<'a> {
    pub const fn standalone(policy: &'a str) -> Self {
        Self {
            policy,
            event_schema: None,
            providers: None,
            macros: None,
        }
    }
}

/// Return parser-backed spans only when the strict Dogwood frontend accepts
/// the complete source, including macro expansion and the operational
/// envelope.
pub fn classify(source: &str) -> Option<Vec<SemanticSpan>> {
    classify_with_input(&SemanticInput::standalone(source))
}

/// Return parser-backed spans for a complete source and its resolved service
/// inputs only when the strict Dogwood frontend accepts the entire snapshot.
pub fn classify_with_input(input: &SemanticInput<'_>) -> Option<Vec<SemanticSpan>> {
    let parse_input = PolicyParseInput {
        policy: input.policy,
        event_schema: input.event_schema,
        providers: input.providers,
        macros: input.macros,
    };
    if !matches!(parse_policy(&parse_input), FrontendOutcome::Report(_)) {
        return None;
    }

    let spans = dogwood_language::syntax::policy_spans(input.policy)?;
    map_spans(input.policy, spans)
}

fn map_spans(source: &str, spans: Vec<SyntaxSpan>) -> Option<Vec<SemanticSpan>> {
    let mapped = spans
        .into_iter()
        .map(map_span)
        .collect::<Option<Vec<_>>>()?;
    if mapped.iter().any(|span| {
        span.start >= span.end
            || span.end > source.len()
            || !source.is_char_boundary(span.start)
            || !source.is_char_boundary(span.end)
    }) {
        return None;
    }
    if mapped.windows(2).any(|pair| pair[1].start < pair[0].end) {
        return None;
    }
    Some(mapped)
}

fn map_span(span: SyntaxSpan) -> Option<SemanticSpan> {
    Some(SemanticSpan {
        start: span.start,
        end: span.end,
        kind: match span.kind {
            SyntaxKind::Namespace => TokenKind::Namespace,
            SyntaxKind::Type => TokenKind::Type,
            SyntaxKind::TypeParameter => TokenKind::TypeParameter,
            SyntaxKind::Parameter => TokenKind::Parameter,
            SyntaxKind::Variable => TokenKind::Variable,
            SyntaxKind::Property => TokenKind::Property,
            SyntaxKind::Event => TokenKind::Event,
            SyntaxKind::Function => TokenKind::Function,
            SyntaxKind::Method => TokenKind::Method,
            SyntaxKind::Macro => TokenKind::Macro,
            SyntaxKind::Keyword => TokenKind::Keyword,
            SyntaxKind::String => TokenKind::String,
            SyntaxKind::Number => TokenKind::Number,
            SyntaxKind::Decorator => TokenKind::Decorator,
            _ => return None,
        },
        modifier: match span.modifier {
            Some(SyntaxModifier::Declaration) => Some(TokenModifier::Declaration),
            Some(_) => return None,
            None => None,
        },
    })
}
