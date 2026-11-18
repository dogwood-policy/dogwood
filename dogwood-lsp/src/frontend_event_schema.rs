//! LSP legend adapter for parser-backed Dogwood event-schema syntax spans.

use dogwood_language::syntax::{SyntaxKind, SyntaxModifier, SyntaxSpan};

use crate::frontend::{FrontendOutcome, parse_event_schema};
use crate::legend::{TokenKind, TokenModifier};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SemanticSpan {
    pub start: usize,
    pub end: usize,
    pub kind: TokenKind,
    pub modifier: Option<TokenModifier>,
}

/// Return structural spans only when the authoritative Dogwood frontend and
/// canonical syntax classifier both accept the source.
pub fn classify(source: &str) -> Option<Vec<SemanticSpan>> {
    if !matches!(
        parse_event_schema(source),
        FrontendOutcome::Report(report) if report.valid
    ) {
        return None;
    }

    let spans = dogwood_language::syntax::event_schema_spans(source)?;
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
