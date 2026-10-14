//! Shared, source-preserving syntax support for Dogwood (`.dw`) policy files.
//!
//! This crate owns the policy grammar used by the semantic parser and exposes
//! the lossless token stream and structural spans needed by the formatter.
//! It deliberately stops before AST construction, macro expansion, schema
//! resolution, or any other semantic operation.

use pest::Parser as _;

mod generated {
    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "grammar.pest"]
    pub(super) struct DogwoodParser;
}

#[doc(hidden)]
pub use generated::Rule;

/// A byte range `[start, end)` in Dogwood source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { start, end }
    }

    pub fn contains(self, other: Span) -> bool {
        self.start <= other.start && other.end <= self.end
    }

    pub fn text(self, source: &str) -> &str {
        &source[self.start..self.end]
    }
}

/// A pair produced by the shared Dogwood policy grammar.
#[doc(hidden)]
pub type Pair<'source> = pest::iterators::Pair<'source, Rule>;

/// The pairs produced by the shared Dogwood policy grammar.
#[doc(hidden)]
pub type Pairs<'source> = pest::iterators::Pairs<'source, Rule>;

/// Parse `source` starting at a rule from the shared Dogwood policy grammar.
///
/// Most callers should use [`parse_document`]. This lower-level entry point is
/// exposed for the semantic parser, which also parses standalone Cedar macro
/// bodies with `Rule::expr_entry`.
#[doc(hidden)]
pub fn parse(rule: Rule, source: &str) -> Result<Pairs<'_>, pest::error::Error<Rule>> {
    generated::DogwoodParser::parse(rule, source)
}

/// Split an optional UTF-8 byte-order mark from the policy text.
///
/// Returned spans and tokens are relative to `source_without_bom`.
pub fn split_bom(source: &str) -> (&str, &str) {
    match source.strip_prefix('\u{feff}') {
        Some(rest) => ("\u{feff}", rest),
        None => ("", source),
    }
}

/// A lossless lexical token category.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Whitespace,
    Comment,
    String,
    Identifier,
    Number,
    Symbol,
    Other,
}

/// One lossless source token.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'source> {
    pub kind: TokenKind,
    pub text: &'source str,
    pub span: Span,
}

impl Token<'_> {
    pub fn is_whitespace(self) -> bool {
        self.kind == TokenKind::Whitespace
    }

    pub fn is_comment(self) -> bool {
        self.kind == TokenKind::Comment
    }
}

/// The only lexical failure possible without interpreting the grammar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnterminatedString {
    pub span: Span,
}

/// Tokenize the complete source without discarding any byte.
pub fn tokenize(source: &str) -> Result<Vec<Token<'_>>, UnterminatedString> {
    let mut tokens = Vec::new();
    let mut index = 0;

    while index < source.len() {
        let rest = &source[index..];
        let first = rest.chars().next().expect("index is inside source");

        let (kind, len) = if first.is_whitespace() {
            (TokenKind::Whitespace, take_while(rest, char::is_whitespace))
        } else if first == '"' {
            (
                TokenKind::String,
                string_end(rest).ok_or(UnterminatedString {
                    span: Span::new(index, source.len()),
                })?,
            )
        } else if rest.starts_with("//") {
            (
                TokenKind::Comment,
                rest.find(['\n', '\r']).unwrap_or(rest.len()),
            )
        } else if first.is_ascii_alphabetic() || first == '_' {
            (
                TokenKind::Identifier,
                take_while(rest, |character| {
                    character.is_ascii_alphanumeric() || character == '_'
                }),
            )
        } else if first.is_ascii_digit() {
            (
                TokenKind::Number,
                take_while(rest, |character| character.is_ascii_digit()),
            )
        } else if let Some(len) = symbol_len(rest) {
            (TokenKind::Symbol, len)
        } else {
            let len = take_while(rest, |character| {
                !character.is_whitespace()
                    && character != '"'
                    && !character.is_ascii_alphanumeric()
                    && character != '_'
                    && symbol_len_at(character).is_none()
            });
            (TokenKind::Other, len.max(first.len_utf8()))
        };

        tokens.push(Token {
            kind,
            text: &source[index..index + len],
            span: Span::new(index, index + len),
        });
        index += len;
    }

    Ok(tokens)
}

fn take_while(source: &str, predicate: impl Fn(char) -> bool) -> usize {
    source
        .char_indices()
        .find_map(|(index, character)| (!predicate(character)).then_some(index))
        .unwrap_or(source.len())
}

fn string_end(source: &str) -> Option<usize> {
    debug_assert!(source.starts_with('"'));
    let mut escaped = false;
    for (index, character) in source.char_indices().skip(1) {
        if escaped {
            escaped = false;
        } else if character == '\\' {
            escaped = true;
        } else if character == '"' {
            return Some(index + character.len_utf8());
        }
    }
    None
}

fn symbol_len(source: &str) -> Option<usize> {
    for symbol in ["::", "==", "!=", "<=", ">=", "&&", "||"] {
        if source.starts_with(symbol) {
            return Some(symbol.len());
        }
    }
    symbol_len_at(source.chars().next()?)
}

fn symbol_len_at(character: char) -> Option<usize> {
    matches!(
        character,
        '(' | ')'
            | '['
            | ']'
            | '{'
            | '}'
            | ','
            | ';'
            | '@'
            | '.'
            | ':'
            | '?'
            | '+'
            | '-'
            | '*'
            | '/'
            | '%'
            | '!'
            | '<'
            | '>'
            | '='
    )
    .then_some(character.len_utf8())
}

/// A top-level concrete-syntax item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ItemKind {
    Definition,
    Policy,
}

/// The source spans that describe one top-level definition or policy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Span,
    /// Policy annotations, the policy head, and each condition clause.
    ///
    /// Definitions have one part covering the whole definition. The final
    /// policy part includes the terminating semicolon.
    pub line_parts: Vec<Span>,
}

/// The grammar-derived outline of a complete Dogwood policy document.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Document {
    pub items: Vec<Item>,
}

/// Parse a complete policy document and retain the spans useful to
/// source-preserving tools.
pub fn parse_document(source: &str) -> Result<Document, pest::error::Error<Rule>> {
    let mut pairs = parse(Rule::policies, source)?;
    let policies = pairs.next().expect("policies produces one top-level pair");
    let items = policies
        .into_inner()
        .filter_map(|pair| match pair.as_rule() {
            Rule::def_decl => Some(definition_item(pair)),
            Rule::policy => Some(policy_item(pair)),
            Rule::EOI => None,
            _ => None,
        })
        .collect();
    Ok(Document { items })
}

fn definition_item(pair: Pair<'_>) -> Item {
    let span = span_of(&pair);
    Item {
        kind: ItemKind::Definition,
        span,
        line_parts: vec![span],
    }
}

fn policy_item(pair: Pair<'_>) -> Item {
    let span = span_of(&pair);
    let mut annotations = Vec::new();
    let mut conditions = Vec::new();
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::annotation => annotations.push(span_of(&child)),
            Rule::cond => conditions.push(span_of(&child)),
            _ => {}
        }
    }

    let mut line_parts = annotations.clone();
    let head_start = annotations.last().map_or(span.start, |part| part.end);
    if conditions.is_empty() {
        line_parts.push(Span::new(head_start, span.end));
    } else {
        line_parts.push(Span::new(head_start, conditions[0].start));
        for (index, condition) in conditions.iter().enumerate() {
            let end = conditions
                .get(index + 1)
                .map_or(span.end, |next| next.start);
            line_parts.push(Span::new(condition.start, end));
        }
    }
    line_parts.retain(|part| part.start < part.end);

    Item {
        kind: ItemKind::Policy,
        span,
        line_parts,
    }
}

fn span_of(pair: &Pair<'_>) -> Span {
    let span = pair.as_span();
    Span::new(span.start(), span.end())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lossless_tokens_reconstruct_the_source() {
        let source =
            "// note\n@id(\"a,  b\") permit (principal, action, resource) when { a && b };";
        let tokens = tokenize(source).expect("tokenizes");
        assert_eq!(
            tokens.iter().map(|token| token.text).collect::<String>(),
            source
        );
        assert!(tokens.iter().any(|token| token.kind == TokenKind::Comment));
        assert!(tokens.iter().any(|token| token.kind == TokenKind::String));
    }

    #[test]
    fn document_outline_uses_grammar_boundaries() {
        let source = "def cedar ok(?x) { ?x == true }; \
            @id(\"a\") permit (principal, action, resource) \
            when { true } unless { false };";
        let document = parse_document(source).expect("parses");
        assert_eq!(document.items.len(), 2);
        assert_eq!(document.items[0].kind, ItemKind::Definition);
        assert_eq!(document.items[1].kind, ItemKind::Policy);
        assert_eq!(
            document.items[1]
                .line_parts
                .iter()
                .map(|span| span.text(source).trim())
                .collect::<Vec<_>>(),
            [
                "@id(\"a\")",
                "permit (principal, action, resource)",
                "when { true }",
                "unless { false };"
            ]
        );
    }

    #[test]
    fn unterminated_strings_are_reported_by_the_lossless_lexer() {
        let source = "permit (principal, action, resource) when { \"unfinished };";
        let error = tokenize(source).expect_err("unterminated string");
        assert_eq!(error.span.start, source.find('"').expect("opening quote"));
        assert_eq!(error.span.end, source.len());
    }
}
