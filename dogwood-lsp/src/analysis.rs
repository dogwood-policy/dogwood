use std::error::Error;
use std::fmt;

use crate::legend::{TokenKind, TokenModifier};
use crate::{frontend_event_schema, frontend_semantic};

pub use crate::frontend_semantic::SemanticInput;

pub const MAX_SEMANTIC_TOKENS: usize = 262_144;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ByteSpan {
    start: usize,
    end: usize,
}

impl ByteSpan {
    pub fn new(start: usize, end: usize) -> Result<Self, SpanError> {
        if start >= end {
            return Err(SpanError { start, end });
        }

        Ok(Self { start, end })
    }

    pub const fn start(self) -> usize {
        self.start
    }

    pub const fn end(self) -> usize {
        self.end
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpanError {
    pub start: usize,
    pub end: usize,
}

impl fmt::Display for SpanError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "byte span must be non-empty and increasing: {}..{}",
            self.start, self.end
        )
    }
}

impl Error for SpanError {}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Token {
    pub span: ByteSpan,
    pub kind: TokenKind,
    pub modifier: Option<TokenModifier>,
}

impl Token {
    pub const fn new(span: ByteSpan, kind: TokenKind, modifier: Option<TokenModifier>) -> Self {
        Self {
            span,
            kind,
            modifier,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValidationError {
    SemanticTokenLimitExceeded { limit: usize },
    OutOfBounds { span: ByteSpan, source_len: usize },
    InvalidCharacterBoundary { span: ByteSpan },
    DuplicateSpan { span: ByteSpan },
    Overlap { earlier: ByteSpan, later: ByteSpan },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SemanticTokenLimitExceeded { limit } => {
                write!(formatter, "semantic token limit of {limit} exceeded")
            }
            Self::OutOfBounds { span, source_len } => write!(
                formatter,
                "token span {}..{} exceeds source length {source_len}",
                span.start, span.end
            ),
            Self::InvalidCharacterBoundary { span } => write!(
                formatter,
                "token span {}..{} is not on UTF-8 character boundaries",
                span.start, span.end
            ),
            Self::DuplicateSpan { span } => {
                write!(
                    formatter,
                    "duplicate token span {}..{}",
                    span.start, span.end
                )
            }
            Self::Overlap { earlier, later } => write!(
                formatter,
                "token span {}..{} overlaps {}..{}",
                earlier.start, earlier.end, later.start, later.end
            ),
        }
    }
}

impl Error for ValidationError {}

pub fn validate_tokens(
    source: &str,
    mut tokens: Vec<Token>,
) -> Result<Vec<Token>, ValidationError> {
    if tokens.len() > MAX_SEMANTIC_TOKENS {
        return Err(ValidationError::SemanticTokenLimitExceeded {
            limit: MAX_SEMANTIC_TOKENS,
        });
    }

    for token in &tokens {
        if token.span.end > source.len() {
            return Err(ValidationError::OutOfBounds {
                span: token.span,
                source_len: source.len(),
            });
        }

        if !source.is_char_boundary(token.span.start) || !source.is_char_boundary(token.span.end) {
            return Err(ValidationError::InvalidCharacterBoundary { span: token.span });
        }
    }

    tokens.sort_unstable();

    for pair in tokens.windows(2) {
        let earlier = pair[0].span;
        let later = pair[1].span;

        if earlier == later {
            return Err(ValidationError::DuplicateSpan { span: earlier });
        }

        if later.start < earlier.end {
            return Err(ValidationError::Overlap { earlier, later });
        }
    }

    Ok(tokens)
}

fn is_identifier_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_'
}

fn is_identifier_continue(byte: u8) -> bool {
    is_identifier_start(byte) || byte.is_ascii_digit()
}

fn is_keyword(identifier: &str) -> bool {
    matches!(
        identifier,
        "true"
            | "false"
            | "if"
            | "then"
            | "else"
            | "in"
            | "has"
            | "like"
            | "is"
            | "permit"
            | "forbid"
            | "when"
            | "unless"
            | "principal"
            | "action"
            | "resource"
            | "context"
            | "def"
            | "cedar"
            | "temporal"
            | "guardrails"
            | "since"
            | "tp"
            | "exists"
            | "formerly"
            | "previous"
            | "sum"
            | "count"
            | "for"
            | "where"
            | "within"
            | "decimal"
    )
}

fn lexical_token(start: usize, end: usize, kind: TokenKind) -> Token {
    Token::new(ByteSpan { start, end }, kind, None)
}

fn push_lexical_token(tokens: &mut Vec<Token>, token: Token) -> Result<(), ValidationError> {
    if tokens.len() == MAX_SEMANTIC_TOKENS {
        return Err(ValidationError::SemanticTokenLimitExceeded {
            limit: MAX_SEMANTIC_TOKENS,
        });
    }

    tokens.push(token);
    Ok(())
}

fn scan_identifier_end(bytes: &[u8], start: usize) -> usize {
    let mut end = start + 1;
    while end < bytes.len() && is_identifier_continue(bytes[end]) {
        end += 1;
    }
    end
}

fn scan_string_end(source: &str, start: usize) -> (usize, bool) {
    let bytes = source.as_bytes();
    let mut cursor = start + 1;
    while cursor < source.len() {
        match bytes[cursor] {
            b'\\' => {
                cursor += 1;
                if cursor < source.len() {
                    cursor += source[cursor..]
                        .chars()
                        .next()
                        .expect("cursor is before the source end")
                        .len_utf8();
                }
            }
            b'"' => return (cursor + 1, true),
            _ => {
                cursor += source[cursor..]
                    .chars()
                    .next()
                    .expect("cursor is before the source end")
                    .len_utf8();
            }
        }
    }
    (cursor, false)
}

struct FallbackAction {
    end: usize,
    segments: Vec<ByteSpan>,
    event: Option<ByteSpan>,
}

fn scan_fallback_action(source: &str, start: usize) -> Result<FallbackAction, usize> {
    let bytes = source.as_bytes();
    let first = ByteSpan {
        start,
        end: scan_identifier_end(bytes, start),
    };
    let mut cursor = first.end;
    if !source[cursor..].starts_with("::") {
        return Err(cursor);
    }
    let mut segments = vec![first];

    while source[cursor..].starts_with("::") {
        let next = cursor + 2;
        if next == source.len() {
            return Err(next);
        }
        if bytes[next] == b'"' {
            let action = segments.last().expect("action has an identifier");
            if &source[action.start..action.end] != "Action" {
                return Err(next);
            }
            let (string_end, terminated) = scan_string_end(source, next);
            let mut event = None;
            let mut end = string_end;
            if terminated && source[string_end..].starts_with("::") {
                let event_start = string_end + 2;
                if event_start < source.len() && is_identifier_start(bytes[event_start]) {
                    let event_end = scan_identifier_end(bytes, event_start);
                    event = Some(ByteSpan {
                        start: event_start,
                        end: event_end,
                    });
                    end = event_end;
                }
            }
            return Ok(FallbackAction {
                end,
                segments,
                event,
            });
        }
        if !is_identifier_start(bytes[next]) {
            return Err(next);
        }
        let end = scan_identifier_end(bytes, next);
        segments.push(ByteSpan { start: next, end });
        cursor = end;
    }

    Err(cursor)
}

fn analyze_fallback_structure(source: &str) -> Result<Vec<Token>, ValidationError> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut cursor = usize::from(source.starts_with('\u{feff}')) * '\u{feff}'.len_utf8();

    while cursor < source.len() {
        if source[cursor..].starts_with("//") {
            cursor += 2;
            while cursor < source.len() && !matches!(bytes[cursor], b'\r' | b'\n') {
                cursor += 1;
            }
            continue;
        }
        if bytes[cursor] == b'"' {
            cursor = scan_string_end(source, cursor).0;
            continue;
        }
        if bytes[cursor] == b'@'
            && (cursor == 0 || !is_identifier_continue(bytes[cursor - 1]))
            && bytes
                .get(cursor + 1)
                .copied()
                .is_some_and(is_identifier_start)
        {
            let start = cursor + 1;
            let end = scan_identifier_end(bytes, start);
            push_lexical_token(&mut tokens, lexical_token(start, end, TokenKind::Decorator))?;
            cursor = end;
            continue;
        }
        if is_identifier_start(bytes[cursor]) {
            match scan_fallback_action(source, cursor) {
                Ok(action) => {
                    let (action_type, namespaces) =
                        action.segments.split_last().expect("action has a segment");
                    for namespace in namespaces {
                        push_lexical_token(
                            &mut tokens,
                            lexical_token(namespace.start, namespace.end, TokenKind::Namespace),
                        )?;
                    }
                    push_lexical_token(
                        &mut tokens,
                        lexical_token(action_type.start, action_type.end, TokenKind::Type),
                    )?;
                    if let Some(event) = action.event {
                        push_lexical_token(
                            &mut tokens,
                            lexical_token(event.start, event.end, TokenKind::Event),
                        )?;
                    }
                    cursor = action.end;
                }
                Err(scanned_end) => cursor = scanned_end.max(cursor + 1),
            }
            continue;
        }
        cursor += source[cursor..]
            .chars()
            .next()
            .expect("cursor is before the source end")
            .len_utf8();
    }

    Ok(tokens)
}

pub fn analyze(source: &str) -> Result<Vec<Token>, ValidationError> {
    analyze_with_input(&SemanticInput::standalone(source))
}

pub fn analyze_with_input(input: &SemanticInput<'_>) -> Result<Vec<Token>, ValidationError> {
    let source = input.policy;
    let lexical = analyze_lexical(source)?;
    let Some(structural) = frontend_semantic::classify_with_input(input) else {
        return Ok(lexical);
    };

    let structural = structural
        .into_iter()
        .map(|span| {
            ByteSpan::new(span.start, span.end)
                .map(|byte_span| Token::new(byte_span, span.kind, span.modifier))
        })
        .collect::<Result<Vec<_>, _>>();
    let Ok(structural) = structural else {
        return Ok(lexical);
    };
    merge_structural_tokens(source, lexical, structural)
}

pub fn analyze_event_schema(source: &str) -> Result<Vec<Token>, ValidationError> {
    let lexical = analyze_lexical(source)?;
    let Some(structural) = frontend_event_schema::classify(source) else {
        return Ok(lexical);
    };

    let structural = structural
        .into_iter()
        .map(|span| {
            ByteSpan::new(span.start, span.end)
                .map(|byte_span| Token::new(byte_span, span.kind, span.modifier))
        })
        .collect::<Result<Vec<_>, _>>();
    let Ok(structural) = structural else {
        return Ok(lexical);
    };
    merge_structural_tokens(source, lexical, structural)
}

pub fn analyze_lexical(source: &str) -> Result<Vec<Token>, ValidationError> {
    let bytes = source.as_bytes();
    let mut tokens = analyze_fallback_structure(source)?;
    let structural_count = tokens.len();
    let mut cursor = usize::from(source.starts_with('\u{feff}')) * '\u{feff}'.len_utf8();

    while cursor < source.len() {
        let start = cursor;

        if source[start..].starts_with("//") {
            cursor += 2;
            while cursor < source.len() && !matches!(bytes[cursor], b'\r' | b'\n') {
                cursor += 1;
            }
            push_lexical_token(
                &mut tokens,
                lexical_token(start, cursor, TokenKind::Comment),
            )?;
            continue;
        }

        if bytes[start] == b'"' {
            cursor = scan_string_end(source, start).0;
            push_lexical_token(&mut tokens, lexical_token(start, cursor, TokenKind::String))?;
            continue;
        }

        if is_identifier_start(bytes[start]) {
            cursor = scan_identifier_end(bytes, start);
            let structurally_classified = tokens[..structural_count]
                .binary_search_by_key(&(start, cursor), |token| (token.span.start, token.span.end))
                .is_ok();
            if !structurally_classified && is_keyword(&source[start..cursor]) {
                push_lexical_token(
                    &mut tokens,
                    lexical_token(start, cursor, TokenKind::Keyword),
                )?;
            }
            continue;
        }

        if bytes[start].is_ascii_digit() {
            cursor += 1;
            while cursor < source.len() && bytes[cursor].is_ascii_digit() {
                cursor += 1;
            }
            if cursor < source.len() && matches!(bytes[cursor], b's' | b'm' | b'h' | b'd') {
                cursor += 1;
            }
            push_lexical_token(&mut tokens, lexical_token(start, cursor, TokenKind::Number))?;
            continue;
        }

        let next_two = bytes.get(start..start.saturating_add(2));
        let (length, kind) = if matches!(
            next_two,
            Some(b"||" | b"&&" | b"<=" | b">=" | b"!=" | b"==")
        ) {
            (2, Some(TokenKind::Operator))
        } else if source[start..].starts_with("::") {
            (2, Some(TokenKind::Punctuation))
        } else if matches!(
            bytes[start],
            b'<' | b'>' | b'=' | b'+' | b'-' | b'*' | b'/' | b'%' | b'!' | b'&' | b'|'
        ) {
            (1, Some(TokenKind::Operator))
        } else if matches!(
            bytes[start],
            b'(' | b')'
                | b'{'
                | b'}'
                | b'['
                | b']'
                | b','
                | b';'
                | b'.'
                | b':'
                | b'@'
                | b'?'
                | b'$'
        ) {
            (1, Some(TokenKind::Punctuation))
        } else {
            (0, None)
        };

        if let Some(kind) = kind {
            cursor += length;
            push_lexical_token(&mut tokens, lexical_token(start, cursor, kind))?;
        } else {
            cursor += source[start..]
                .chars()
                .next()
                .expect("cursor is before the source end")
                .len_utf8();
        }
    }

    validate_tokens(source, tokens)
}

fn merge_structural_tokens(
    source: &str,
    lexical: Vec<Token>,
    structural: Vec<Token>,
) -> Result<Vec<Token>, ValidationError> {
    let structural = match validate_tokens(source, structural) {
        Ok(structural) => structural,
        Err(_) => return Ok(lexical),
    };
    let mut merged = Vec::with_capacity(lexical.len().saturating_add(structural.len()));
    let mut structural_index = 0;

    for token in &lexical {
        while structural
            .get(structural_index)
            .is_some_and(|structural| structural.span.end() <= token.span.start())
        {
            structural_index += 1;
        }
        let conflicts = structural
            .get(structural_index)
            .is_some_and(|structural| structural.span.start() < token.span.end());
        if !conflicts {
            merged.push(*token);
        }
    }
    merged.extend(structural);
    match validate_tokens(source, merged) {
        Ok(merged) => Ok(merged),
        Err(_) => Ok(lexical),
    }
}

// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#[cfg(all(test, unix))]
mod tests {
    use super::{
        ByteSpan, MAX_SEMANTIC_TOKENS, SemanticInput, SpanError, Token, ValidationError, analyze,
        analyze_lexical, analyze_with_input, validate_tokens,
    };
    use crate::legend::{TokenKind, TokenModifier};

    fn span(start: usize, end: usize) -> ByteSpan {
        ByteSpan::new(start, end).expect("test span should be non-empty")
    }

    fn token(start: usize, end: usize, kind: TokenKind) -> Token {
        Token::new(span(start, end), kind, None)
    }

    fn analyzed(source: &str) -> Vec<Token> {
        analyze(source).expect("lexical analysis should produce valid tokens")
    }

    fn lexical(source: &str) -> Vec<Token> {
        analyze_lexical(source).expect("lexical analysis should produce valid tokens")
    }

    fn lexemes(source: &str) -> Vec<(&str, TokenKind)> {
        analyzed(source)
            .into_iter()
            .map(|token| (&source[token.span.start()..token.span.end()], token.kind))
            .collect()
    }

    #[test]
    fn every_reserved_word_is_a_keyword() {
        let words = [
            "true",
            "false",
            "if",
            "then",
            "else",
            "in",
            "has",
            "like",
            "is",
            "permit",
            "forbid",
            "when",
            "unless",
            "principal",
            "action",
            "resource",
            "context",
            "def",
            "cedar",
            "temporal",
            "guardrails",
            "since",
            "tp",
            "exists",
            "formerly",
            "previous",
            "sum",
            "count",
            "for",
            "where",
            "within",
            "decimal",
        ];
        let source = words.join(" ");

        assert_eq!(
            lexemes(&source),
            words
                .iter()
                .map(|word| (*word, TokenKind::Keyword))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn identifiers_and_keyword_prefixes_are_unclassified() {
        assert!(
            analyzed("truth trueValue permit_ _when WHEN request response datetime duration ip")
                .is_empty()
        );
    }

    #[test]
    fn lexical_fallback_recognizes_only_narrow_policy_structure() {
        let source = concat!(
            "@id(\"policy\") ",
            "Acme::Net::Action::\"net:request\"::attempt{} ",
            "Action::\"root:id\" ",
            "unrelated Thing::\"value\" \"plain\"::suffix email@domain"
        );

        assert_eq!(
            lexemes(source),
            vec![
                ("@", TokenKind::Punctuation),
                ("id", TokenKind::Decorator),
                ("(", TokenKind::Punctuation),
                ("\"policy\"", TokenKind::String),
                (")", TokenKind::Punctuation),
                ("Acme", TokenKind::Namespace),
                ("::", TokenKind::Punctuation),
                ("Net", TokenKind::Namespace),
                ("::", TokenKind::Punctuation),
                ("Action", TokenKind::Type),
                ("::", TokenKind::Punctuation),
                ("\"net:request\"", TokenKind::String),
                ("::", TokenKind::Punctuation),
                ("attempt", TokenKind::Event),
                ("{", TokenKind::Punctuation),
                ("}", TokenKind::Punctuation),
                ("Action", TokenKind::Type),
                ("::", TokenKind::Punctuation),
                ("\"root:id\"", TokenKind::String),
                ("::", TokenKind::Punctuation),
                ("\"value\"", TokenKind::String),
                ("\"plain\"", TokenKind::String),
                ("::", TokenKind::Punctuation),
                ("@", TokenKind::Punctuation),
            ]
        );
    }

    #[test]
    fn lexical_fallback_structure_does_not_escape_comments_or_strings() {
        let source = concat!(
            "// @comment Acme::Action::\"hidden\"::attempt\n",
            "\"@quoted Acme::Action::\\\"hidden\\\"::response\" ",
            "@permit Action::\"visible\"::request"
        );

        assert_eq!(
            lexemes(source),
            vec![
                (
                    "// @comment Acme::Action::\"hidden\"::attempt",
                    TokenKind::Comment,
                ),
                (
                    "\"@quoted Acme::Action::\\\"hidden\\\"::response\"",
                    TokenKind::String,
                ),
                ("@", TokenKind::Punctuation),
                ("permit", TokenKind::Decorator),
                ("Action", TokenKind::Type),
                ("::", TokenKind::Punctuation),
                ("\"visible\"", TokenKind::String),
                ("::", TokenKind::Punctuation),
                ("request", TokenKind::Event),
            ]
        );
    }

    #[test]
    fn comments_take_precedence_and_stop_before_line_endings() {
        let source = "// one / \"\rpermit// two\nforbid//// three";

        assert_eq!(
            lexemes(source),
            vec![
                ("// one / \"", TokenKind::Comment),
                ("permit", TokenKind::Keyword),
                ("// two", TokenKind::Comment),
                ("forbid", TokenKind::Keyword),
                ("//// three", TokenKind::Comment),
            ]
        );
    }

    #[test]
    fn strings_are_single_tolerant_tokens() {
        for source in [
            "\"complete\"",
            "\"escaped \\\" quote and \\\\ slash\"",
            "\"escaped unicode \\\u{1f680} stays in string\"",
            "\"invalid \\q escape\"",
            "\"unicode \u{e9}\u{1f680}\"",
            "\"line one\nline two\"",
            "\"unterminated \u{1f680}",
            "\"trailing\\",
        ] {
            assert_eq!(lexemes(source), vec![(source, TokenKind::String)]);
        }
    }

    #[test]
    fn numbers_include_one_immediate_duration_suffix() {
        let source = "0 15s 20m 3h 7d 12x 34ms -56 78_9";

        assert_eq!(
            lexemes(source),
            vec![
                ("0", TokenKind::Number),
                ("15s", TokenKind::Number),
                ("20m", TokenKind::Number),
                ("3h", TokenKind::Number),
                ("7d", TokenKind::Number),
                ("12", TokenKind::Number),
                ("34m", TokenKind::Number),
                ("-", TokenKind::Operator),
                ("56", TokenKind::Number),
                ("78", TokenKind::Number),
            ]
        );
    }

    #[test]
    fn operators_and_punctuation_use_longest_match() {
        let source = "|| && <= >= != == :: < > = + - * / % ! & | : ( ) { } [ ] , ; . @ ? $";

        assert_eq!(
            lexemes(source),
            vec![
                ("||", TokenKind::Operator),
                ("&&", TokenKind::Operator),
                ("<=", TokenKind::Operator),
                (">=", TokenKind::Operator),
                ("!=", TokenKind::Operator),
                ("==", TokenKind::Operator),
                ("::", TokenKind::Punctuation),
                ("<", TokenKind::Operator),
                (">", TokenKind::Operator),
                ("=", TokenKind::Operator),
                ("+", TokenKind::Operator),
                ("-", TokenKind::Operator),
                ("*", TokenKind::Operator),
                ("/", TokenKind::Operator),
                ("%", TokenKind::Operator),
                ("!", TokenKind::Operator),
                ("&", TokenKind::Operator),
                ("|", TokenKind::Operator),
                (":", TokenKind::Punctuation),
                ("(", TokenKind::Punctuation),
                (")", TokenKind::Punctuation),
                ("{", TokenKind::Punctuation),
                ("}", TokenKind::Punctuation),
                ("[", TokenKind::Punctuation),
                ("]", TokenKind::Punctuation),
                (",", TokenKind::Punctuation),
                (";", TokenKind::Punctuation),
                (".", TokenKind::Punctuation),
                ("@", TokenKind::Punctuation),
                ("?", TokenKind::Punctuation),
                ("$", TokenKind::Punctuation),
            ]
        );
    }

    #[test]
    fn bom_and_unknown_unicode_are_skipped_without_stalling() {
        let source = "\u{feff}\u{1f600}\u{3bb} permit \u{524d} + forbid";

        assert_eq!(
            lexemes(source),
            vec![
                ("permit", TokenKind::Keyword),
                ("+", TokenKind::Operator),
                ("forbid", TokenKind::Keyword),
            ]
        );
    }

    #[test]
    fn analysis_is_deterministic_sorted_non_overlapping_and_unmodified() {
        let source = "\u{feff}// \u{1f600}\npermit(action == \"\u{524d}\\\"\", -15m) && |";
        let first = analyzed(source);
        let second = analyzed(source);

        assert_eq!(first, second);
        assert!(first.iter().all(|token| token.modifier.is_none()));
        assert!(first.iter().all(|token| {
            token.span.start() < token.span.end()
                && source.is_char_boundary(token.span.start())
                && source.is_char_boundary(token.span.end())
        }));
        assert!(
            first
                .windows(2)
                .all(|pair| pair[0].span.end() <= pair[1].span.start())
        );
    }

    #[test]
    fn analysis_accepts_the_token_limit_and_rejects_the_next_token() {
        let mut source = "+".repeat(MAX_SEMANTIC_TOKENS);

        let tokens = analyze(&source).expect("the semantic token limit should be accepted");
        assert_eq!(tokens.len(), MAX_SEMANTIC_TOKENS);

        source.push('+');
        let error = analyze(&source).expect_err("the next token should exceed the limit");
        assert_eq!(
            error,
            ValidationError::SemanticTokenLimitExceeded {
                limit: MAX_SEMANTIC_TOKENS,
            }
        );
        assert_eq!(
            error.to_string(),
            format!("semantic token limit of {MAX_SEMANTIC_TOKENS} exceeded")
        );
    }

    #[test]
    fn validation_rejects_oversized_caller_vectors() {
        let tokens = vec![token(0, 1, TokenKind::Operator); MAX_SEMANTIC_TOKENS + 1];

        assert_eq!(
            validate_tokens("=", tokens),
            Err(ValidationError::SemanticTokenLimitExceeded {
                limit: MAX_SEMANTIC_TOKENS,
            })
        );
    }

    #[test]
    fn adjacent_sorted_tokens_are_valid() {
        let tokens = vec![
            token(0, 1, TokenKind::Keyword),
            token(1, 2, TokenKind::Punctuation),
            token(2, 3, TokenKind::Variable),
        ];

        assert_eq!(validate_tokens("abc", tokens.clone()), Ok(tokens));
    }

    #[test]
    fn unsorted_tokens_are_sorted_deterministically() {
        let first = Token::new(
            span(0, 1),
            TokenKind::Variable,
            Some(TokenModifier::Declaration),
        );
        let second = token(2, 4, TokenKind::String);
        let third = token(4, 5, TokenKind::Operator);

        assert_eq!(
            validate_tokens("abcde", vec![third, first, second]),
            Ok(vec![first, second, third])
        );
    }

    #[test]
    fn overlapping_tokens_fail() {
        assert_eq!(
            validate_tokens(
                "abcd",
                vec![
                    token(0, 3, TokenKind::String),
                    token(2, 4, TokenKind::Variable)
                ]
            ),
            Err(ValidationError::Overlap {
                earlier: span(0, 3),
                later: span(2, 4),
            })
        );
    }

    #[test]
    fn duplicate_spans_fail_even_when_kinds_differ() {
        assert_eq!(
            validate_tokens(
                "abcd",
                vec![
                    token(1, 3, TokenKind::String),
                    token(1, 3, TokenKind::Variable)
                ]
            ),
            Err(ValidationError::DuplicateSpan { span: span(1, 3) })
        );
    }

    #[test]
    fn empty_and_reversed_spans_fail_at_construction() {
        assert_eq!(ByteSpan::new(2, 2), Err(SpanError { start: 2, end: 2 }));
        assert_eq!(ByteSpan::new(3, 2), Err(SpanError { start: 3, end: 2 }));
    }

    #[test]
    fn out_of_bounds_spans_fail_validation() {
        assert_eq!(
            validate_tokens("abc", vec![token(2, 4, TokenKind::Variable)]),
            Err(ValidationError::OutOfBounds {
                span: span(2, 4),
                source_len: 3,
            })
        );
    }

    #[test]
    fn invalid_utf8_character_boundaries_fail_validation() {
        let source = "a\u{1f333}b";

        assert_eq!(
            validate_tokens(source, vec![token(1, 2, TokenKind::String)]),
            Err(ValidationError::InvalidCharacterBoundary { span: span(1, 2) })
        );
        assert_eq!(
            validate_tokens(source, vec![token(2, 5, TokenKind::String)]),
            Err(ValidationError::InvalidCharacterBoundary { span: span(2, 5) })
        );
    }

    #[test]
    fn incomplete_source_returns_the_complete_lexical_fallback() {
        let source =
            "permit (principal, action == App::Action::\"Read\", resource) when { context.input.";

        assert_eq!(analyzed(source), lexical(source));
    }

    #[test]
    fn valid_source_overlays_structure_and_preserves_nonconflicting_lexical_tokens() {
        let source = "permit (principal, action, resource) when { context.input.count == 3 };";
        let tokens = analyzed(source);
        let lexemes = tokens
            .iter()
            .map(|token| {
                (
                    &source[token.span.start()..token.span.end()],
                    token.kind,
                    token.modifier,
                )
            })
            .collect::<Vec<_>>();

        assert!(lexemes.contains(&("principal", TokenKind::Variable, None)));
        assert!(lexemes.contains(&("input", TokenKind::Property, None)));
        assert!(lexemes.contains(&("count", TokenKind::Property, None)));
        assert!(lexemes.contains(&("==", TokenKind::Operator, None)));
        assert!(lexemes.contains(&("3", TokenKind::Number, None)));
    }

    #[test]
    fn structural_overlay_limit_failure_returns_exact_lexical_stream() {
        let policy = "permit(principal,action,resource) when { context.foo == 1 };";
        let policy_lexical = analyze_lexical(policy).expect("policy lexical scan should succeed");
        let comments = MAX_SEMANTIC_TOKENS
            .checked_sub(policy_lexical.len())
            .expect("policy should fit below the token limit");
        let source = format!("{}{policy}", "//\n".repeat(comments));
        let lexical = analyze_lexical(&source).expect("exact-boundary lexical scan should succeed");

        assert_eq!(lexical.len(), MAX_SEMANTIC_TOKENS);
        assert!(
            crate::frontend_semantic::classify(&source).is_some(),
            "production strict classification must reach the structural merge"
        );
        assert_eq!(
            analyze(&source),
            Ok(lexical),
            "structural overflow must atomically retain the complete lexical stream"
        );
    }

    #[test]
    fn malformed_resolved_service_inputs_return_exact_lexical_stream() {
        let policy = "permit(principal,action,resource);";
        let lexical = analyze_lexical(policy).expect("lexical scan should succeed");
        let inputs = [
            SemanticInput {
                policy,
                event_schema: Some("!"),
                providers: None,
                macros: None,
            },
            SemanticInput {
                policy,
                event_schema: None,
                providers: Some("!"),
                macros: None,
            },
            SemanticInput {
                policy,
                event_schema: None,
                providers: None,
                macros: Some("def cedar broken("),
            },
        ];

        for input in inputs {
            assert_eq!(
                analyze_with_input(&input),
                Ok(lexical.clone()),
                "malformed service input must retain lexical fallback: {input:?}"
            );
        }
    }
}
