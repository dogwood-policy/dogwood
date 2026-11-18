use std::error::Error;
use std::fmt;

use dogwood_lsp::analysis::{MAX_SEMANTIC_TOKENS, Token, ValidationError, validate_tokens};
#[cfg(test)]
use lsp_types::Position;
use lsp_types::SemanticToken;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EncodingError {
    InvalidTokens(ValidationError),
    InvalidOffset(usize),
    #[cfg(test)]
    OffsetInLineTerminator(usize),
    PositionTooLarge,
}

impl fmt::Display for EncodingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTokens(error) => write!(formatter, "invalid semantic tokens: {error}"),
            Self::InvalidOffset(offset) => write!(formatter, "invalid source offset {offset}"),
            #[cfg(test)]
            Self::OffsetInLineTerminator(offset) => {
                write!(
                    formatter,
                    "source offset {offset} is inside a line terminator"
                )
            }
            Self::PositionTooLarge => formatter.write_str("semantic token position exceeds u32"),
        }
    }
}

impl Error for EncodingError {}

impl From<ValidationError> for EncodingError {
    fn from(error: ValidationError) -> Self {
        Self::InvalidTokens(error)
    }
}

#[derive(Clone, Copy, Debug)]
struct SourceLine {
    start: usize,
    content_end: usize,
}

#[derive(Clone, Copy, Debug)]
struct LineCursor {
    line_index: usize,
    byte_offset: usize,
    utf16_column: u32,
}

impl LineCursor {
    const fn new(line_index: usize, byte_offset: usize) -> Self {
        Self {
            line_index,
            byte_offset,
            utf16_column: 0,
        }
    }

    fn advance_to(&mut self, source: &str, offset: usize) -> Result<u32, EncodingError> {
        let text = source
            .get(self.byte_offset..offset)
            .ok_or(EncodingError::InvalidOffset(offset))?;
        let length = utf16_len(text)?;
        self.utf16_column = self
            .utf16_column
            .checked_add(length)
            .ok_or(EncodingError::PositionTooLarge)?;
        self.byte_offset = offset;
        Ok(length)
    }
}

pub(crate) fn encode_tokens(
    source: &str,
    tokens: Vec<Token>,
) -> Result<Vec<SemanticToken>, EncodingError> {
    let tokens = validate_tokens(source, tokens)?;
    if tokens.is_empty() {
        return Ok(Vec::new());
    }

    let lines = source_lines(source)?;
    let mut encoded = Vec::with_capacity(tokens.len());
    let mut cursor = None;
    let mut previous_line = 0;
    let mut previous_start = 0;

    for token in tokens {
        let first_line = lines.partition_point(|line| line.content_end <= token.span.start());

        for (line_offset, line) in lines[first_line..].iter().enumerate() {
            if line.start >= token.span.end() {
                break;
            }

            let start = token.span.start().max(line.start);
            let end = token.span.end().min(line.content_end);
            if start >= end {
                continue;
            }

            let line_index = first_line + line_offset;
            let cursor = cursor.get_or_insert_with(|| LineCursor::new(line_index, line.start));
            if cursor.line_index != line_index {
                *cursor = LineCursor::new(line_index, line.start);
            }

            cursor.advance_to(source, start)?;
            let start_column = cursor.utf16_column;
            let length = cursor.advance_to(source, end)?;
            if length == 0 {
                continue;
            }

            let line = u32::try_from(line_index).map_err(|_| EncodingError::PositionTooLarge)?;
            let delta_line = line
                .checked_sub(previous_line)
                .ok_or(EncodingError::PositionTooLarge)?;
            let delta_start = if delta_line == 0 {
                start_column
                    .checked_sub(previous_start)
                    .ok_or(EncodingError::PositionTooLarge)?
            } else {
                start_column
            };
            push_semantic_token(
                &mut encoded,
                SemanticToken {
                    delta_line,
                    delta_start,
                    length,
                    token_type: token.kind.legend_index(),
                    token_modifiers_bitset: token
                        .modifier
                        .map_or(0, |modifier| modifier.legend_bit()),
                },
            )?;
            previous_line = line;
            previous_start = start_column;
        }
    }

    Ok(encoded)
}

fn push_semantic_token(
    tokens: &mut Vec<SemanticToken>,
    token: SemanticToken,
) -> Result<(), EncodingError> {
    if tokens.len() == MAX_SEMANTIC_TOKENS {
        return Err(ValidationError::SemanticTokenLimitExceeded {
            limit: MAX_SEMANTIC_TOKENS,
        }
        .into());
    }

    tokens.push(token);
    Ok(())
}

#[cfg(test)]
fn position_at(source: &str, offset: usize) -> Result<Position, EncodingError> {
    if offset > source.len() || !source.is_char_boundary(offset) {
        return Err(EncodingError::InvalidOffset(offset));
    }

    for (line_index, line) in source_lines(source)?.into_iter().enumerate() {
        if offset >= line.start && offset <= line.content_end {
            return position_on_line(source, line_index, line, offset);
        }
        if offset < line.start {
            return Err(EncodingError::OffsetInLineTerminator(offset));
        }
    }

    Err(EncodingError::InvalidOffset(offset))
}

#[cfg(test)]
fn position_on_line(
    source: &str,
    line_index: usize,
    line: SourceLine,
    offset: usize,
) -> Result<Position, EncodingError> {
    let prefix = source
        .get(line.start..offset)
        .ok_or(EncodingError::InvalidOffset(offset))?;
    Ok(Position::new(
        u32::try_from(line_index).map_err(|_| EncodingError::PositionTooLarge)?,
        utf16_len(prefix)?,
    ))
}

fn utf16_len(text: &str) -> Result<u32, EncodingError> {
    u32::try_from(text.encode_utf16().count()).map_err(|_| EncodingError::PositionTooLarge)
}

fn source_lines(source: &str) -> Result<Vec<SourceLine>, EncodingError> {
    let bytes = source.as_bytes();
    let mut lines = Vec::new();
    let mut line_start = 0;
    let mut index = 0;

    while index < bytes.len() {
        let terminator_len = match bytes[index] {
            b'\r' if bytes.get(index + 1) == Some(&b'\n') => 2,
            b'\r' | b'\n' => 1,
            _ => {
                index += 1;
                continue;
            }
        };

        push_source_line(
            &mut lines,
            SourceLine {
                start: line_start,
                content_end: index,
            },
        )?;
        index += terminator_len;
        line_start = index;
    }

    push_source_line(
        &mut lines,
        SourceLine {
            start: line_start,
            content_end: source.len(),
        },
    )?;
    Ok(lines)
}

fn push_source_line(lines: &mut Vec<SourceLine>, line: SourceLine) -> Result<(), EncodingError> {
    if lines.len() == MAX_SEMANTIC_TOKENS {
        return Err(ValidationError::SemanticTokenLimitExceeded {
            limit: MAX_SEMANTIC_TOKENS,
        }
        .into());
    }

    lines.push(line);
    Ok(())
}

#[cfg(test)]
mod tests {
    use dogwood_lsp::analysis::{ByteSpan, MAX_SEMANTIC_TOKENS, Token, ValidationError};
    use dogwood_lsp::legend::{TokenKind, TokenModifier};
    use lsp_types::{Position, SemanticToken};

    use super::{EncodingError, encode_tokens, position_at};

    fn token(start: usize, end: usize, kind: TokenKind, modifier: Option<TokenModifier>) -> Token {
        Token::new(
            ByteSpan::new(start, end).expect("test span should be valid"),
            kind,
            modifier,
        )
    }

    #[test]
    fn positions_count_utf16_code_units() {
        let source = "a\u{00e9}\u{1f600}z\nq\r\nr";

        assert_eq!(position_at(source, 0), Ok(Position::new(0, 0)));
        assert_eq!(position_at(source, 1), Ok(Position::new(0, 1)));
        assert_eq!(position_at(source, 3), Ok(Position::new(0, 2)));
        assert_eq!(position_at(source, 7), Ok(Position::new(0, 4)));
        assert_eq!(position_at(source, 8), Ok(Position::new(0, 5)));
        assert_eq!(position_at(source, 9), Ok(Position::new(1, 0)));
        assert_eq!(position_at(source, 10), Ok(Position::new(1, 1)));
        assert_eq!(position_at(source, 12), Ok(Position::new(2, 0)));
        assert_eq!(position_at(source, 13), Ok(Position::new(2, 1)));
    }

    #[test]
    fn positions_reject_utf8_boundaries_and_the_middle_of_crlf() {
        let source = "\u{1f600}\r\n";

        assert_eq!(position_at(source, 1), Err(EncodingError::InvalidOffset(1)));
        assert_eq!(
            position_at(source, 5),
            Err(EncodingError::OffsetInLineTerminator(5))
        );
        assert_eq!(position_at(source, 6), Ok(Position::new(1, 0)));
    }

    #[test]
    fn same_line_tokens_use_relative_start_deltas() {
        let source = "aa bb cc";
        let encoded = encode_tokens(
            source,
            vec![
                token(0, 2, TokenKind::Variable, None),
                token(3, 5, TokenKind::String, None),
                token(6, 8, TokenKind::Number, None),
            ],
        )
        .expect("tokens should encode");

        assert_eq!(
            encoded,
            vec![
                SemanticToken {
                    delta_line: 0,
                    delta_start: 0,
                    length: 2,
                    token_type: TokenKind::Variable.legend_index(),
                    token_modifiers_bitset: 0,
                },
                SemanticToken {
                    delta_line: 0,
                    delta_start: 3,
                    length: 2,
                    token_type: TokenKind::String.legend_index(),
                    token_modifiers_bitset: 0,
                },
                SemanticToken {
                    delta_line: 0,
                    delta_start: 3,
                    length: 2,
                    token_type: TokenKind::Number.legend_index(),
                    token_modifiers_bitset: 0,
                },
            ]
        );
    }

    #[test]
    fn multiline_tokens_are_split_without_line_terminators() {
        let source = "ab\n\u{1f600}x\r\nyz";
        let encoded = encode_tokens(
            source,
            vec![token(1, source.len(), TokenKind::String, None)],
        )
        .expect("multiline token should encode");

        assert_eq!(
            encoded,
            vec![
                SemanticToken {
                    delta_line: 0,
                    delta_start: 1,
                    length: 1,
                    token_type: TokenKind::String.legend_index(),
                    token_modifiers_bitset: 0,
                },
                SemanticToken {
                    delta_line: 1,
                    delta_start: 0,
                    length: 3,
                    token_type: TokenKind::String.legend_index(),
                    token_modifiers_bitset: 0,
                },
                SemanticToken {
                    delta_line: 1,
                    delta_start: 0,
                    length: 2,
                    token_type: TokenKind::String.legend_index(),
                    token_modifiers_bitset: 0,
                },
            ]
        );
    }

    #[test]
    fn empty_continuation_lines_do_not_emit_zero_length_tokens() {
        let source = "a\n\nb";
        let encoded = encode_tokens(
            source,
            vec![token(0, source.len(), TokenKind::Comment, None)],
        )
        .expect("token should encode");

        assert_eq!(encoded.len(), 2);
        assert_eq!(encoded[0].length, 1);
        assert_eq!(encoded[1].delta_line, 2);
        assert_eq!(encoded[1].length, 1);
    }

    #[test]
    fn tokens_at_line_terminator_boundaries_only_emit_content() {
        let source = "a\r\nb\n\rc\r";
        let encoded = encode_tokens(
            source,
            vec![
                token(1, 2, TokenKind::Comment, None),
                token(2, 4, TokenKind::String, None),
                token(4, 5, TokenKind::Operator, None),
                token(5, 7, TokenKind::Number, None),
                token(7, 8, TokenKind::Punctuation, None),
            ],
        )
        .expect("boundary tokens should encode");

        assert_eq!(
            encoded,
            vec![
                SemanticToken {
                    delta_line: 1,
                    delta_start: 0,
                    length: 1,
                    token_type: TokenKind::String.legend_index(),
                    token_modifiers_bitset: 0,
                },
                SemanticToken {
                    delta_line: 2,
                    delta_start: 0,
                    length: 1,
                    token_type: TokenKind::Number.legend_index(),
                    token_modifiers_bitset: 0,
                },
            ]
        );
    }

    #[test]
    fn many_multiline_tokens_preserve_exact_utf16_deltas() {
        const LINE_COUNT: usize = 4_096;
        const TOKENS_PER_LINE: usize = 3;

        let mut source = String::new();
        let mut tokens = Vec::with_capacity(LINE_COUNT * TOKENS_PER_LINE);

        for line_index in 0..LINE_COUNT {
            let line_start = source.len();
            source.push_str("a \u{1f600} z");
            tokens.extend([
                token(line_start, line_start + 1, TokenKind::Variable, None),
                token(line_start + 2, line_start + 6, TokenKind::String, None),
                token(line_start + 7, line_start + 8, TokenKind::Number, None),
            ]);

            if line_index + 1 < LINE_COUNT {
                source.push_str(match line_index % 3 {
                    0 => "\n",
                    1 => "\r",
                    _ => "\r\n",
                });
            }
        }

        let encoded = encode_tokens(&source, tokens).expect("all dense tokens should encode");

        assert_eq!(encoded.len(), LINE_COUNT * TOKENS_PER_LINE);
        for (line_index, line_tokens) in encoded.as_chunks::<TOKENS_PER_LINE>().0.iter().enumerate()
        {
            assert_eq!(
                *line_tokens,
                [
                    SemanticToken {
                        delta_line: u32::from(line_index != 0),
                        delta_start: 0,
                        length: 1,
                        token_type: TokenKind::Variable.legend_index(),
                        token_modifiers_bitset: 0,
                    },
                    SemanticToken {
                        delta_line: 0,
                        delta_start: 2,
                        length: 2,
                        token_type: TokenKind::String.legend_index(),
                        token_modifiers_bitset: 0,
                    },
                    SemanticToken {
                        delta_line: 0,
                        delta_start: 3,
                        length: 1,
                        token_type: TokenKind::Number.legend_index(),
                        token_modifiers_bitset: 0,
                    },
                ],
                "unexpected semantic-token group on source line {line_index}"
            );
        }
    }

    #[test]
    fn many_single_line_tokens_advance_utf16_columns_monotonically() {
        const TOKEN_COUNT: usize = 16_384;
        const CHARACTER: &str = "\u{1f600}";

        let mut source = String::with_capacity(TOKEN_COUNT * CHARACTER.len());
        let mut tokens = Vec::with_capacity(TOKEN_COUNT);
        for _ in 0..TOKEN_COUNT {
            let start = source.len();
            source.push_str(CHARACTER);
            tokens.push(token(start, source.len(), TokenKind::String, None));
        }

        let encoded = encode_tokens(&source, tokens).expect("dense tokens should encode");

        assert_eq!(encoded.len(), TOKEN_COUNT);
        for (index, token) in encoded.into_iter().enumerate() {
            assert_eq!(
                token,
                SemanticToken {
                    delta_line: 0,
                    delta_start: u32::from(index != 0) * 2,
                    length: 2,
                    token_type: TokenKind::String.legend_index(),
                    token_modifiers_bitset: 0,
                },
                "unexpected semantic token at index {index}"
            );
        }
    }

    #[test]
    fn punctuation_and_declarations_use_the_frozen_legend_bits() {
        let encoded = encode_tokens(
            "; name",
            vec![
                token(0, 1, TokenKind::Punctuation, None),
                token(2, 6, TokenKind::Variable, Some(TokenModifier::Declaration)),
            ],
        )
        .expect("tokens should encode");

        assert_eq!(encoded[0].token_type, TokenKind::Operator.legend_index());
        assert_eq!(encoded[0].token_modifiers_bitset, 0);
        assert_eq!(encoded[1].token_type, TokenKind::Variable.legend_index());
        assert_eq!(
            encoded[1].token_modifiers_bitset,
            TokenModifier::Declaration.legend_bit()
        );
    }

    #[test]
    fn empty_input_produces_empty_semantic_token_data() {
        assert_eq!(encode_tokens("permit();", Vec::new()), Ok(Vec::new()));
    }

    #[test]
    fn empty_tokens_skip_the_line_table_for_newline_dense_source() {
        let source = "\n".repeat(MAX_SEMANTIC_TOKENS + 1);

        assert_eq!(encode_tokens(&source, Vec::new()), Ok(Vec::new()));
    }

    #[test]
    fn source_line_table_is_bounded() {
        let mut source = "\n".repeat(MAX_SEMANTIC_TOKENS);
        let token_start = source.len();
        source.push('+');

        assert_eq!(
            encode_tokens(
                &source,
                vec![token(token_start, source.len(), TokenKind::Operator, None,)],
            ),
            Err(EncodingError::InvalidTokens(
                ValidationError::SemanticTokenLimitExceeded {
                    limit: MAX_SEMANTIC_TOKENS,
                }
            ))
        );
    }

    #[test]
    fn multiline_token_segments_are_bounded() {
        let mut source = String::with_capacity(MAX_SEMANTIC_TOKENS + 2);
        source.push_str("a\n");
        source.push_str(&"=".repeat(MAX_SEMANTIC_TOKENS));

        let mut tokens = Vec::with_capacity(MAX_SEMANTIC_TOKENS);
        tokens.push(token(0, 3, TokenKind::String, None));
        tokens.extend(
            (3..source.len()).map(|start| token(start, start + 1, TokenKind::Operator, None)),
        );
        assert_eq!(tokens.len(), MAX_SEMANTIC_TOKENS);

        assert_eq!(
            encode_tokens(&source, tokens),
            Err(EncodingError::InvalidTokens(
                ValidationError::SemanticTokenLimitExceeded {
                    limit: MAX_SEMANTIC_TOKENS,
                }
            ))
        );
    }

    #[test]
    fn invalid_byte_spans_are_rejected_before_encoding() {
        let invalid_boundary = token(1, 2, TokenKind::String, None);
        assert!(matches!(
            encode_tokens("\u{1f600}", vec![invalid_boundary]),
            Err(EncodingError::InvalidTokens(
                ValidationError::InvalidCharacterBoundary { .. }
            ))
        ));

        let out_of_bounds = token(0, 2, TokenKind::String, None);
        assert!(matches!(
            encode_tokens("a", vec![out_of_bounds]),
            Err(EncodingError::InvalidTokens(
                ValidationError::OutOfBounds { .. }
            ))
        ));
    }
}
