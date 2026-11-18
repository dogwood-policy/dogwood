use dogwood_lsp::analysis::{Token, analyze_event_schema, analyze_lexical};
use dogwood_lsp::frontend_event_schema;
use dogwood_lsp::legend::{TokenKind, TokenModifier};

const BASIC: &str = include_str!("fixtures/dogwood/m6/basic.dwschema");
const COMPREHENSIVE: &str = include_str!("fixtures/dogwood/m6/comprehensive.dwschema");
const UNICODE_CRLF: &str = include_str!("fixtures/dogwood/m6/unicode-crlf.dwschema");
const MALFORMED: &str = include_str!("fixtures/dogwood/m6/malformed.dwschema");
const INCOMPLETE: &str = include_str!("fixtures/dogwood/m6/incomplete.dwschema");
const UPSTREAM_CUSTOM: &str =
    include_str!("fixtures/dogwood/m6/upstream/1110-custom-kinds.dwschema");
const UPSTREAM_PIN: &str = include_str!("fixtures/dogwood/m6/upstream/1118-nested-pin.dwschema");

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Expected {
    bytes: (usize, usize),
    position: (u32, u32),
    utf16_length: u32,
    slice: &'static str,
    kind: TokenKind,
    declaration: bool,
    delta: [u32; 5],
}

const fn e(
    bytes: (usize, usize),
    position: (u32, u32),
    utf16_length: u32,
    slice: &'static str,
    kind: TokenKind,
    declaration: bool,
    delta: [u32; 5],
) -> Expected {
    Expected {
        bytes,
        position,
        utf16_length,
        slice,
        kind,
        declaration,
        delta,
    }
}

const COMPREHENSIVE_EXPECTED: &[Expected] = &[
    e(
        (0, 10),
        (0, 0),
        10,
        "max_window",
        TokenKind::Keyword,
        false,
        [0, 0, 10, 12, 0],
    ),
    e(
        (11, 12),
        (0, 11),
        1,
        "=",
        TokenKind::Operator,
        false,
        [0, 11, 1, 17, 0],
    ),
    e(
        (13, 15),
        (0, 13),
        2,
        "30",
        TokenKind::Number,
        false,
        [0, 2, 2, 16, 0],
    ),
    e(
        (16, 45),
        (0, 16),
        27,
        "// legal interval trivia 🚀",
        TokenKind::Comment,
        false,
        [0, 3, 27, 14, 0],
    ),
    e(
        (46, 47),
        (1, 0),
        1,
        "d",
        TokenKind::Number,
        false,
        [1, 0, 1, 16, 0],
    ),
    e(
        (49, 57),
        (3, 0),
        8,
        "decision",
        TokenKind::Keyword,
        false,
        [2, 0, 8, 12, 0],
    ),
    e(
        (58, 63),
        (3, 9),
        5,
        "event",
        TokenKind::Keyword,
        false,
        [0, 9, 5, 12, 0],
    ),
    e(
        (64, 65),
        (3, 15),
        1,
        "<",
        TokenKind::Operator,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (65, 71),
        (3, 16),
        6,
        "Action",
        TokenKind::TypeParameter,
        true,
        [0, 1, 6, 3, 1],
    ),
    e(
        (71, 72),
        (3, 22),
        1,
        ">",
        TokenKind::Operator,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (72, 74),
        (3, 23),
        2,
        "::",
        TokenKind::Punctuation,
        false,
        [0, 1, 2, 17, 0],
    ),
    e(
        (74, 81),
        (3, 25),
        7,
        "request",
        TokenKind::Event,
        true,
        [0, 2, 7, 8, 1],
    ),
    e(
        (82, 83),
        (3, 33),
        1,
        "{",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (88, 89),
        (4, 4),
        1,
        ".",
        TokenKind::Punctuation,
        false,
        [1, 4, 1, 17, 0],
    ),
    e(
        (89, 90),
        (4, 5),
        1,
        ".",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (90, 91),
        (4, 6),
        1,
        ".",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (91, 97),
        (4, 7),
        6,
        "inputs",
        TokenKind::Function,
        false,
        [0, 1, 6, 9, 0],
    ),
    e(
        (97, 98),
        (4, 13),
        1,
        "(",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (98, 104),
        (4, 14),
        6,
        "Action",
        TokenKind::TypeParameter,
        false,
        [0, 1, 6, 3, 0],
    ),
    e(
        (104, 105),
        (4, 20),
        1,
        ")",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (105, 106),
        (4, 21),
        1,
        ",",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (111, 112),
        (5, 4),
        1,
        ".",
        TokenKind::Punctuation,
        false,
        [1, 4, 1, 17, 0],
    ),
    e(
        (112, 113),
        (5, 5),
        1,
        ".",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (113, 114),
        (5, 6),
        1,
        ".",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (114, 121),
        (5, 7),
        7,
        "outputs",
        TokenKind::Function,
        false,
        [0, 1, 7, 9, 0],
    ),
    e(
        (121, 122),
        (5, 14),
        1,
        "(",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (122, 128),
        (5, 15),
        6,
        "Action",
        TokenKind::TypeParameter,
        false,
        [0, 1, 6, 3, 0],
    ),
    e(
        (128, 129),
        (5, 21),
        1,
        ")",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (129, 130),
        (5, 22),
        1,
        ",",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (135, 138),
        (6, 4),
        3,
        "pin",
        TokenKind::Keyword,
        false,
        [1, 4, 3, 12, 0],
    ),
    e(
        (139, 144),
        (6, 8),
        5,
        "actor",
        TokenKind::Property,
        true,
        [0, 4, 5, 6, 1],
    ),
    e(
        (144, 145),
        (6, 13),
        1,
        ":",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (146, 159),
        (6, 15),
        13,
        "principalType",
        TokenKind::Function,
        false,
        [0, 2, 13, 9, 0],
    ),
    e(
        (159, 160),
        (6, 28),
        1,
        "(",
        TokenKind::Punctuation,
        false,
        [0, 13, 1, 17, 0],
    ),
    e(
        (160, 166),
        (6, 29),
        6,
        "Action",
        TokenKind::TypeParameter,
        false,
        [0, 1, 6, 3, 0],
    ),
    e(
        (166, 167),
        (6, 35),
        1,
        ")",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (168, 169),
        (6, 37),
        1,
        "=",
        TokenKind::Operator,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (170, 179),
        (6, 39),
        9,
        "principal",
        TokenKind::Variable,
        false,
        [0, 2, 9, 5, 0],
    ),
    e(
        (179, 180),
        (6, 48),
        1,
        ".",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (180, 190),
        (6, 49),
        10,
        "department",
        TokenKind::Property,
        false,
        [0, 1, 10, 6, 0],
    ),
    e(
        (190, 191),
        (6, 59),
        1,
        ",",
        TokenKind::Punctuation,
        false,
        [0, 10, 1, 17, 0],
    ),
    e(
        (196, 202),
        (7, 4),
        6,
        "target",
        TokenKind::Property,
        true,
        [1, 4, 6, 6, 1],
    ),
    e(
        (202, 203),
        (7, 10),
        1,
        ":",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (204, 216),
        (7, 12),
        12,
        "resourceType",
        TokenKind::Function,
        false,
        [0, 2, 12, 9, 0],
    ),
    e(
        (216, 217),
        (7, 24),
        1,
        "(",
        TokenKind::Punctuation,
        false,
        [0, 12, 1, 17, 0],
    ),
    e(
        (217, 223),
        (7, 25),
        6,
        "Action",
        TokenKind::TypeParameter,
        false,
        [0, 1, 6, 3, 0],
    ),
    e(
        (223, 224),
        (7, 31),
        1,
        ")",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (224, 225),
        (7, 32),
        1,
        ",",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (230, 233),
        (8, 4),
        3,
        "pin",
        TokenKind::Property,
        true,
        [1, 4, 3, 6, 1],
    ),
    e(
        (233, 234),
        (8, 7),
        1,
        ":",
        TokenKind::Punctuation,
        false,
        [0, 3, 1, 17, 0],
    ),
    e(
        (235, 241),
        (8, 9),
        6,
        "String",
        TokenKind::Type,
        false,
        [0, 2, 6, 1, 0],
    ),
    e(
        (241, 242),
        (8, 15),
        1,
        ",",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (247, 253),
        (9, 4),
        6,
        "nested",
        TokenKind::Property,
        true,
        [1, 4, 6, 6, 1],
    ),
    e(
        (253, 254),
        (9, 10),
        1,
        ":",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (255, 256),
        (9, 12),
        1,
        "{",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (265, 268),
        (10, 8),
        3,
        "pin",
        TokenKind::Keyword,
        false,
        [1, 8, 3, 12, 0],
    ),
    e(
        (269, 278),
        (10, 12),
        9,
        "target_id",
        TokenKind::Property,
        true,
        [0, 4, 9, 6, 1],
    ),
    e(
        (278, 279),
        (10, 21),
        1,
        ":",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (280, 284),
        (10, 23),
        4,
        "Acme",
        TokenKind::Namespace,
        false,
        [0, 2, 4, 0, 0],
    ),
    e(
        (284, 286),
        (10, 27),
        2,
        "::",
        TokenKind::Punctuation,
        false,
        [0, 4, 2, 17, 0],
    ),
    e(
        (286, 291),
        (10, 29),
        5,
        "Types",
        TokenKind::Namespace,
        false,
        [0, 2, 5, 0, 0],
    ),
    e(
        (291, 293),
        (10, 34),
        2,
        "::",
        TokenKind::Punctuation,
        false,
        [0, 5, 2, 17, 0],
    ),
    e(
        (293, 303),
        (10, 36),
        10,
        "Identifier",
        TokenKind::Type,
        false,
        [0, 2, 10, 1, 0],
    ),
    e(
        (304, 305),
        (10, 47),
        1,
        "=",
        TokenKind::Operator,
        false,
        [0, 11, 1, 17, 0],
    ),
    e(
        (306, 314),
        (10, 49),
        8,
        "resource",
        TokenKind::Variable,
        false,
        [0, 2, 8, 5, 0],
    ),
    e(
        (314, 315),
        (10, 57),
        1,
        ".",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (315, 317),
        (10, 58),
        2,
        "id",
        TokenKind::Property,
        false,
        [0, 1, 2, 6, 0],
    ),
    e(
        (317, 318),
        (10, 60),
        1,
        ",",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (327, 330),
        (11, 8),
        3,
        "pin",
        TokenKind::Keyword,
        false,
        [1, 8, 3, 12, 0],
    ),
    e(
        (331, 338),
        (11, 12),
        7,
        "session",
        TokenKind::Property,
        true,
        [0, 4, 7, 6, 1],
    ),
    e(
        (338, 339),
        (11, 19),
        1,
        ":",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (340, 346),
        (11, 21),
        6,
        "String",
        TokenKind::Type,
        false,
        [0, 2, 6, 1, 0],
    ),
    e(
        (347, 348),
        (11, 28),
        1,
        "=",
        TokenKind::Operator,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (349, 356),
        (11, 30),
        7,
        "context",
        TokenKind::Variable,
        false,
        [0, 2, 7, 5, 0],
    ),
    e(
        (356, 357),
        (11, 37),
        1,
        ".",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (357, 364),
        (11, 38),
        7,
        "session",
        TokenKind::Property,
        false,
        [0, 1, 7, 6, 0],
    ),
    e(
        (364, 365),
        (11, 45),
        1,
        ".",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (365, 367),
        (11, 46),
        2,
        "id",
        TokenKind::Property,
        false,
        [0, 1, 2, 6, 0],
    ),
    e(
        (367, 368),
        (11, 48),
        1,
        ",",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (373, 374),
        (12, 4),
        1,
        "}",
        TokenKind::Punctuation,
        false,
        [1, 4, 1, 17, 0],
    ),
    e(
        (374, 375),
        (12, 5),
        1,
        ",",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (376, 377),
        (13, 0),
        1,
        "}",
        TokenKind::Punctuation,
        false,
        [1, 0, 1, 17, 0],
    ),
    e(
        (379, 384),
        (15, 0),
        5,
        "event",
        TokenKind::Keyword,
        false,
        [2, 0, 5, 12, 0],
    ),
    e(
        (385, 386),
        (15, 6),
        1,
        "<",
        TokenKind::Operator,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (386, 392),
        (15, 7),
        6,
        "Action",
        TokenKind::TypeParameter,
        true,
        [0, 1, 6, 3, 1],
    ),
    e(
        (392, 393),
        (15, 13),
        1,
        ">",
        TokenKind::Operator,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (393, 395),
        (15, 14),
        2,
        "::",
        TokenKind::Punctuation,
        false,
        [0, 1, 2, 17, 0],
    ),
    e(
        (395, 400),
        (15, 16),
        5,
        "audit",
        TokenKind::Event,
        true,
        [0, 2, 5, 8, 1],
    ),
    e(
        (401, 402),
        (15, 22),
        1,
        "{",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (407, 412),
        (16, 4),
        5,
        "value",
        TokenKind::Property,
        true,
        [1, 4, 5, 6, 1],
    ),
    e(
        (412, 413),
        (16, 9),
        1,
        ":",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (414, 418),
        (16, 11),
        4,
        "Acme",
        TokenKind::Namespace,
        false,
        [0, 2, 4, 0, 0],
    ),
    e(
        (418, 420),
        (16, 15),
        2,
        "::",
        TokenKind::Punctuation,
        false,
        [0, 4, 2, 17, 0],
    ),
    e(
        (420, 425),
        (16, 17),
        5,
        "Types",
        TokenKind::Namespace,
        false,
        [0, 2, 5, 0, 0],
    ),
    e(
        (425, 427),
        (16, 22),
        2,
        "::",
        TokenKind::Punctuation,
        false,
        [0, 5, 2, 17, 0],
    ),
    e(
        (427, 432),
        (16, 24),
        5,
        "Value",
        TokenKind::Type,
        false,
        [0, 2, 5, 1, 0],
    ),
    e(
        (432, 433),
        (16, 29),
        1,
        ",",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (434, 435),
        (17, 0),
        1,
        "}",
        TokenKind::Punctuation,
        false,
        [1, 0, 1, 17, 0],
    ),
];

fn position(source: &str, offset: usize) -> (u32, u32) {
    let prefix = &source[..offset];
    let line = u32::try_from(prefix.matches('\n').count()).unwrap();
    let line_start = prefix.rfind('\n').map_or(0, |index| index + 1);
    let character = u32::try_from(source[line_start..offset].encode_utf16().count()).unwrap();
    (line, character)
}

fn encoded(tokens: &[Token], source: &str) -> Vec<[u32; 5]> {
    let mut previous_line = 0;
    let mut previous_start = 0;
    tokens
        .iter()
        .map(|token| {
            let (line, start) = position(source, token.span.start());
            let length = u32::try_from(
                source[token.span.start()..token.span.end()]
                    .encode_utf16()
                    .count(),
            )
            .unwrap();
            let delta_line = line - previous_line;
            let delta_start = if delta_line == 0 {
                start - previous_start
            } else {
                start
            };
            previous_line = line;
            previous_start = start;
            [
                delta_line,
                delta_start,
                length,
                token.kind.legend_index(),
                token.modifier.map_or(0, TokenModifier::legend_bit),
            ]
        })
        .collect()
}

#[test]
fn comprehensive_schema_has_exact_spans_utf16_positions_and_encoded_deltas() {
    let tokens = analyze_event_schema(COMPREHENSIVE).unwrap();
    let deltas = encoded(&tokens, COMPREHENSIVE);
    assert_eq!(tokens.len(), COMPREHENSIVE_EXPECTED.len());
    for ((token, delta), expected) in tokens.iter().zip(deltas).zip(COMPREHENSIVE_EXPECTED) {
        assert_eq!(
            (token.span.start(), token.span.end()),
            expected.bytes,
            "{expected:?}"
        );
        assert_eq!(
            &COMPREHENSIVE[token.span.start()..token.span.end()],
            expected.slice
        );
        assert_eq!(
            position(COMPREHENSIVE, token.span.start()),
            expected.position
        );
        assert_eq!(
            u32::try_from(
                COMPREHENSIVE[token.span.start()..token.span.end()]
                    .encode_utf16()
                    .count()
            )
            .unwrap(),
            expected.utf16_length
        );
        assert_eq!(token.kind, expected.kind);
        assert_eq!(
            token.modifier == Some(TokenModifier::Declaration),
            expected.declaration
        );
        assert_eq!(delta, expected.delta);
    }
}

#[test]
fn max_horizon_directive_is_classified() {
    let source = "max_window = 1h\nmax_horizon = 48h\n\ndecision event <A>::request { requestId: String }\n";
    let tokens = analyze_event_schema(source).unwrap();
    let classified = tokens
        .iter()
        .map(|token| (&source[token.span.start()..token.span.end()], token.kind))
        .collect::<Vec<_>>();
    assert!(classified.contains(&("max_window", TokenKind::Keyword)), "{classified:?}");
    assert!(classified.contains(&("max_horizon", TokenKind::Keyword)), "{classified:?}");
    assert!(classified.contains(&("48", TokenKind::Number)), "{classified:?}");
}

#[test]
fn complete_fixtures_are_parser_backed_sorted_and_nonoverlapping() {
    for source in [
        BASIC,
        COMPREHENSIVE,
        UNICODE_CRLF,
        UPSTREAM_CUSTOM,
        UPSTREAM_PIN,
    ] {
        let first = frontend_event_schema::classify(source).expect("fixture should parse");
        let second = frontend_event_schema::classify(source).expect("fixture should repeat");
        assert_eq!(first, second);
        assert!(first.iter().all(|span| {
            span.start < span.end
                && span.end <= source.len()
                && source.is_char_boundary(span.start)
                && source.is_char_boundary(span.end)
        }));
        assert!(first.windows(2).all(|pair| pair[0].end <= pair[1].start));
    }
    assert!(
        UNICODE_CRLF
            .as_bytes()
            .windows(2)
            .any(|pair| pair == b"\r\n")
    );
    assert!(UNICODE_CRLF.contains('🚀'));
}

#[test]
fn every_required_schema_classification_is_present() {
    let tokens = analyze_event_schema(COMPREHENSIVE).unwrap();
    let classified = tokens
        .iter()
        .map(|token| {
            (
                &COMPREHENSIVE[token.span.start()..token.span.end()],
                token.kind,
                token.modifier,
            )
        })
        .collect::<Vec<_>>();

    for keyword in ["max_window", "decision", "event", "pin"] {
        assert!(classified.contains(&(keyword, TokenKind::Keyword, None)));
    }
    for selector in ["inputs", "outputs", "principalType", "resourceType"] {
        assert!(classified.contains(&(selector, TokenKind::Function, None)));
    }
    for root in ["principal", "resource", "context"] {
        assert!(classified.contains(&(root, TokenKind::Variable, None)));
    }
    assert!(classified.contains(&(
        "Action",
        TokenKind::TypeParameter,
        Some(TokenModifier::Declaration)
    )));
    assert!(classified.contains(&("Action", TokenKind::TypeParameter, None)));
    assert!(classified.contains(&(
        "request",
        TokenKind::Event,
        Some(TokenModifier::Declaration)
    )));
    assert!(classified.contains(&("pin", TokenKind::Property, Some(TokenModifier::Declaration))));
    assert!(classified.contains(&("Acme", TokenKind::Namespace, None)));
    assert!(classified.contains(&("Types", TokenKind::Namespace, None)));
    assert!(classified.contains(&("Identifier", TokenKind::Type, None)));
}

#[test]
fn malformed_and_incomplete_sources_keep_the_complete_lexical_stream() {
    for source in [MALFORMED, INCOMPLETE, "event <A>::x { ...inputs(B), }"] {
        assert!(frontend_event_schema::classify(source).is_none());
        assert_eq!(
            analyze_event_schema(source).unwrap(),
            analyze_lexical(source).unwrap()
        );
    }
}

#[test]
fn generated_valid_forms_and_every_utf8_truncation_are_fallback_safe() {
    for index in 1..=12 {
        let source = format!(
            "// generated {index} 🚀\nmax_window = {index} h\n\
             decision event <Action{index}>::request{index} {{ \
             ...inputs(Action{index}), pin owner: Ns::User = principal.id, \
             nested: {{ pin session: String = context.session.id, }}, }}"
        );
        assert!(
            frontend_event_schema::classify(&source).is_some(),
            "generated schema {index} should parse"
        );

        for end in (0..=source.len()).filter(|end| source.is_char_boundary(*end)) {
            let prefix = &source[..end];
            let first = analyze_event_schema(prefix).unwrap();
            let second = analyze_event_schema(prefix).unwrap();
            assert_eq!(first, second, "schema {index}, truncation {end}");
            assert!(first.iter().all(|token| {
                token.span.start() < token.span.end()
                    && token.span.end() <= prefix.len()
                    && prefix.is_char_boundary(token.span.start())
                    && prefix.is_char_boundary(token.span.end())
            }));
            assert!(
                first
                    .windows(2)
                    .all(|pair| pair[0].span.end() <= pair[1].span.start())
            );
            if frontend_event_schema::classify(prefix).is_none() {
                assert_eq!(
                    first,
                    analyze_lexical(prefix).unwrap(),
                    "schema {index}, truncation {end}"
                );
            }
        }
    }
}
