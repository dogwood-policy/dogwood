// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#![cfg(unix)]

use dogwood_lsp::analysis::{analyze, analyze_lexical};
use dogwood_lsp::frontend_semantic;
use dogwood_lsp::legend::{TokenKind, TokenModifier};

/// The Cedar fixture with CRLF line endings, whatever line endings the checkout
/// gave the file.
fn cedar() -> String {
    include_str!("fixtures/dogwood/m5/cedar-crlf-unicode.dw")
        .replace("\r\n", "\n")
        .replace('\n', "\r\n")
}
const MIXED: &str = include_str!("fixtures/dogwood/m5/mixed-temporal.dw");
const MACROS: &str = include_str!("fixtures/dogwood/m5/macros.dw");
const NESTED_CALLS: &str = include_str!("fixtures/dogwood/m5/nested-calls.dw");
const INTERVAL_CALL: &str = include_str!("fixtures/dogwood/m5/interval-call.dw");
const INCOMPLETE: &str = include_str!("fixtures/dogwood/m5/incomplete.dw");
const ACTION_STRUCTURE: &str = concat!(
    "@id(\"namespaced\")\n",
    "permit(principal, action == Acme::Action::\"net:request\", resource)\n",
    "when temporal { formerly within 1h Acme::Action::\"net:request\"::response{} };\n",
    "@id(\"root\")\n",
    "permit(principal, action == Action::\"root:id\", resource)\n",
    "when temporal { formerly within 1h Action::\"root:id\"::attempt{} };",
);
const INCOMPLETE_STRUCTURE: &str = concat!(
    "// 🚀\r\n",
    "@id(\"draft-🚀\")\r\n",
    "Acme::Action::\"net:request\"::attempt{ unrelated \"plain\"::suffix",
);
const HAS_IF: &str = "permit(principal, action, resource) when { context has if } when { if true then true else false };";
const COMMENT_WINDOW: &str = r#"permit(principal, action, resource) when temporal {
formerly within 1 // window gap
h Drupe::Action::"GetStockInfo"::request{}
};"#;
const COMMENT_ARGUMENT: &str = r#"def temporal r(?w, ?e) { formerly within ?w ?e };
permit(principal, action, resource) when temporal {
r(1 // argument gap
h, Drupe::Action::"GetStockInfo"::request{})
};"#;
const ADJACENT_INTERVAL: &str = r#"permit(principal, action, resource) when temporal { formerly within 2h Drupe::Action::"GetStockInfo"::request{} };"#;
const SPACED_INTERVAL: &str = r#"permit(principal, action, resource) when temporal { formerly within 3 h Drupe::Action::"GetStockInfo"::request{} };"#;
const UPSTREAM_CEDAR: &str =
    include_str!("fixtures/dogwood/m5/upstream/cedar_documentation_0001_policy_1.dw");
const UPSTREAM_MACRO: &str = include_str!("fixtures/dogwood/m5/upstream/macro_0034_policy_1.dw");
const UPSTREAM_TEMPORAL: &str =
    include_str!("fixtures/dogwood/m5/upstream/temporal_0808_policy_1.dw");

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Expected {
    byte_start: usize,
    byte_end: usize,
    line: u32,
    character: u32,
    slice: &'static str,
    kind: TokenKind,
    declaration: bool,
    delta: [u32; 5],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CorpusExpected {
    byte_start: usize,
    byte_end: usize,
    line: u32,
    character: u32,
    utf16_length: u32,
    slice: &'static str,
    kind: TokenKind,
    declaration: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CommentExpected<'a> {
    byte_start: usize,
    byte_end: usize,
    slice: &'a str,
    position: (u32, u32),
    delta: [u32; 5],
}

const fn corpus_e(
    bytes: (usize, usize),
    position: (u32, u32),
    utf16_length: u32,
    slice: &'static str,
    kind: TokenKind,
    declaration: bool,
) -> CorpusExpected {
    CorpusExpected {
        byte_start: bytes.0,
        byte_end: bytes.1,
        line: position.0,
        character: position.1,
        utf16_length,
        slice,
        kind,
        declaration,
    }
}

const fn e(
    bytes: (usize, usize),
    position: (u32, u32),
    slice: &'static str,
    kind: TokenKind,
    declaration: bool,
    delta: [u32; 5],
) -> Expected {
    Expected {
        byte_start: bytes.0,
        byte_end: bytes.1,
        line: position.0,
        character: position.1,
        slice,
        kind,
        declaration,
        delta,
    }
}

const CEDAR_EXPECTED: &[Expected] = &[
    e(
        (0, 12),
        (0, 0),
        "// cafe 🚀",
        TokenKind::Comment,
        false,
        [0, 0, 10, 14, 0],
    ),
    e(
        (14, 15),
        (1, 0),
        "@",
        TokenKind::Punctuation,
        false,
        [1, 0, 1, 17, 0],
    ),
    e(
        (15, 17),
        (1, 1),
        "id",
        TokenKind::Decorator,
        false,
        [0, 1, 2, 18, 0],
    ),
    e(
        (17, 18),
        (1, 3),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (18, 24),
        (1, 4),
        "\"🚀\"",
        TokenKind::String,
        false,
        [0, 1, 4, 15, 0],
    ),
    e(
        (24, 25),
        (1, 8),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 4, 1, 17, 0],
    ),
    e(
        (26, 32),
        (1, 10),
        "permit",
        TokenKind::Keyword,
        false,
        [0, 2, 6, 12, 0],
    ),
    e(
        (32, 33),
        (1, 16),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (33, 42),
        (1, 17),
        "principal",
        TokenKind::Variable,
        false,
        [0, 1, 9, 5, 0],
    ),
    e(
        (42, 43),
        (1, 26),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (44, 50),
        (1, 28),
        "action",
        TokenKind::Variable,
        false,
        [0, 2, 6, 5, 0],
    ),
    e(
        (51, 53),
        (1, 35),
        "==",
        TokenKind::Operator,
        false,
        [0, 7, 2, 17, 0],
    ),
    e(
        (54, 58),
        (1, 38),
        "Acme",
        TokenKind::Namespace,
        false,
        [0, 3, 4, 0, 0],
    ),
    e(
        (58, 60),
        (1, 42),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 4, 2, 17, 0],
    ),
    e(
        (60, 66),
        (1, 44),
        "Action",
        TokenKind::Type,
        false,
        [0, 2, 6, 1, 0],
    ),
    e(
        (66, 68),
        (1, 50),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 6, 2, 17, 0],
    ),
    e(
        (68, 74),
        (1, 52),
        "\"Read\"",
        TokenKind::String,
        false,
        [0, 2, 6, 15, 0],
    ),
    e(
        (74, 75),
        (1, 58),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (76, 84),
        (1, 60),
        "resource",
        TokenKind::Variable,
        false,
        [0, 2, 8, 5, 0],
    ),
    e(
        (84, 85),
        (1, 68),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (87, 91),
        (2, 0),
        "when",
        TokenKind::Keyword,
        false,
        [1, 0, 4, 12, 0],
    ),
    e(
        (92, 93),
        (2, 5),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (94, 101),
        (2, 7),
        "context",
        TokenKind::Variable,
        false,
        [0, 2, 7, 5, 0],
    ),
    e(
        (101, 102),
        (2, 14),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (102, 107),
        (2, 15),
        "input",
        TokenKind::Property,
        false,
        [0, 1, 5, 6, 0],
    ),
    e(
        (107, 108),
        (2, 20),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (108, 113),
        (2, 21),
        "owner",
        TokenKind::Property,
        false,
        [0, 1, 5, 6, 0],
    ),
    e(
        (113, 114),
        (2, 26),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (114, 122),
        (2, 27),
        "contains",
        TokenKind::Method,
        false,
        [0, 1, 8, 10, 0],
    ),
    e(
        (122, 123),
        (2, 35),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (123, 127),
        (2, 36),
        "\"é\"",
        TokenKind::String,
        false,
        [0, 1, 3, 15, 0],
    ),
    e(
        (127, 128),
        (2, 39),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 3, 1, 17, 0],
    ),
    e(
        (129, 130),
        (2, 41),
        "}",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (130, 131),
        (2, 42),
        ";",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
];

const MIXED_EXPECTED: &[Expected] = &[
    e(
        (0, 6),
        (0, 0),
        "permit",
        TokenKind::Keyword,
        false,
        [0, 0, 6, 12, 0],
    ),
    e(
        (6, 7),
        (0, 6),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (7, 16),
        (0, 7),
        "principal",
        TokenKind::Variable,
        false,
        [0, 1, 9, 5, 0],
    ),
    e(
        (16, 17),
        (0, 16),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (18, 24),
        (0, 18),
        "action",
        TokenKind::Variable,
        false,
        [0, 2, 6, 5, 0],
    ),
    e(
        (24, 25),
        (0, 24),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (26, 34),
        (0, 26),
        "resource",
        TokenKind::Variable,
        false,
        [0, 2, 8, 5, 0],
    ),
    e(
        (34, 35),
        (0, 34),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (36, 40),
        (0, 36),
        "when",
        TokenKind::Keyword,
        false,
        [0, 2, 4, 12, 0],
    ),
    e(
        (41, 49),
        (0, 41),
        "temporal",
        TokenKind::Keyword,
        false,
        [0, 5, 8, 12, 0],
    ),
    e(
        (50, 51),
        (0, 50),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (54, 62),
        (1, 2),
        "formerly",
        TokenKind::Keyword,
        false,
        [1, 2, 8, 12, 0],
    ),
    e(
        (63, 69),
        (1, 11),
        "within",
        TokenKind::Keyword,
        false,
        [0, 9, 6, 12, 0],
    ),
    e(
        (70, 71),
        (1, 18),
        "1",
        TokenKind::Number,
        false,
        [0, 7, 1, 16, 0],
    ),
    e(
        (71, 72),
        (1, 19),
        "h",
        TokenKind::Number,
        false,
        [0, 1, 1, 16, 0],
    ),
    e(
        (73, 77),
        (1, 21),
        "Acme",
        TokenKind::Namespace,
        false,
        [0, 2, 4, 0, 0],
    ),
    e(
        (77, 79),
        (1, 25),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 4, 2, 17, 0],
    ),
    e(
        (79, 85),
        (1, 27),
        "Action",
        TokenKind::Type,
        false,
        [0, 2, 6, 1, 0],
    ),
    e(
        (85, 87),
        (1, 33),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 6, 2, 17, 0],
    ),
    e(
        (87, 93),
        (1, 35),
        "\"Read\"",
        TokenKind::String,
        false,
        [0, 2, 6, 15, 0],
    ),
    e(
        (93, 95),
        (1, 41),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 6, 2, 17, 0],
    ),
    e(
        (95, 103),
        (1, 43),
        "response",
        TokenKind::Event,
        false,
        [0, 2, 8, 8, 0],
    ),
    e(
        (103, 104),
        (1, 51),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (109, 115),
        (2, 4),
        "output",
        TokenKind::Property,
        false,
        [1, 4, 6, 6, 0],
    ),
    e(
        (115, 116),
        (2, 10),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (116, 121),
        (2, 11),
        "owner",
        TokenKind::Property,
        false,
        [0, 1, 5, 6, 0],
    ),
    e(
        (121, 122),
        (2, 16),
        ":",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (123, 130),
        (2, 18),
        "context",
        TokenKind::Variable,
        false,
        [0, 2, 7, 5, 0],
    ),
    e(
        (130, 131),
        (2, 25),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (131, 136),
        (2, 26),
        "input",
        TokenKind::Property,
        false,
        [0, 1, 5, 6, 0],
    ),
    e(
        (136, 137),
        (2, 31),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (137, 142),
        (2, 32),
        "owner",
        TokenKind::Property,
        false,
        [0, 1, 5, 6, 0],
    ),
    e(
        (145, 146),
        (3, 2),
        "}",
        TokenKind::Punctuation,
        false,
        [1, 2, 1, 17, 0],
    ),
    e(
        (147, 148),
        (4, 0),
        "}",
        TokenKind::Punctuation,
        false,
        [1, 0, 1, 17, 0],
    ),
    e(
        (148, 149),
        (4, 1),
        ";",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
];

const MACROS_EXPECTED: &[Expected] = &[
    e(
        (0, 3),
        (0, 0),
        "def",
        TokenKind::Keyword,
        false,
        [0, 0, 3, 12, 0],
    ),
    e(
        (4, 9),
        (0, 4),
        "cedar",
        TokenKind::Keyword,
        false,
        [0, 4, 5, 12, 0],
    ),
    e(
        (10, 14),
        (0, 10),
        "same",
        TokenKind::Macro,
        true,
        [0, 6, 4, 11, 1],
    ),
    e(
        (14, 15),
        (0, 14),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 4, 1, 17, 0],
    ),
    e(
        (15, 21),
        (0, 15),
        "?value",
        TokenKind::Parameter,
        true,
        [0, 1, 6, 4, 1],
    ),
    e(
        (21, 22),
        (0, 21),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (23, 24),
        (0, 23),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (25, 31),
        (0, 25),
        "?value",
        TokenKind::Parameter,
        false,
        [0, 2, 6, 4, 0],
    ),
    e(
        (32, 34),
        (0, 32),
        "==",
        TokenKind::Operator,
        false,
        [0, 7, 2, 17, 0],
    ),
    e(
        (35, 44),
        (0, 35),
        "principal",
        TokenKind::Variable,
        false,
        [0, 3, 9, 5, 0],
    ),
    e(
        (45, 46),
        (0, 45),
        "}",
        TokenKind::Punctuation,
        false,
        [0, 10, 1, 17, 0],
    ),
    e(
        (46, 47),
        (0, 46),
        ";",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (48, 51),
        (1, 0),
        "def",
        TokenKind::Keyword,
        false,
        [1, 0, 3, 12, 0],
    ),
    e(
        (52, 60),
        (1, 4),
        "temporal",
        TokenKind::Keyword,
        false,
        [0, 4, 8, 12, 0],
    ),
    e(
        (61, 67),
        (1, 13),
        "recent",
        TokenKind::Macro,
        true,
        [0, 9, 6, 11, 1],
    ),
    e(
        (67, 68),
        (1, 19),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (68, 75),
        (1, 20),
        "?window",
        TokenKind::Parameter,
        true,
        [0, 1, 7, 4, 1],
    ),
    e(
        (75, 76),
        (1, 27),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (77, 83),
        (1, 29),
        "?event",
        TokenKind::Parameter,
        true,
        [0, 2, 6, 4, 1],
    ),
    e(
        (83, 84),
        (1, 35),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (85, 86),
        (1, 37),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (89, 94),
        (2, 2),
        "count",
        TokenKind::Keyword,
        false,
        [1, 2, 5, 12, 0],
    ),
    e(
        (95, 98),
        (2, 8),
        "for",
        TokenKind::Keyword,
        false,
        [0, 6, 3, 12, 0],
    ),
    e(
        (99, 100),
        (2, 12),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 4, 1, 17, 0],
    ),
    e(
        (100, 102),
        (2, 13),
        "$t",
        TokenKind::Variable,
        true,
        [0, 1, 2, 5, 1],
    ),
    e(
        (102, 103),
        (2, 15),
        ":",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (104, 113),
        (2, 17),
        "Timepoint",
        TokenKind::Type,
        false,
        [0, 2, 9, 1, 0],
    ),
    e(
        (113, 114),
        (2, 26),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (114, 115),
        (2, 27),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (116, 121),
        (2, 29),
        "where",
        TokenKind::Keyword,
        false,
        [0, 2, 5, 12, 0],
    ),
    e(
        (122, 123),
        (2, 35),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (123, 131),
        (2, 36),
        "formerly",
        TokenKind::Keyword,
        false,
        [0, 1, 8, 12, 0],
    ),
    e(
        (132, 138),
        (2, 45),
        "within",
        TokenKind::Keyword,
        false,
        [0, 9, 6, 12, 0],
    ),
    e(
        (139, 146),
        (2, 52),
        "?window",
        TokenKind::Parameter,
        false,
        [0, 7, 7, 4, 0],
    ),
    e(
        (147, 148),
        (2, 60),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (148, 154),
        (2, 61),
        "?event",
        TokenKind::Parameter,
        false,
        [0, 1, 6, 4, 0],
    ),
    e(
        (155, 157),
        (2, 68),
        "&&",
        TokenKind::Operator,
        false,
        [0, 7, 2, 17, 0],
    ),
    e(
        (158, 160),
        (2, 71),
        "tp",
        TokenKind::Keyword,
        false,
        [0, 3, 2, 12, 0],
    ),
    e(
        (160, 161),
        (2, 73),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (161, 163),
        (2, 74),
        "$t",
        TokenKind::Variable,
        false,
        [0, 1, 2, 5, 0],
    ),
    e(
        (163, 164),
        (2, 76),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (164, 165),
        (2, 77),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (165, 166),
        (2, 78),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (167, 168),
        (3, 0),
        "}",
        TokenKind::Punctuation,
        false,
        [1, 0, 1, 17, 0],
    ),
    e(
        (168, 169),
        (3, 1),
        ";",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (170, 173),
        (4, 0),
        "def",
        TokenKind::Keyword,
        false,
        [1, 0, 3, 12, 0],
    ),
    e(
        (174, 182),
        (4, 4),
        "temporal",
        TokenKind::Keyword,
        false,
        [0, 4, 8, 12, 0],
    ),
    e(
        (183, 188),
        (4, 13),
        "total",
        TokenKind::Macro,
        true,
        [0, 9, 5, 11, 1],
    ),
    e(
        (188, 189),
        (4, 18),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (189, 195),
        (4, 19),
        "?value",
        TokenKind::Parameter,
        true,
        [0, 1, 6, 4, 1],
    ),
    e(
        (195, 196),
        (4, 25),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (197, 203),
        (4, 27),
        "?event",
        TokenKind::Parameter,
        true,
        [0, 2, 6, 4, 1],
    ),
    e(
        (203, 204),
        (4, 33),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (205, 206),
        (4, 35),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (209, 212),
        (5, 2),
        "sum",
        TokenKind::Keyword,
        false,
        [1, 2, 3, 12, 0],
    ),
    e(
        (213, 219),
        (5, 6),
        "?value",
        TokenKind::Parameter,
        false,
        [0, 4, 6, 4, 0],
    ),
    e(
        (220, 223),
        (5, 13),
        "for",
        TokenKind::Keyword,
        false,
        [0, 7, 3, 12, 0],
    ),
    e(
        (224, 225),
        (5, 17),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 4, 1, 17, 0],
    ),
    e(
        (225, 231),
        (5, 18),
        "?value",
        TokenKind::Parameter,
        true,
        [0, 1, 6, 4, 1],
    ),
    e(
        (231, 232),
        (5, 24),
        ":",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (233, 237),
        (5, 26),
        "Long",
        TokenKind::Type,
        false,
        [0, 2, 4, 1, 0],
    ),
    e(
        (237, 238),
        (5, 30),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 4, 1, 17, 0],
    ),
    e(
        (238, 239),
        (5, 31),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (240, 245),
        (5, 33),
        "where",
        TokenKind::Keyword,
        false,
        [0, 2, 5, 12, 0],
    ),
    e(
        (246, 252),
        (5, 39),
        "?event",
        TokenKind::Parameter,
        false,
        [0, 6, 6, 4, 0],
    ),
    e(
        (253, 254),
        (6, 0),
        "}",
        TokenKind::Punctuation,
        false,
        [1, 0, 1, 17, 0],
    ),
    e(
        (254, 255),
        (6, 1),
        ";",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
];

const NESTED_CALLS_EXPECTED: &[Expected] = &[
    e(
        (0, 3),
        (0, 0),
        "def",
        TokenKind::Keyword,
        false,
        [0, 0, 3, 12, 0],
    ),
    e(
        (4, 9),
        (0, 4),
        "cedar",
        TokenKind::Keyword,
        false,
        [0, 4, 5, 12, 0],
    ),
    e(
        (10, 17),
        (0, 10),
        "allowed",
        TokenKind::Macro,
        true,
        [0, 6, 7, 11, 1],
    ),
    e(
        (17, 18),
        (0, 17),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (18, 24),
        (0, 18),
        "?value",
        TokenKind::Parameter,
        true,
        [0, 1, 6, 4, 1],
    ),
    e(
        (24, 25),
        (0, 24),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (26, 27),
        (0, 26),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (28, 34),
        (0, 28),
        "?value",
        TokenKind::Parameter,
        false,
        [0, 2, 6, 4, 0],
    ),
    e(
        (35, 37),
        (0, 35),
        "==",
        TokenKind::Operator,
        false,
        [0, 7, 2, 17, 0],
    ),
    e(
        (38, 42),
        (0, 38),
        "true",
        TokenKind::Keyword,
        false,
        [0, 3, 4, 12, 0],
    ),
    e(
        (43, 44),
        (0, 43),
        "}",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (44, 45),
        (0, 44),
        ";",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (46, 52),
        (1, 0),
        "permit",
        TokenKind::Keyword,
        false,
        [1, 0, 6, 12, 0],
    ),
    e(
        (52, 53),
        (1, 6),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (53, 62),
        (1, 7),
        "principal",
        TokenKind::Variable,
        false,
        [0, 1, 9, 5, 0],
    ),
    e(
        (62, 63),
        (1, 16),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (64, 70),
        (1, 18),
        "action",
        TokenKind::Variable,
        false,
        [0, 2, 6, 5, 0],
    ),
    e(
        (70, 71),
        (1, 24),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (72, 80),
        (1, 26),
        "resource",
        TokenKind::Variable,
        false,
        [0, 2, 8, 5, 0],
    ),
    e(
        (80, 81),
        (1, 34),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (82, 86),
        (1, 36),
        "when",
        TokenKind::Keyword,
        false,
        [0, 2, 4, 12, 0],
    ),
    e(
        (87, 88),
        (1, 41),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (91, 98),
        (2, 2),
        "allowed",
        TokenKind::Macro,
        false,
        [1, 2, 7, 11, 0],
    ),
    e(
        (98, 99),
        (2, 9),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (99, 104),
        (2, 10),
        "Guard",
        TokenKind::Namespace,
        false,
        [0, 1, 5, 0, 0],
    ),
    e(
        (104, 106),
        (2, 15),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 5, 2, 17, 0],
    ),
    e(
        (106, 113),
        (2, 17),
        "Allowed",
        TokenKind::Function,
        false,
        [0, 2, 7, 9, 0],
    ),
    e(
        (113, 114),
        (2, 24),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (114, 121),
        (2, 25),
        "context",
        TokenKind::Variable,
        false,
        [0, 1, 7, 5, 0],
    ),
    e(
        (121, 122),
        (2, 32),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (122, 127),
        (2, 33),
        "input",
        TokenKind::Property,
        false,
        [0, 1, 5, 6, 0],
    ),
    e(
        (127, 128),
        (2, 38),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (128, 132),
        (2, 39),
        "name",
        TokenKind::Property,
        false,
        [0, 1, 4, 6, 0],
    ),
    e(
        (132, 133),
        (2, 43),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 4, 1, 17, 0],
    ),
    e(
        (133, 134),
        (2, 44),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (134, 140),
        (2, 45),
        "result",
        TokenKind::Property,
        false,
        [0, 1, 6, 6, 0],
    ),
    e(
        (140, 141),
        (2, 51),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (141, 149),
        (2, 52),
        "contains",
        TokenKind::Method,
        false,
        [0, 1, 8, 10, 0],
    ),
    e(
        (149, 150),
        (2, 60),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (150, 155),
        (2, 61),
        "\"yes\"",
        TokenKind::String,
        false,
        [0, 1, 5, 15, 0],
    ),
    e(
        (155, 156),
        (2, 66),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 5, 1, 17, 0],
    ),
    e(
        (156, 157),
        (2, 67),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (158, 159),
        (3, 0),
        "}",
        TokenKind::Punctuation,
        false,
        [1, 0, 1, 17, 0],
    ),
    e(
        (159, 160),
        (3, 1),
        ";",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
];

const INTERVAL_CALL_EXPECTED: &[Expected] = &[
    e(
        (0, 3),
        (0, 0),
        "def",
        TokenKind::Keyword,
        false,
        [0, 0, 3, 12, 0],
    ),
    e(
        (4, 12),
        (0, 4),
        "temporal",
        TokenKind::Keyword,
        false,
        [0, 4, 8, 12, 0],
    ),
    e(
        (13, 19),
        (0, 13),
        "recent",
        TokenKind::Macro,
        true,
        [0, 9, 6, 11, 1],
    ),
    e(
        (19, 20),
        (0, 19),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (20, 27),
        (0, 20),
        "?window",
        TokenKind::Parameter,
        true,
        [0, 1, 7, 4, 1],
    ),
    e(
        (27, 28),
        (0, 27),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (29, 35),
        (0, 29),
        "?event",
        TokenKind::Parameter,
        true,
        [0, 2, 6, 4, 1],
    ),
    e(
        (35, 36),
        (0, 35),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (37, 38),
        (0, 37),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (39, 47),
        (0, 39),
        "formerly",
        TokenKind::Keyword,
        false,
        [0, 2, 8, 12, 0],
    ),
    e(
        (48, 54),
        (0, 48),
        "within",
        TokenKind::Keyword,
        false,
        [0, 9, 6, 12, 0],
    ),
    e(
        (55, 62),
        (0, 55),
        "?window",
        TokenKind::Parameter,
        false,
        [0, 7, 7, 4, 0],
    ),
    e(
        (63, 69),
        (0, 63),
        "?event",
        TokenKind::Parameter,
        false,
        [0, 8, 6, 4, 0],
    ),
    e(
        (70, 71),
        (0, 70),
        "}",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (71, 72),
        (0, 71),
        ";",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (73, 79),
        (1, 0),
        "permit",
        TokenKind::Keyword,
        false,
        [1, 0, 6, 12, 0],
    ),
    e(
        (79, 80),
        (1, 6),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (80, 89),
        (1, 7),
        "principal",
        TokenKind::Variable,
        false,
        [0, 1, 9, 5, 0],
    ),
    e(
        (89, 90),
        (1, 16),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (91, 97),
        (1, 18),
        "action",
        TokenKind::Variable,
        false,
        [0, 2, 6, 5, 0],
    ),
    e(
        (97, 98),
        (1, 24),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (99, 107),
        (1, 26),
        "resource",
        TokenKind::Variable,
        false,
        [0, 2, 8, 5, 0],
    ),
    e(
        (107, 108),
        (1, 34),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (109, 113),
        (1, 36),
        "when",
        TokenKind::Keyword,
        false,
        [0, 2, 4, 12, 0],
    ),
    e(
        (114, 122),
        (1, 41),
        "temporal",
        TokenKind::Keyword,
        false,
        [0, 5, 8, 12, 0],
    ),
    e(
        (123, 124),
        (1, 50),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (127, 133),
        (2, 2),
        "recent",
        TokenKind::Macro,
        false,
        [1, 2, 6, 11, 0],
    ),
    e(
        (133, 134),
        (2, 8),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (134, 135),
        (2, 9),
        "1",
        TokenKind::Number,
        false,
        [0, 1, 1, 16, 0],
    ),
    e(
        (135, 136),
        (2, 10),
        "h",
        TokenKind::Number,
        false,
        [0, 1, 1, 16, 0],
    ),
    e(
        (136, 137),
        (2, 11),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (138, 142),
        (2, 13),
        "Acme",
        TokenKind::Namespace,
        false,
        [0, 2, 4, 0, 0],
    ),
    e(
        (142, 144),
        (2, 17),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 4, 2, 17, 0],
    ),
    e(
        (144, 150),
        (2, 19),
        "Action",
        TokenKind::Type,
        false,
        [0, 2, 6, 1, 0],
    ),
    e(
        (150, 152),
        (2, 25),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 6, 2, 17, 0],
    ),
    e(
        (152, 158),
        (2, 27),
        "\"Read\"",
        TokenKind::String,
        false,
        [0, 2, 6, 15, 0],
    ),
    e(
        (158, 160),
        (2, 33),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 6, 2, 17, 0],
    ),
    e(
        (160, 167),
        (2, 35),
        "request",
        TokenKind::Event,
        false,
        [0, 2, 7, 8, 0],
    ),
    e(
        (167, 168),
        (2, 42),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (168, 169),
        (2, 43),
        "}",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (169, 170),
        (2, 44),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
    e(
        (171, 172),
        (3, 0),
        "}",
        TokenKind::Punctuation,
        false,
        [1, 0, 1, 17, 0],
    ),
    e(
        (172, 173),
        (3, 1),
        ";",
        TokenKind::Punctuation,
        false,
        [0, 1, 1, 17, 0],
    ),
];

const INCOMPLETE_EXPECTED: &[Expected] = &[
    e(
        (0, 6),
        (0, 0),
        "permit",
        TokenKind::Keyword,
        false,
        [0, 0, 6, 12, 0],
    ),
    e(
        (6, 7),
        (0, 6),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (7, 16),
        (0, 7),
        "principal",
        TokenKind::Keyword,
        false,
        [0, 1, 9, 12, 0],
    ),
    e(
        (16, 17),
        (0, 16),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (18, 24),
        (0, 18),
        "action",
        TokenKind::Keyword,
        false,
        [0, 2, 6, 12, 0],
    ),
    e(
        (25, 27),
        (0, 25),
        "==",
        TokenKind::Operator,
        false,
        [0, 7, 2, 17, 0],
    ),
    e(
        (28, 32),
        (0, 28),
        "Acme",
        TokenKind::Namespace,
        false,
        [0, 3, 4, 0, 0],
    ),
    e(
        (32, 34),
        (0, 32),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 4, 2, 17, 0],
    ),
    e(
        (34, 40),
        (0, 34),
        "Action",
        TokenKind::Type,
        false,
        [0, 2, 6, 1, 0],
    ),
    e(
        (40, 42),
        (0, 40),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 6, 2, 17, 0],
    ),
    e(
        (42, 48),
        (0, 42),
        "\"Read\"",
        TokenKind::String,
        false,
        [0, 2, 6, 15, 0],
    ),
    e(
        (48, 49),
        (0, 48),
        ",",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (50, 58),
        (0, 50),
        "resource",
        TokenKind::Keyword,
        false,
        [0, 2, 8, 12, 0],
    ),
    e(
        (58, 59),
        (0, 58),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (60, 64),
        (1, 0),
        "when",
        TokenKind::Keyword,
        false,
        [1, 0, 4, 12, 0],
    ),
    e(
        (65, 73),
        (1, 5),
        "temporal",
        TokenKind::Keyword,
        false,
        [0, 5, 8, 12, 0],
    ),
    e(
        (74, 75),
        (1, 14),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 9, 1, 17, 0],
    ),
    e(
        (76, 84),
        (1, 16),
        "formerly",
        TokenKind::Keyword,
        false,
        [0, 2, 8, 12, 0],
    ),
    e(
        (85, 91),
        (1, 25),
        "within",
        TokenKind::Keyword,
        false,
        [0, 9, 6, 12, 0],
    ),
    e(
        (92, 94),
        (1, 32),
        "1h",
        TokenKind::Number,
        false,
        [0, 7, 2, 16, 0],
    ),
    e(
        (95, 99),
        (1, 35),
        "Acme",
        TokenKind::Namespace,
        false,
        [0, 3, 4, 0, 0],
    ),
    e(
        (99, 101),
        (1, 39),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 4, 2, 17, 0],
    ),
    e(
        (101, 107),
        (1, 41),
        "Action",
        TokenKind::Type,
        false,
        [0, 2, 6, 1, 0],
    ),
    e(
        (107, 109),
        (1, 47),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 6, 2, 17, 0],
    ),
    e(
        (109, 115),
        (1, 49),
        "\"Read\"",
        TokenKind::String,
        false,
        [0, 2, 6, 15, 0],
    ),
    e(
        (115, 117),
        (1, 55),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 6, 2, 17, 0],
    ),
    e(
        (117, 125),
        (1, 57),
        "response",
        TokenKind::Event,
        false,
        [0, 2, 8, 8, 0],
    ),
    e(
        (125, 126),
        (1, 65),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 8, 1, 17, 0],
    ),
    e(
        (135, 136),
        (2, 8),
        ".",
        TokenKind::Punctuation,
        false,
        [1, 8, 1, 17, 0],
    ),
    e(
        (141, 142),
        (2, 14),
        ":",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
    e(
        (143, 150),
        (2, 16),
        "context",
        TokenKind::Keyword,
        false,
        [0, 2, 7, 12, 0],
    ),
    e(
        (150, 151),
        (2, 23),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (156, 157),
        (2, 29),
        ".",
        TokenKind::Punctuation,
        false,
        [0, 6, 1, 17, 0],
    ),
];

const INCOMPLETE_STRUCTURE_EXPECTED: &[Expected] = &[
    e(
        (0, 7),
        (0, 0),
        "// 🚀",
        TokenKind::Comment,
        false,
        [0, 0, 5, 14, 0],
    ),
    e(
        (9, 10),
        (1, 0),
        "@",
        TokenKind::Punctuation,
        false,
        [1, 0, 1, 17, 0],
    ),
    e(
        (10, 12),
        (1, 1),
        "id",
        TokenKind::Decorator,
        false,
        [0, 1, 2, 18, 0],
    ),
    e(
        (12, 13),
        (1, 3),
        "(",
        TokenKind::Punctuation,
        false,
        [0, 2, 1, 17, 0],
    ),
    e(
        (13, 25),
        (1, 4),
        "\"draft-🚀\"",
        TokenKind::String,
        false,
        [0, 1, 10, 15, 0],
    ),
    e(
        (25, 26),
        (1, 14),
        ")",
        TokenKind::Punctuation,
        false,
        [0, 10, 1, 17, 0],
    ),
    e(
        (28, 32),
        (2, 0),
        "Acme",
        TokenKind::Namespace,
        false,
        [1, 0, 4, 0, 0],
    ),
    e(
        (32, 34),
        (2, 4),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 4, 2, 17, 0],
    ),
    e(
        (34, 40),
        (2, 6),
        "Action",
        TokenKind::Type,
        false,
        [0, 2, 6, 1, 0],
    ),
    e(
        (40, 42),
        (2, 12),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 6, 2, 17, 0],
    ),
    e(
        (42, 55),
        (2, 14),
        "\"net:request\"",
        TokenKind::String,
        false,
        [0, 2, 13, 15, 0],
    ),
    e(
        (55, 57),
        (2, 27),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 13, 2, 17, 0],
    ),
    e(
        (57, 64),
        (2, 29),
        "attempt",
        TokenKind::Event,
        false,
        [0, 2, 7, 8, 0],
    ),
    e(
        (64, 65),
        (2, 36),
        "{",
        TokenKind::Punctuation,
        false,
        [0, 7, 1, 17, 0],
    ),
    e(
        (76, 83),
        (2, 48),
        "\"plain\"",
        TokenKind::String,
        false,
        [0, 12, 7, 15, 0],
    ),
    e(
        (83, 85),
        (2, 55),
        "::",
        TokenKind::Punctuation,
        false,
        [0, 7, 2, 17, 0],
    ),
];

fn position(source: &str, offset: usize) -> (u32, u32) {
    let prefix = &source[..offset];
    let line = u32::try_from(prefix.bytes().filter(|byte| *byte == b'\n').count()).unwrap();
    let line_start = prefix.rfind('\n').map_or(0, |index| index + 1);
    let character = u32::try_from(source[line_start..offset].encode_utf16().count()).unwrap();
    (line, character)
}

fn modifier(expected: &Expected) -> Option<TokenModifier> {
    expected.declaration.then_some(TokenModifier::Declaration)
}

fn encoded_analysis(source: &str) -> Vec<((usize, usize), [u32; 5])> {
    let tokens = analyze(source).expect("source should analyze");
    let mut previous_line = 0;
    let mut previous_start = 0;
    tokens
        .into_iter()
        .map(|token| {
            let (line, start) = position(source, token.span.start());
            let (end_line, end) = position(source, token.span.end());
            assert_eq!(end_line, line, "test source tokens must be line-local");
            let delta_line = line - previous_line;
            let delta_start = if delta_line == 0 {
                start - previous_start
            } else {
                start
            };
            let encoded = [
                delta_line,
                delta_start,
                end - start,
                token.kind.legend_index(),
                token.modifier.map_or(0, TokenModifier::legend_bit),
            ];
            previous_line = line;
            previous_start = start;
            ((token.span.start(), token.span.end()), encoded)
        })
        .collect()
}

fn assert_exact_interval_projection(
    source: &str,
    expected_numbers: &[(usize, usize, &str)],
    expected_comment: Option<CommentExpected<'_>>,
) {
    let structural =
        frontend_semantic::classify(source).expect("interval source should strictly parse");
    assert!(
        structural
            .iter()
            .filter(|span| span.kind == TokenKind::Number)
            .all(|span| span.modifier.is_none())
    );
    let structural_numbers = structural
        .iter()
        .filter(|span| span.kind == TokenKind::Number)
        .map(|span| (span.start, span.end, &source[span.start..span.end]))
        .collect::<Vec<_>>();
    assert_eq!(structural_numbers, expected_numbers);

    let merged = analyze(source).expect("interval source should merge");
    assert!(
        merged
            .iter()
            .filter(|token| token.kind == TokenKind::Number)
            .all(|token| token.modifier.is_none())
    );
    let merged_numbers = merged
        .iter()
        .filter(|token| token.kind == TokenKind::Number)
        .map(|token| {
            (
                token.span.start(),
                token.span.end(),
                &source[token.span.start()..token.span.end()],
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(merged_numbers, expected_numbers);

    if let Some(expected) = expected_comment {
        assert_eq!(position(source, expected.byte_start), expected.position);
        assert_eq!(
            &source[expected.byte_start..expected.byte_end],
            expected.slice
        );
        assert!(merged.iter().any(|token| {
            token.span.start() == expected.byte_start
                && token.span.end() == expected.byte_end
                && token.kind == TokenKind::Comment
                && token.modifier.is_none()
        }));
        assert!(encoded_analysis(source).iter().any(|(range, delta)| {
            *range == (expected.byte_start, expected.byte_end) && *delta == expected.delta
        }));
    }
}

fn assert_golden(source: &str, expected: &[Expected], strict: bool) {
    let actual = analyze(source).expect("golden source should analyze");
    assert_eq!(analyze(source), Ok(actual.clone()), "analysis must repeat");
    assert_eq!(actual.len(), expected.len());

    let mut encoded = Vec::with_capacity(actual.len() * 5);
    let mut previous_line = 0;
    let mut previous_start = 0;
    for (index, (actual, expected)) in actual.iter().zip(expected).enumerate() {
        assert_eq!(actual.span.start(), expected.byte_start, "token {index}");
        assert_eq!(actual.span.end(), expected.byte_end, "token {index}");
        assert_eq!(
            &source[actual.span.start()..actual.span.end()],
            expected.slice,
            "token {index}"
        );
        assert_eq!(actual.kind, expected.kind, "token {index}");
        assert_eq!(actual.modifier, modifier(expected), "token {index}");
        assert_eq!(
            position(source, actual.span.start()),
            (expected.line, expected.character)
        );
        let (_, end) = position(source, actual.span.end());
        assert_eq!(end - expected.character, expected.delta[2], "token {index}");
        assert_eq!(
            actual.kind.legend_index(),
            expected.delta[3],
            "token {index}"
        );
        assert_eq!(
            actual.modifier.map_or(0, TokenModifier::legend_bit),
            expected.delta[4],
            "token {index}"
        );
        let delta_line = expected.line - previous_line;
        let delta_start = if delta_line == 0 {
            expected.character - previous_start
        } else {
            expected.character
        };
        let actual_delta = [
            delta_line,
            delta_start,
            end - expected.character,
            actual.kind.legend_index(),
            actual.modifier.map_or(0, TokenModifier::legend_bit),
        ];
        assert_eq!(actual_delta, expected.delta, "token {index}");
        encoded.extend_from_slice(&actual_delta);
        previous_line = expected.line;
        previous_start = expected.character;
    }
    assert_eq!(
        encoded,
        expected
            .iter()
            .flat_map(|token| token.delta)
            .collect::<Vec<_>>()
    );

    if strict {
        let structural =
            frontend_semantic::classify(source).expect("fixture should strictly parse");
        for span in structural {
            let expected = expected
                .iter()
                .find(|expected| {
                    expected.byte_start == span.start
                        && expected.byte_end == span.end
                        && expected.kind == span.kind
                        && modifier(expected) == span.modifier
                })
                .unwrap_or_else(|| panic!("unexpected parser span: {span:?}"));
            assert_eq!(&source[span.start..span.end], expected.slice);
        }
    } else {
        assert!(frontend_semantic::classify(source).is_none());
        assert_eq!(actual, analyze_lexical(source).unwrap());
    }
}

fn assert_upstream_corpus_fixture(source: &str, expected: &[CorpusExpected]) {
    let lexical = analyze_lexical(source).expect("copied fixture lexical scan should succeed");
    let analyzed = analyze(source).expect("copied fixture analysis should succeed");
    let structural =
        frontend_semantic::classify(source).expect("copied fixture must strictly parse");

    assert_eq!(analyze(source), Ok(analyzed.clone()));
    assert_eq!(
        frontend_semantic::classify(source),
        Some(structural.clone())
    );
    assert_ne!(
        analyzed, lexical,
        "copied valid fixture silently fell back to M2 lexical tokens"
    );

    for expected in expected {
        assert_eq!(
            source.get(expected.byte_start..expected.byte_end),
            Some(expected.slice)
        );
        assert_eq!(
            position(source, expected.byte_start),
            (expected.line, expected.character)
        );
        let (end_line, end_character) = position(source, expected.byte_end);
        assert_eq!(end_line, expected.line);
        assert_eq!(end_character - expected.character, expected.utf16_length);
        let modifier = expected.declaration.then_some(TokenModifier::Declaration);
        assert!(
            structural.iter().any(|span| {
                span.start == expected.byte_start
                    && span.end == expected.byte_end
                    && span.kind == expected.kind
                    && span.modifier == modifier
            }),
            "missing exact parser span {expected:?}: {structural:?}"
        );
        assert!(
            analyzed.iter().any(|token| {
                token.span.start() == expected.byte_start
                    && token.span.end() == expected.byte_end
                    && token.kind == expected.kind
                    && token.modifier == modifier
            }),
            "missing exact merged token {expected:?}: {analyzed:?}"
        );
    }

    for span in structural {
        assert_eq!(
            source.get(span.start..span.end),
            Some(&source[span.start..span.end])
        );
    }
}

#[test]
fn exact_cedar_crlf_unicode_golden() {
    let cedar = cedar();
    assert!(cedar.as_bytes().windows(2).any(|bytes| bytes == b"\r\n"));
    assert_golden(&cedar, CEDAR_EXPECTED, true);
}

#[test]
fn exact_mixed_temporal_golden() {
    assert_golden(MIXED, MIXED_EXPECTED, true);
}

#[test]
fn exact_standalone_both_dialect_macro_library_golden() {
    assert_golden(MACROS, MACROS_EXPECTED, true);
}

#[test]
fn exact_nested_qualified_function_and_unqualified_macro_call_golden() {
    assert_golden(NESTED_CALLS, NESTED_CALLS_EXPECTED, true);
}

#[test]
fn exact_temporal_interval_macro_argument_golden() {
    assert_golden(INTERVAL_CALL, INTERVAL_CALL_EXPECTED, true);
}

#[test]
fn comment_separated_temporal_window_preserves_exact_ranges_and_comment() {
    assert_exact_interval_projection(
        COMMENT_WINDOW,
        &[(68, 69, "1"), (84, 85, "h")],
        Some(CommentExpected {
            byte_start: 70,
            byte_end: 83,
            slice: "// window gap",
            position: (1, 18),
            delta: [0, 2, 13, 14, 0],
        }),
    );

    let encoded = encoded_analysis(COMMENT_WINDOW);
    assert!(encoded.contains(&((68, 69), [0, 7, 1, 16, 0])));
    assert!(encoded.contains(&((84, 85), [1, 0, 1, 16, 0])));
}

#[test]
fn comment_separated_temporal_macro_argument_preserves_exact_ranges_and_comment() {
    assert_exact_interval_projection(
        COMMENT_ARGUMENT,
        &[(104, 105, "1"), (122, 123, "h")],
        Some(CommentExpected {
            byte_start: 106,
            byte_end: 121,
            slice: "// argument gap",
            position: (2, 4),
            delta: [0, 2, 15, 14, 0],
        }),
    );

    let structural =
        frontend_semantic::classify(COMMENT_ARGUMENT).expect("macro argument should parse");
    assert!(structural.iter().any(|span| {
        span.start == 41
            && span.end == 43
            && span.kind == TokenKind::Parameter
            && span.modifier.is_none()
            && &COMMENT_ARGUMENT[span.start..span.end] == "?w"
    }));
    let encoded = encoded_analysis(COMMENT_ARGUMENT);
    assert!(encoded.contains(&((104, 105), [0, 1, 1, 16, 0])));
    assert!(encoded.contains(&((122, 123), [1, 0, 1, 16, 0])));
}

#[test]
fn interval_number_spans_are_exact_for_adjacent_spaced_and_commented_forms() {
    assert_exact_interval_projection(ADJACENT_INTERVAL, &[(68, 69, "2"), (69, 70, "h")], None);
    assert_exact_interval_projection(SPACED_INTERVAL, &[(68, 69, "3"), (70, 71, "h")], None);

    for source in [
        COMMENT_WINDOW,
        COMMENT_ARGUMENT,
        ADJACENT_INTERVAL,
        SPACED_INTERVAL,
    ] {
        let structural =
            frontend_semantic::classify(source).expect("interval form should strictly parse");
        for span in structural
            .iter()
            .filter(|span| span.kind == TokenKind::Number)
        {
            let slice = &source[span.start..span.end];
            assert!(
                slice.bytes().all(|byte| byte.is_ascii_digit())
                    || matches!(slice, "s" | "m" | "h" | "d"),
                "Number span contains non-interval trivia: {span:?} => {slice:?}"
            );
        }
    }
}

#[test]
fn exact_has_if_property_and_conditional_keyword_golden() {
    let expected = [
        e(
            (0, 6),
            (0, 0),
            "permit",
            TokenKind::Keyword,
            false,
            [0, 0, 6, 12, 0],
        ),
        e(
            (6, 7),
            (0, 6),
            "(",
            TokenKind::Punctuation,
            false,
            [0, 6, 1, 17, 0],
        ),
        e(
            (7, 16),
            (0, 7),
            "principal",
            TokenKind::Variable,
            false,
            [0, 1, 9, 5, 0],
        ),
        e(
            (16, 17),
            (0, 16),
            ",",
            TokenKind::Punctuation,
            false,
            [0, 9, 1, 17, 0],
        ),
        e(
            (18, 24),
            (0, 18),
            "action",
            TokenKind::Variable,
            false,
            [0, 2, 6, 5, 0],
        ),
        e(
            (24, 25),
            (0, 24),
            ",",
            TokenKind::Punctuation,
            false,
            [0, 6, 1, 17, 0],
        ),
        e(
            (26, 34),
            (0, 26),
            "resource",
            TokenKind::Variable,
            false,
            [0, 2, 8, 5, 0],
        ),
        e(
            (34, 35),
            (0, 34),
            ")",
            TokenKind::Punctuation,
            false,
            [0, 8, 1, 17, 0],
        ),
        e(
            (36, 40),
            (0, 36),
            "when",
            TokenKind::Keyword,
            false,
            [0, 2, 4, 12, 0],
        ),
        e(
            (41, 42),
            (0, 41),
            "{",
            TokenKind::Punctuation,
            false,
            [0, 5, 1, 17, 0],
        ),
        e(
            (43, 50),
            (0, 43),
            "context",
            TokenKind::Variable,
            false,
            [0, 2, 7, 5, 0],
        ),
        e(
            (51, 54),
            (0, 51),
            "has",
            TokenKind::Keyword,
            false,
            [0, 8, 3, 12, 0],
        ),
        e(
            (55, 57),
            (0, 55),
            "if",
            TokenKind::Property,
            false,
            [0, 4, 2, 6, 0],
        ),
        e(
            (58, 59),
            (0, 58),
            "}",
            TokenKind::Punctuation,
            false,
            [0, 3, 1, 17, 0],
        ),
        e(
            (60, 64),
            (0, 60),
            "when",
            TokenKind::Keyword,
            false,
            [0, 2, 4, 12, 0],
        ),
        e(
            (65, 66),
            (0, 65),
            "{",
            TokenKind::Punctuation,
            false,
            [0, 5, 1, 17, 0],
        ),
        e(
            (67, 69),
            (0, 67),
            "if",
            TokenKind::Keyword,
            false,
            [0, 2, 2, 12, 0],
        ),
        e(
            (70, 74),
            (0, 70),
            "true",
            TokenKind::Keyword,
            false,
            [0, 3, 4, 12, 0],
        ),
        e(
            (75, 79),
            (0, 75),
            "then",
            TokenKind::Keyword,
            false,
            [0, 5, 4, 12, 0],
        ),
        e(
            (80, 84),
            (0, 80),
            "true",
            TokenKind::Keyword,
            false,
            [0, 5, 4, 12, 0],
        ),
        e(
            (85, 89),
            (0, 85),
            "else",
            TokenKind::Keyword,
            false,
            [0, 5, 4, 12, 0],
        ),
        e(
            (90, 95),
            (0, 90),
            "false",
            TokenKind::Keyword,
            false,
            [0, 5, 5, 12, 0],
        ),
        e(
            (96, 97),
            (0, 96),
            "}",
            TokenKind::Punctuation,
            false,
            [0, 6, 1, 17, 0],
        ),
        e(
            (97, 98),
            (0, 97),
            ";",
            TokenKind::Punctuation,
            false,
            [0, 1, 1, 17, 0],
        ),
    ];

    assert_golden(HAS_IF, &expected, true);
}

#[test]
fn exact_incomplete_edit_golden_is_complete_lexical_fallback() {
    assert_golden(INCOMPLETE, INCOMPLETE_EXPECTED, false);
}

#[test]
fn parser_backed_annotations_actions_and_arbitrary_events_have_exact_spans() {
    assert_upstream_corpus_fixture(
        ACTION_STRUCTURE,
        &[
            corpus_e((1, 3), (0, 1), 2, "id", TokenKind::Decorator, false),
            corpus_e(
                (4, 16),
                (0, 4),
                12,
                "\"namespaced\"",
                TokenKind::String,
                false,
            ),
            corpus_e((46, 50), (1, 28), 4, "Acme", TokenKind::Namespace, false),
            corpus_e((52, 58), (1, 34), 6, "Action", TokenKind::Type, false),
            corpus_e(
                (60, 73),
                (1, 42),
                13,
                "\"net:request\"",
                TokenKind::String,
                false,
            ),
            corpus_e((120, 124), (2, 35), 4, "Acme", TokenKind::Namespace, false),
            corpus_e((126, 132), (2, 41), 6, "Action", TokenKind::Type, false),
            corpus_e(
                (134, 147),
                (2, 49),
                13,
                "\"net:request\"",
                TokenKind::String,
                false,
            ),
            corpus_e((149, 157), (2, 64), 8, "response", TokenKind::Event, false),
            corpus_e((164, 166), (3, 1), 2, "id", TokenKind::Decorator, false),
            corpus_e((167, 173), (3, 4), 6, "\"root\"", TokenKind::String, false),
            corpus_e((203, 209), (4, 28), 6, "Action", TokenKind::Type, false),
            corpus_e(
                (211, 220),
                (4, 36),
                9,
                "\"root:id\"",
                TokenKind::String,
                false,
            ),
            corpus_e((267, 273), (5, 35), 6, "Action", TokenKind::Type, false),
            corpus_e(
                (275, 284),
                (5, 43),
                9,
                "\"root:id\"",
                TokenKind::String,
                false,
            ),
            corpus_e((286, 293), (5, 54), 7, "attempt", TokenKind::Event, false),
        ],
    );
}

#[test]
fn incomplete_crlf_unicode_structure_has_exact_fallback_deltas() {
    assert!(
        INCOMPLETE_STRUCTURE
            .as_bytes()
            .windows(2)
            .any(|bytes| bytes == b"\r\n")
    );
    assert_golden(INCOMPLETE_STRUCTURE, INCOMPLETE_STRUCTURE_EXPECTED, false);
    assert!(!analyze(INCOMPLETE_STRUCTURE).unwrap().iter().any(|token| {
        matches!(
            &INCOMPLETE_STRUCTURE[token.span.start()..token.span.end()],
            "unrelated" | "suffix"
        )
    }));
}

#[test]
fn historical_cedar_corpus_fixture_is_parser_backed() {
    assert_upstream_corpus_fixture(
        UPSTREAM_CEDAR,
        &[
            corpus_e(
                (247, 256),
                (6, 4),
                9,
                "principal",
                TokenKind::Variable,
                false,
            ),
            corpus_e((272, 277), (7, 14), 5, "Drupe", TokenKind::Namespace, false),
            corpus_e((279, 285), (7, 21), 6, "Action", TokenKind::Type, false),
            corpus_e(
                (307, 315),
                (8, 4),
                8,
                "resource",
                TokenKind::Variable,
                false,
            ),
        ],
    );
}

#[test]
fn historical_macro_corpus_fixture_is_parser_backed() {
    assert_upstream_corpus_fixture(
        UPSTREAM_MACRO,
        &[
            corpus_e(
                (428, 445),
                (9, 10),
                17,
                "is_priority_stock",
                TokenKind::Macro,
                true,
            ),
            corpus_e((446, 448), (9, 28), 2, "?s", TokenKind::Parameter, true),
            corpus_e((456, 458), (10, 4), 2, "?s", TokenKind::Parameter, false),
            corpus_e(
                (525, 530),
                (15, 14),
                5,
                "Drupe",
                TokenKind::Namespace,
                false,
            ),
            corpus_e(
                (580, 597),
                (19, 4),
                17,
                "is_priority_stock",
                TokenKind::Macro,
                false,
            ),
            corpus_e(
                (598, 605),
                (19, 22),
                7,
                "context",
                TokenKind::Variable,
                false,
            ),
            corpus_e((606, 611), (19, 30), 5, "input", TokenKind::Property, false),
            corpus_e((612, 617), (19, 36), 5, "stock", TokenKind::Property, false),
        ],
    );
}

#[test]
fn historical_temporal_corpus_fixture_is_parser_backed() {
    assert_upstream_corpus_fixture(
        UPSTREAM_TEMPORAL,
        &[
            corpus_e((13, 22), (1, 4), 9, "principal", TokenKind::Variable, false),
            corpus_e((56, 64), (5, 5), 8, "temporal", TokenKind::Keyword, false),
            corpus_e((71, 79), (6, 4), 8, "formerly", TokenKind::Keyword, false),
            corpus_e((87, 88), (6, 20), 1, "1", TokenKind::Number, false),
            corpus_e((88, 89), (6, 21), 1, "h", TokenKind::Number, false),
            corpus_e((90, 95), (6, 23), 5, "Drupe", TokenKind::Namespace, false),
            corpus_e((97, 103), (6, 30), 6, "Action", TokenKind::Type, false),
            corpus_e((114, 121), (6, 47), 7, "request", TokenKind::Event, false),
            corpus_e((123, 128), (6, 56), 5, "input", TokenKind::Property, false),
            corpus_e((129, 133), (6, 62), 4, "user", TokenKind::Property, false),
        ],
    );
}

#[test]
fn macro_and_operational_failures_are_complete_lexical_fallback() {
    let invalid_macro = "def cedar bad(?x) { missing(?x) }; permit(principal, action, resource);";
    assert!(frontend_semantic::classify(invalid_macro).is_none());
    assert_eq!(analyze(invalid_macro), analyze_lexical(invalid_macro));

    let nested = format!(
        "permit(principal, action, resource) when {{ {}true{} }};",
        "(".repeat(33),
        ")".repeat(33)
    );
    assert!(frontend_semantic::classify(&nested).is_none());
    assert_eq!(analyze(&nested), analyze_lexical(&nested));
}

#[test]
fn deterministic_generated_valid_forms_and_all_utf8_truncations_are_bounded() {
    for index in 0..12 {
        let source = format!(
            "// generated {index} 🚀\n\
             @id(\"g{index}\") permit(principal, action == Ns{index}::Action::\"Read{index}\", resource) \
             when {{ context.input.value == {index} && resource.owner == principal }};"
        );
        assert!(
            frontend_semantic::classify(&source).is_some(),
            "generated form {index} must strictly parse"
        );

        for end in (0..=source.len()).filter(|end| source.is_char_boundary(*end)) {
            let prefix = &source[..end];
            let first = analyze(prefix).expect("truncation should remain analyzable");
            let second = analyze(prefix).expect("truncation should remain deterministic");
            assert_eq!(first, second, "generated form {index}, truncation {end}");
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
            if frontend_semantic::classify(prefix).is_none() {
                assert_eq!(
                    first,
                    analyze_lexical(prefix).unwrap(),
                    "failed strict parse lost fallback at form {index}, truncation {end}"
                );
            }
        }
    }
}
