// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#![cfg(unix)]

use std::str::FromStr;

use dogwood_lsp::analysis::{Token, analyze, analyze_event_schema};
use dogwood_lsp::diagnostics::{
    BundleDocuments, SourceDocument, project_event_schema_outcome, project_frontend_outcome,
};
use dogwood_lsp::frontend::{BundleInput, FrontendOutcome, parse_event_schema, validate_bundle};
use dogwood_lsp::legend::{TOKEN_MODIFIERS, TOKEN_TYPES};
use lsp_types::{Position, Range, Uri};

const SEED: u64 = 0xC623_7C88_0000_0008;
const ACTION_SCHEMA: &str = include_str!("fixtures/dogwood/m3/default-valid/schema.cedarschema");
const FRAGMENTS: [&str; 24] = [
    "permit",
    "forbid",
    "principal",
    "action",
    "resource",
    "when",
    "temporal",
    "formerly",
    "within",
    "1h",
    "event",
    "decision",
    "context",
    "true",
    "false",
    "\"text\"",
    "\"unterminated",
    "// comment",
    "\u{1f600}",
    "\u{00e9}",
    "{",
    "}",
    "\r\n",
    "\n",
];

#[test]
fn seeded_parser_token_and_diagnostic_properties_are_deterministic_and_bounded() {
    let policy_uri = uri("file:///property/policy.dw");
    let action_uri = uri("file:///property/actions.cedarschema");
    let event_uri = uri("file:///property/events.dwschema");
    let mut random = Lcg::new(SEED);

    for case_index in 0..384 {
        let source = generated_source(&mut random);
        let context = format!("seed={SEED:#x} case={case_index} source={source:?}");

        let first_policy_tokens =
            analyze(&source).unwrap_or_else(|error| panic!("{context}: policy tokens: {error}"));
        let second_policy_tokens = analyze(&source)
            .unwrap_or_else(|error| panic!("{context}: policy retokenize: {error}"));
        assert_eq!(
            first_policy_tokens, second_policy_tokens,
            "{context}: policy token output changed"
        );
        assert_token_invariants(&source, &first_policy_tokens, &context);

        let first_schema_tokens = analyze_event_schema(&source)
            .unwrap_or_else(|error| panic!("{context}: schema tokens: {error}"));
        let second_schema_tokens = analyze_event_schema(&source)
            .unwrap_or_else(|error| panic!("{context}: schema retokenize: {error}"));
        assert_eq!(
            first_schema_tokens, second_schema_tokens,
            "{context}: schema token output changed"
        );
        assert_token_invariants(&source, &first_schema_tokens, &context);

        let input = BundleInput {
            policy: &source,
            action_schema: ACTION_SCHEMA,
            event_schema: None,
            providers: None,
            macros: None,
        };
        let first_outcome = validate_bundle(&input);
        let second_outcome = validate_bundle(&input);
        assert_eq!(
            first_outcome, second_outcome,
            "{context}: policy diagnostics changed"
        );
        let documents = BundleDocuments {
            policy: SourceDocument {
                uri: &policy_uri,
                text: &source,
            },
            action_schema: SourceDocument {
                uri: &action_uri,
                text: ACTION_SCHEMA,
            },
            event_schema: None,
            providers: None,
            macros: None,
        };
        let first_publication = project_frontend_outcome(41, documents, first_outcome);
        let second_publication = project_frontend_outcome(41, documents, second_outcome);
        assert_eq!(
            first_publication, second_publication,
            "{context}: projected policy diagnostics changed"
        );
        assert_eq!(first_publication.version, Some(41));
        for diagnostic in &first_publication.diagnostics {
            assert_range(&source, diagnostic.range, &context);
            for related in diagnostic.related_information.iter().flatten() {
                let related_source = if related.location.uri == policy_uri {
                    source.as_str()
                } else {
                    assert_eq!(related.location.uri, action_uri, "{context}");
                    ACTION_SCHEMA
                };
                assert_range(related_source, related.location.range, &context);
            }
        }

        let first_schema_outcome = parse_event_schema(&source);
        let second_schema_outcome = parse_event_schema(&source);
        assert_eq!(
            first_schema_outcome, second_schema_outcome,
            "{context}: standalone schema diagnostics changed"
        );
        let first_schema_publication = project_event_schema_outcome(
            73,
            SourceDocument {
                uri: &event_uri,
                text: &source,
            },
            first_schema_outcome.clone(),
        );
        let second_schema_publication = project_event_schema_outcome(
            73,
            SourceDocument {
                uri: &event_uri,
                text: &source,
            },
            second_schema_outcome,
        );
        assert_eq!(
            first_schema_publication, second_schema_publication,
            "{context}: projected schema diagnostics changed"
        );
        assert_eq!(first_schema_publication.version, Some(73));
        for diagnostic in &first_schema_publication.diagnostics {
            assert_range(&source, diagnostic.range, &context);
            for related in diagnostic.related_information.iter().flatten() {
                assert_eq!(related.location.uri, event_uri, "{context}");
                assert_range(&source, related.location.range, &context);
            }
        }

        assert_outcome_label_boundaries(&source, &first_schema_outcome, &context);
    }
}

fn generated_source(random: &mut Lcg) -> String {
    let fragment_count = 1 + (random.next() as usize % 32);
    let mut source = String::new();
    for index in 0..fragment_count {
        if index != 0 && !source.ends_with(['\r', '\n']) {
            source.push(if random.next().is_multiple_of(3) {
                '\t'
            } else {
                ' '
            });
        }
        source.push_str(FRAGMENTS[random.next() as usize % FRAGMENTS.len()]);
    }
    source
}

fn assert_token_invariants(source: &str, tokens: &[Token], context: &str) {
    for token in tokens {
        assert!(
            token.span.start() < token.span.end() && token.span.end() <= source.len(),
            "{context}: token bounds"
        );
        assert!(
            source.is_char_boundary(token.span.start())
                && source.is_char_boundary(token.span.end()),
            "{context}: token UTF-8 boundary"
        );
        assert!(
            (token.kind.legend_index() as usize) < TOKEN_TYPES.len(),
            "{context}: token legend"
        );
        if let Some(modifier) = token.modifier {
            assert!(
                (modifier.legend_index() as usize) < TOKEN_MODIFIERS.len(),
                "{context}: modifier legend"
            );
        }
    }
    for pair in tokens.windows(2) {
        assert!(
            pair[0].span.end() <= pair[1].span.start(),
            "{context}: overlapping tokens"
        );
    }
}

fn assert_outcome_label_boundaries<R>(source: &str, outcome: &FrontendOutcome<R>, context: &str)
where
    R: std::fmt::Debug,
{
    let FrontendOutcome::Fatal(fatal) = outcome else {
        return;
    };
    for finding in std::iter::once(fatal.diagnostic.as_ref()).chain(&fatal.related) {
        for label in &finding.labels {
            let end = label
                .start
                .checked_add(label.len)
                .unwrap_or_else(|| panic!("{context}: label overflow"));
            let synthetic_eof = label.start == source.len() && label.len == 1;
            assert!(
                source.is_char_boundary(label.start)
                    && (synthetic_eof || (end <= source.len() && source.is_char_boundary(end))),
                "{context}: invalid frontend label {label:?}"
            );
        }
    }
}

fn assert_range(source: &str, range: Range, context: &str) {
    let start = byte_offset(source, range.start)
        .unwrap_or_else(|| panic!("{context}: invalid range start {range:?}"));
    let end = byte_offset(source, range.end)
        .unwrap_or_else(|| panic!("{context}: invalid range end {range:?}"));
    assert!(start <= end, "{context}: reversed range {range:?}");
}

fn byte_offset(source: &str, position: Position) -> Option<usize> {
    let mut line_start = 0;
    for _ in 0..position.line {
        line_start += source[line_start..].find('\n')? + 1;
    }
    let remainder = &source[line_start..];
    let mut content_end = remainder.find('\n').unwrap_or(remainder.len());
    if content_end > 0 && remainder.as_bytes()[content_end - 1] == b'\r' {
        content_end -= 1;
    }
    let line = &remainder[..content_end];
    let mut utf16 = 0_u32;
    for (byte, scalar) in line.char_indices() {
        if utf16 == position.character {
            return Some(line_start + byte);
        }
        utf16 += scalar.len_utf16() as u32;
        if utf16 > position.character {
            return None;
        }
    }
    (utf16 == position.character).then_some(line_start + content_end)
}

fn uri(value: &str) -> Uri {
    Uri::from_str(value).expect("property URI should be valid")
}

struct Lcg(u64);

impl Lcg {
    const fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(2_862_933_555_777_941_757)
            .wrapping_add(3_037_000_493);
        self.0
    }
}
