//! Parser-backed, editor-neutral syntax spans for Dogwood source files.
//!
//! This module intentionally exposes semantic classifications rather than Pest
//! parser internals. Consumers such as language servers can map these spans to
//! their own protocol legend while the canonical Dogwood grammars and parse
//! trees remain private to this crate.

mod event_schema;
mod policy;

use dogwood_syntax::ParseOptions;

/// A source-level semantic classification produced by Dogwood's canonical
/// parser.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum SyntaxKind {
    Namespace,
    Type,
    TypeParameter,
    Parameter,
    Variable,
    Property,
    Event,
    Function,
    Method,
    Macro,
    Keyword,
    String,
    Number,
    Decorator,
}

/// Optional semantic information attached to a [`SyntaxSpan`].
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum SyntaxModifier {
    Declaration,
}

/// One nonempty UTF-8 byte range in the source.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SyntaxSpan {
    pub start: usize,
    pub end: usize,
    pub kind: SyntaxKind,
    pub modifier: Option<SyntaxModifier>,
}

impl SyntaxSpan {
    pub(crate) const fn new(
        start: usize,
        end: usize,
        kind: SyntaxKind,
        modifier: Option<SyntaxModifier>,
    ) -> Self {
        Self {
            start,
            end,
            kind,
            modifier,
        }
    }
}

/// Classify a complete Dogwood policy using the canonical policy and temporal
/// grammars.
///
/// Returns `None` when structural classification is unavailable. This is not a
/// validity diagnostic; callers should use the normal parse/validation API for
/// authoritative findings.
pub fn policy_spans(source: &str) -> Option<Vec<SyntaxSpan>> {
    policy_spans_with(source, &ParseOptions::default())
}

/// [`policy_spans`] under `options`: source nested deeper than
/// `options.max_depth` is not classified.
pub fn policy_spans_with(source: &str, options: &ParseOptions) -> Option<Vec<SyntaxSpan>> {
    let (parsed_source, base) = source
        .strip_prefix('\u{feff}')
        .map_or((source, 0), |stripped| (stripped, '\u{feff}'.len_utf8()));
    finish(
        source,
        policy::classify(parsed_source, base, options.max_depth)?,
    )
}

/// Classify a complete Dogwood event schema using the canonical event-schema
/// grammar.
///
/// Returns `None` when structural classification is unavailable. This is not a
/// validity diagnostic; callers should use [`crate::ServiceSchemaBuilder`] for
/// authoritative findings.
pub fn event_schema_spans(source: &str) -> Option<Vec<SyntaxSpan>> {
    event_schema_spans_with(source, &ParseOptions::default())
}

/// [`event_schema_spans`] under `options`: source nested deeper than
/// `options.max_depth` is not classified.
pub fn event_schema_spans_with(source: &str, options: &ParseOptions) -> Option<Vec<SyntaxSpan>> {
    let (parsed_source, base) = source
        .strip_prefix('\u{feff}')
        .map_or((source, 0), |stripped| (stripped, '\u{feff}'.len_utf8()));
    let spans = event_schema::classify(parsed_source, options.max_depth)?
        .into_iter()
        .map(|mut span| {
            span.start = span.start.checked_add(base)?;
            span.end = span.end.checked_add(base)?;
            Some(span)
        })
        .collect::<Option<Vec<_>>>()?;
    finish(source, spans)
}

fn finish(source: &str, mut spans: Vec<SyntaxSpan>) -> Option<Vec<SyntaxSpan>> {
    spans.sort_unstable();
    spans.dedup();

    if spans.iter().any(|span| {
        span.start >= span.end
            || span.end > source.len()
            || !source.is_char_boundary(span.start)
            || !source.is_char_boundary(span.end)
    }) {
        return None;
    }
    if spans.windows(2).any(|pair| pair[1].start < pair[0].end) {
        return None;
    }
    Some(spans)
}

#[cfg(test)]
mod tests {
    use super::{SyntaxKind, SyntaxModifier, event_schema_spans, policy_spans};

    fn policy_lexemes(source: &str) -> Vec<(&str, SyntaxKind, Option<SyntaxModifier>)> {
        policy_spans(source)
            .expect("policy syntax should classify")
            .into_iter()
            .map(|span| (&source[span.start..span.end], span.kind, span.modifier))
            .collect()
    }

    #[test]
    fn policy_spans_include_hidden_temporal_literals_without_grammar_copies() {
        let macro_source = r#"def temporal total(?value, ?event) {
    sum ?value for (?value: Long). where ?event
};"#;
        let macro_tokens = policy_lexemes(macro_source);
        for keyword in ["sum", "for", "where"] {
            assert!(macro_tokens.contains(&(keyword, SyntaxKind::Keyword, None)));
        }

        let policy_source = r#"permit(principal, action, resource) when temporal {
    exists ($t: Timepoint). (
        formerly within 1h Acme::Action::"Read"::request{}
        && previous within 2m Acme::Action::"Write"::response{}
        && tp($t)
        && context.input.amount == decimal("1.0")
    )
};"#;
        let policy_tokens = policy_lexemes(policy_source);
        for keyword in ["exists", "formerly", "within", "previous", "tp"] {
            assert!(policy_tokens.contains(&(keyword, SyntaxKind::Keyword, None)));
        }
        assert!(policy_tokens.contains(&("context", SyntaxKind::Variable, None)));
        assert!(policy_tokens.contains(&("decimal", SyntaxKind::Function, None)));
    }

    #[test]
    fn policy_spans_find_comment_separated_since_and_remain_nonoverlapping() {
        let source = r#"permit(principal, action, resource) when temporal {
    Acme::Action::"Read"::request{} // left
    since // operator
    within 1d Acme::Action::"Login"::request{}
};"#;
        let spans = policy_spans(source).expect("comment-separated since should classify");
        assert!(spans.iter().any(|span| {
            &source[span.start..span.end] == "since" && span.kind == SyntaxKind::Keyword
        }));
        assert!(spans.windows(2).all(|pair| pair[0].end <= pair[1].start));
    }

    #[test]
    fn event_schema_spans_classify_context_without_changing_the_grammar() {
        let source = r#"event <A>::request {
    pin session: String = context // gap
        .input.session,
}"#;
        let spans = event_schema_spans(source).expect("event schema should classify");
        let tokens = spans
            .iter()
            .map(|span| (&source[span.start..span.end], span.kind))
            .collect::<Vec<_>>();
        assert!(tokens.contains(&("context", SyntaxKind::Variable)));
        assert!(tokens.contains(&("input", SyntaxKind::Property)));
        assert!(tokens.contains(&("session", SyntaxKind::Property)));
        assert!(spans.windows(2).all(|pair| pair[0].end <= pair[1].start));
    }

    #[test]
    fn incomplete_sources_have_no_structural_spans() {
        assert!(policy_spans("permit(principal, action, resource").is_none());
        assert!(event_schema_spans("event <A>::request {").is_none());
    }

    #[test]
    fn leading_bom_preserves_source_offsets() {
        let policy = "\u{feff}permit(principal, action, resource);";
        let policy_spans = policy_spans(policy).expect("BOM-prefixed policy should classify");
        assert!(policy_spans.iter().all(|span| span.start >= 3));
        assert!(policy_spans.iter().any(|span| {
            &policy[span.start..span.end] == "permit" && span.kind == SyntaxKind::Keyword
        }));

        let event_schema = "\u{feff}event <A>::request {}";
        let event_spans =
            event_schema_spans(event_schema).expect("BOM-prefixed event schema should classify");
        assert!(event_spans.iter().all(|span| span.start >= 3));
        assert!(event_spans.iter().any(|span| {
            &event_schema[span.start..span.end] == "event" && span.kind == SyntaxKind::Keyword
        }));
    }
}
