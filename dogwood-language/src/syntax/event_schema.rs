//! Event-schema syntax walker over Dogwood's canonical Pest grammar.

use pest::Parser;
use pest::iterators::Pair;
use pest_derive::Parser;

use super::{SyntaxKind as TokenKind, SyntaxModifier as TokenModifier, SyntaxSpan as SemanticSpan};

#[derive(Parser)]
#[grammar = "event_schema/grammar.pest"]
struct EventSchemaParser;

pub(super) fn classify(source: &str, max_depth: usize) -> Option<Vec<SemanticSpan>> {
    // The generated parser recurses once per nesting level.
    if dogwood_syntax::nesting_depth_error::<Rule>(source, &[], max_depth).is_some() {
        return None;
    }
    let mut pairs = EventSchemaParser::parse(Rule::schema_entry, source).ok()?;
    let root = pairs.next()?;
    if pairs.next().is_some() {
        return None;
    }

    let mut spans = Vec::new();
    visit_schema(root, &mut spans)?;
    Some(spans)
}

fn visit_schema(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    if pair.as_rule() != Rule::schema_entry {
        return None;
    }
    let children = pair.into_inner().collect::<Vec<_>>();
    let mut index = 0;
    while let Some(child) = children.get(index).filter(|child| {
        matches!(
            child.as_rule(),
            Rule::max_window_decl | Rule::max_horizon_decl
        )
    }) {
        visit_directive(child.clone(), spans)?;
        index += 1;
    }
    while children
        .get(index)
        .is_some_and(|child| child.as_rule() == Rule::event_decl)
    {
        visit_event(children[index].clone(), spans)?;
        index += 1;
    }
    if children
        .get(index)
        .is_some_and(|child| child.as_rule() == Rule::EOI)
    {
        index += 1;
    }
    (index == children.len()).then_some(())
}

/// A `max_window = <interval>` or `max_horizon = <interval>` directive.
fn visit_directive(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let (rule, keyword) = match pair.as_rule() {
        Rule::max_window_decl => (Rule::max_window_decl, Rule::kw_max_window),
        Rule::max_horizon_decl => (Rule::max_horizon_decl, Rule::kw_max_horizon),
        _ => return None,
    };
    let children = exact_children(pair, rule, 2)?;
    if children[0].as_rule() != keyword || children[1].as_rule() != Rule::interval {
        return None;
    }
    emit(&children[0], TokenKind::Keyword, None, spans);
    let interval = exact_children(children[1].clone(), Rule::interval, 2)?;
    if interval[0].as_rule() != Rule::integer || interval[1].as_rule() != Rule::time_unit {
        return None;
    }
    emit(&interval[0], TokenKind::Number, None, spans);
    emit(&interval[1], TokenKind::Number, None, spans);
    Some(())
}

fn visit_event(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = pair.into_inner().collect::<Vec<_>>();
    let mut index = 0;
    if children
        .first()
        .is_some_and(|child| child.as_rule() == Rule::decision_marker)
    {
        visit_single_wrapper(
            children[0].clone(),
            Rule::decision_marker,
            Rule::kw_decision,
            TokenKind::Keyword,
            None,
            spans,
        )?;
        index += 1;
    }
    let keyword = children.get(index)?;
    let binder = children.get(index + 1)?;
    let event_kind = children.get(index + 2)?;
    if keyword.as_rule() != Rule::kw_event
        || binder.as_rule() != Rule::binder
        || event_kind.as_rule() != Rule::event_kind
    {
        return None;
    }
    emit(keyword, TokenKind::Keyword, None, spans);
    visit_identifier_wrapper(
        binder.clone(),
        Rule::binder,
        TokenKind::TypeParameter,
        Some(TokenModifier::Declaration),
        spans,
    )?;
    visit_identifier_wrapper(
        event_kind.clone(),
        Rule::event_kind,
        TokenKind::Event,
        Some(TokenModifier::Declaration),
        spans,
    )?;
    index += 3;
    if children
        .get(index)
        .is_some_and(|child| child.as_rule() == Rule::field_list)
    {
        visit_field_list(children[index].clone(), spans)?;
        index += 1;
    }
    (index == children.len()).then_some(())
}

fn visit_field_list(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = pair.into_inner().collect::<Vec<_>>();
    if children.is_empty() || children.iter().any(|child| child.as_rule() != Rule::field) {
        return None;
    }
    for field in children {
        let field = exact_children(field, Rule::field, 1)?;
        match field[0].as_rule() {
            Rule::spread => visit_spread(field[0].clone(), spans)?,
            Rule::named_field => visit_named_field(field[0].clone(), spans)?,
            _ => return None,
        }
    }
    Some(())
}

fn visit_spread(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = exact_children(pair, Rule::spread, 2)?;
    visit_selector(children[0].clone(), spans)?;
    visit_binder_ref(children[1].clone(), spans)
}

fn visit_named_field(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = pair.into_inner().collect::<Vec<_>>();
    let mut index = 0;
    if children
        .first()
        .is_some_and(|child| child.as_rule() == Rule::pin_marker)
    {
        visit_single_wrapper(
            children[0].clone(),
            Rule::pin_marker,
            Rule::kw_pin,
            TokenKind::Keyword,
            None,
            spans,
        )?;
        index += 1;
    }
    let field = children.get(index)?;
    let type_expression = children.get(index + 1)?;
    if field.as_rule() != Rule::ident || type_expression.as_rule() != Rule::type_expr {
        return None;
    }
    emit(
        field,
        TokenKind::Property,
        Some(TokenModifier::Declaration),
        spans,
    );
    visit_type_expression(type_expression.clone(), spans)?;
    index += 2;
    if children
        .get(index)
        .is_some_and(|child| child.as_rule() == Rule::pin_rhs)
    {
        visit_pin_rhs(children[index].clone(), spans)?;
        index += 1;
    }
    (index == children.len()).then_some(())
}

fn visit_type_expression(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = exact_children(pair, Rule::type_expr, 1)?;
    match children[0].as_rule() {
        Rule::selector_call => visit_selector_call(children[0].clone(), spans),
        Rule::record_type => visit_record(children[0].clone(), spans),
        Rule::concrete_type => visit_concrete_type(children[0].clone(), spans),
        _ => None,
    }
}

fn visit_selector_call(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = exact_children(pair, Rule::selector_call, 2)?;
    visit_selector(children[0].clone(), spans)?;
    visit_binder_ref(children[1].clone(), spans)
}

fn visit_selector(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = exact_children(pair, Rule::selector, 1)?;
    if !matches!(
        children[0].as_rule(),
        Rule::sel_inputs | Rule::sel_outputs | Rule::sel_principal_type | Rule::sel_resource_type
    ) {
        return None;
    }
    emit(&children[0], TokenKind::Function, None, spans);
    Some(())
}

fn visit_binder_ref(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    visit_identifier_wrapper(
        pair,
        Rule::binder_ref,
        TokenKind::TypeParameter,
        None,
        spans,
    )
}

fn visit_record(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = pair.into_inner().collect::<Vec<_>>();
    match children.as_slice() {
        [] => Some(()),
        [fields] if fields.as_rule() == Rule::field_list => visit_field_list(fields.clone(), spans),
        _ => None,
    }
}

fn visit_concrete_type(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = pair.into_inner().collect::<Vec<_>>();
    if children.is_empty() || children.iter().any(|child| child.as_rule() != Rule::ident) {
        return None;
    }
    let terminal = children.len() - 1;
    for (index, segment) in children.iter().enumerate() {
        emit(
            segment,
            if index == terminal {
                TokenKind::Type
            } else {
                TokenKind::Namespace
            },
            None,
            spans,
        );
    }
    Some(())
}

fn visit_pin_rhs(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = exact_children(pair, Rule::pin_rhs, 1)?;
    match children[0].as_rule() {
        Rule::pin_scope => visit_pin_scope(children[0].clone(), spans),
        Rule::pin_context => visit_pin_context(children[0].clone(), spans),
        _ => None,
    }
}

fn visit_pin_scope(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    let children = pair.into_inner().collect::<Vec<_>>();
    let root = children.first()?;
    if root.as_rule() != Rule::pin_scope_root
        || children[1..]
            .iter()
            .any(|child| child.as_rule() != Rule::ident)
    {
        return None;
    }
    emit(root, TokenKind::Variable, None, spans);
    for property in &children[1..] {
        emit(property, TokenKind::Property, None, spans);
    }
    Some(())
}

fn visit_pin_context(pair: Pair<'_, Rule>, spans: &mut Vec<SemanticSpan>) -> Option<()> {
    emit_prefix(&pair, "context", TokenKind::Variable, None, spans)?;
    let children = pair.into_inner().collect::<Vec<_>>();
    if children.is_empty() || children.iter().any(|child| child.as_rule() != Rule::ident) {
        return None;
    }
    for property in &children {
        emit(property, TokenKind::Property, None, spans);
    }
    Some(())
}

fn visit_identifier_wrapper(
    pair: Pair<'_, Rule>,
    wrapper: Rule,
    kind: TokenKind,
    modifier: Option<TokenModifier>,
    spans: &mut Vec<SemanticSpan>,
) -> Option<()> {
    let children = exact_children(pair, wrapper, 1)?;
    if children[0].as_rule() != Rule::ident {
        return None;
    }
    emit(&children[0], kind, modifier, spans);
    Some(())
}

fn visit_single_wrapper(
    pair: Pair<'_, Rule>,
    wrapper: Rule,
    child: Rule,
    kind: TokenKind,
    modifier: Option<TokenModifier>,
    spans: &mut Vec<SemanticSpan>,
) -> Option<()> {
    let children = exact_children(pair, wrapper, 1)?;
    if children[0].as_rule() != child {
        return None;
    }
    emit(&children[0], kind, modifier, spans);
    Some(())
}

fn exact_children(pair: Pair<'_, Rule>, rule: Rule, count: usize) -> Option<Vec<Pair<'_, Rule>>> {
    if pair.as_rule() != rule {
        return None;
    }
    let children = pair.into_inner().collect::<Vec<_>>();
    (children.len() == count).then_some(children)
}

fn emit(
    pair: &Pair<'_, Rule>,
    kind: TokenKind,
    modifier: Option<TokenModifier>,
    spans: &mut Vec<SemanticSpan>,
) {
    let span = pair.as_span();
    spans.push(SemanticSpan::new(span.start(), span.end(), kind, modifier));
}

fn emit_prefix(
    pair: &Pair<'_, Rule>,
    literal: &str,
    kind: TokenKind,
    modifier: Option<TokenModifier>,
    spans: &mut Vec<SemanticSpan>,
) -> Option<()> {
    let span = pair.as_span();
    let start = span.start();
    let end = start.checked_add(literal.len())?;
    if span.get_input().get(start..end)? != literal {
        return None;
    }
    spans.push(SemanticSpan::new(start, end, kind, modifier));
    Some(())
}
