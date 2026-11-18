//! Policy and temporal syntax walkers over Dogwood's canonical Pest grammars.

use super::SyntaxSpan as SemanticSpan;

pub(super) fn classify(source: &str, base: usize, max_depth: usize) -> Option<Vec<SemanticSpan>> {
    policy_grammar::classify(source, base, max_depth)
}

mod policy_grammar {
    use dogwood_syntax::Rule;
    use pest::iterators::Pair;

    use super::{SemanticSpan, temporal};
    use crate::syntax::{SyntaxKind as TokenKind, SyntaxModifier as TokenModifier};

    pub(super) fn classify(
        source: &str,
        base: usize,
        max_depth: usize,
    ) -> Option<Vec<SemanticSpan>> {
        let options = dogwood_syntax::ParseOptions::default().max_depth(max_depth);
        let mut pairs = dogwood_syntax::parse_with(Rule::policies, source, &options).ok()?;
        let root = pairs.next()?;
        let mut spans = Vec::new();
        visit(root, source, base, max_depth, &mut spans)?;
        Some(spans)
    }

    fn visit(
        pair: Pair<'_, Rule>,
        source: &str,
        base: usize,
        max_depth: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        match pair.as_rule() {
            Rule::def_decl => visit_definition(pair, source, base, max_depth, spans),
            Rule::extension_marker => {
                for child in pair.into_inner() {
                    match child.as_rule() {
                        Rule::dialect_tag => {
                            emit(&child, base, TokenKind::Keyword, None, spans);
                        }
                        Rule::block_inner => {
                            let block_base = base + child.as_span().start();
                            let mut body = temporal::classify_condition(
                                child.as_str(),
                                block_base,
                                max_depth,
                            )?;
                            spans.append(&mut body);
                        }
                        _ => visit(child, source, base, max_depth, spans)?,
                    }
                }
                Some(())
            }
            Rule::annotation => {
                for child in pair.into_inner() {
                    if child.as_rule() == Rule::any_ident {
                        emit(&child, base, TokenKind::Decorator, None, spans);
                    } else {
                        visit(child, source, base, max_depth, spans)?;
                    }
                }
                Some(())
            }
            Rule::effect | Rule::cond_kw => {
                emit(&pair, base, TokenKind::Keyword, None, spans);
                Some(())
            }
            Rule::variable_def => visit_scope_variable(pair, source, base, max_depth, spans),
            Rule::ref_ => {
                for child in pair.into_inner() {
                    match child.as_rule() {
                        Rule::name => classify_type_name(child, base, spans),
                        _ => visit(child, source, base, max_depth, spans)?,
                    }
                }
                Some(())
            }
            Rule::member => visit_member(pair, source, base, max_depth, spans),
            Rule::has_tail => visit_has_tail(pair, source, base, max_depth, spans),
            Rule::is_tail => visit_is_tail(pair, source, base, max_depth, spans),
            Rule::rec_init => visit_record_entry(pair, source, base, max_depth, spans),
            Rule::access_field => {
                classify_direct_child(
                    pair,
                    Rule::any_ident,
                    base,
                    TokenKind::Property,
                    None,
                    spans,
                );
                Some(())
            }
            Rule::name => {
                classify_name(pair, base, TokenKind::Variable, spans);
                Some(())
            }
            Rule::slot_principal | Rule::slot_resource => {
                emit(&pair, base, TokenKind::Variable, None, spans);
                Some(())
            }
            Rule::slot_other => {
                emit(&pair, base, TokenKind::Parameter, None, spans);
                Some(())
            }
            Rule::number => {
                emit(&pair, base, TokenKind::Number, None, spans);
                Some(())
            }
            Rule::string => {
                emit(&pair, base, TokenKind::String, None, spans);
                Some(())
            }
            Rule::kw_def
            | Rule::kw_def_cedar
            | Rule::kw_def_temporal
            | Rule::kw_true
            | Rule::kw_false
            | Rule::kw_if
            | Rule::kw_then
            | Rule::kw_else
            | Rule::kw_in
            | Rule::kw_has
            | Rule::kw_like
            | Rule::kw_is
            | Rule::kw_permit
            | Rule::kw_forbid
            | Rule::kw_when
            | Rule::kw_unless
            | Rule::dialect_tag
            | Rule::guardrails_tag => {
                emit(&pair, base, TokenKind::Keyword, None, spans);
                Some(())
            }
            Rule::block_inner | Rule::EOI => Some(()),
            _ => {
                for child in pair.into_inner() {
                    visit(child, source, base, max_depth, spans)?;
                }
                Some(())
            }
        }
    }

    fn visit_definition(
        pair: Pair<'_, Rule>,
        source: &str,
        base: usize,
        max_depth: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        let mut kind = None;
        let mut saw_name = false;
        for child in pair.into_inner() {
            match child.as_rule() {
                Rule::kw_def => emit(&child, base, TokenKind::Keyword, None, spans),
                Rule::def_kind => {
                    kind = Some(child.as_str());
                    visit(child, source, base, max_depth, spans)?;
                }
                Rule::ident if !saw_name => {
                    saw_name = true;
                    emit(
                        &child,
                        base,
                        TokenKind::Macro,
                        Some(TokenModifier::Declaration),
                        spans,
                    );
                }
                Rule::param_list => {
                    for param in child
                        .into_inner()
                        .filter(|param| param.as_rule() == Rule::param)
                    {
                        emit(
                            &param,
                            base,
                            TokenKind::Parameter,
                            Some(TokenModifier::Declaration),
                            spans,
                        );
                    }
                }
                Rule::block_inner => {
                    let block_base = base + child.as_span().start();
                    let mut body_spans = match kind {
                        Some("cedar") => {
                            classify_cedar_body(child.as_str(), block_base, max_depth)?
                        }
                        Some("temporal") => {
                            temporal::classify_macro_body(child.as_str(), block_base, max_depth)?
                        }
                        _ => return None,
                    };
                    spans.append(&mut body_spans);
                }
                _ => visit(child, source, base, max_depth, spans)?,
            }
        }
        Some(())
    }

    fn classify_cedar_body(
        source: &str,
        base: usize,
        max_depth: usize,
    ) -> Option<Vec<SemanticSpan>> {
        let options = dogwood_syntax::ParseOptions::default().max_depth(max_depth);
        let mut pairs = dogwood_syntax::parse_with(Rule::expr_entry, source, &options).ok()?;
        let root = pairs.next()?;
        let mut spans = Vec::new();
        visit(root, source, base, max_depth, &mut spans)?;
        Some(spans)
    }

    fn visit_scope_variable(
        pair: Pair<'_, Rule>,
        source: &str,
        base: usize,
        max_depth: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        let children = pair.into_inner().collect::<Vec<_>>();
        let mut index = 0;
        if children
            .first()
            .is_some_and(|child| child.as_rule() == Rule::any_ident)
        {
            emit(&children[0], base, TokenKind::Variable, None, spans);
            index = 1;
        }

        while index < children.len() {
            let child = children[index].clone();
            if child.as_rule() == Rule::kw_is {
                emit(&child, base, TokenKind::Keyword, None, spans);
                index += 1;
                if let Some(type_expr) = children.get(index) {
                    classify_type_expression(type_expr.clone(), base, spans)?;
                    index += 1;
                }
                continue;
            }
            visit(child, source, base, max_depth, spans)?;
            index += 1;
        }
        Some(())
    }

    fn visit_member(
        pair: Pair<'_, Rule>,
        source: &str,
        base: usize,
        max_depth: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        let mut children = pair.into_inner();
        let primary = children.next()?;
        let accessors = children
            .filter(|child| child.as_rule() == Rule::mem_access)
            .filter_map(|child| child.into_inner().next())
            .collect::<Vec<_>>();

        let primary_name = find_descendant(primary.clone(), Rule::name);
        let is_function = primary_name.is_some()
            && accessors
                .first()
                .is_some_and(|accessor| accessor.as_rule() == Rule::access_call);
        if is_function {
            classify_callable(primary_name?, base, spans);
        } else {
            visit(primary, source, base, max_depth, spans)?;
        }

        let mut index = 0;
        while index < accessors.len() {
            let accessor = accessors[index].clone();
            match accessor.as_rule() {
                Rule::access_field => {
                    let is_method = accessors
                        .get(index + 1)
                        .is_some_and(|next| next.as_rule() == Rule::access_call);
                    classify_direct_child(
                        accessor,
                        Rule::any_ident,
                        base,
                        if is_method {
                            TokenKind::Method
                        } else {
                            TokenKind::Property
                        },
                        None,
                        spans,
                    );
                    if is_method {
                        visit(accessors[index + 1].clone(), source, base, max_depth, spans)?;
                        index += 1;
                    }
                }
                _ => visit(accessor, source, base, max_depth, spans)?,
            }
            index += 1;
        }
        Some(())
    }

    fn visit_has_tail(
        pair: Pair<'_, Rule>,
        source: &str,
        base: usize,
        max_depth: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        for child in pair.into_inner() {
            match child.as_rule() {
                Rule::kw_has => emit(&child, base, TokenKind::Keyword, None, spans),
                Rule::has_rhs => {
                    for nested in child.into_inner() {
                        classify_property_path(nested, base, spans)?;
                    }
                }
                _ => visit(child, source, base, max_depth, spans)?,
            }
        }
        Some(())
    }

    fn classify_property_path(
        pair: Pair<'_, Rule>,
        base: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        match pair.as_rule() {
            Rule::has_if_rhs => {
                for child in pair.into_inner() {
                    if child.as_rule() == Rule::kw_if {
                        emit(&child, base, TokenKind::Property, None, spans);
                    } else {
                        classify_property_path(child, base, spans)?;
                    }
                }
                Some(())
            }
            Rule::name => {
                for segment in name_segments(pair) {
                    emit(&segment, base, TokenKind::Property, None, spans);
                }
                Some(())
            }
            Rule::access_field => {
                classify_direct_child(
                    pair,
                    Rule::any_ident,
                    base,
                    TokenKind::Property,
                    None,
                    spans,
                );
                Some(())
            }
            Rule::string => {
                emit(&pair, base, TokenKind::Property, None, spans);
                Some(())
            }
            _ => {
                for child in pair.into_inner() {
                    classify_property_path(child, base, spans)?;
                }
                Some(())
            }
        }
    }

    fn visit_is_tail(
        pair: Pair<'_, Rule>,
        source: &str,
        base: usize,
        max_depth: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        let mut type_seen = false;
        for child in pair.into_inner() {
            match child.as_rule() {
                Rule::kw_is | Rule::kw_in => {
                    emit(&child, base, TokenKind::Keyword, None, spans);
                }
                Rule::add if !type_seen => {
                    type_seen = true;
                    classify_type_expression(child, base, spans)?;
                }
                _ => visit(child, source, base, max_depth, spans)?,
            }
        }
        Some(())
    }

    fn visit_record_entry(
        pair: Pair<'_, Rule>,
        source: &str,
        base: usize,
        max_depth: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        let inner = pair.into_inner().next()?;
        match inner.as_rule() {
            Rule::rec_init_if => {
                for child in inner.into_inner() {
                    if child.as_rule() == Rule::kw_if {
                        emit(&child, base, TokenKind::Property, None, spans);
                    } else {
                        visit(child, source, base, max_depth, spans)?;
                    }
                }
            }
            Rule::rec_init_expr => {
                let expressions = inner
                    .into_inner()
                    .filter(|child| child.as_rule() == Rule::expr)
                    .collect::<Vec<_>>();
                let key = expressions.first()?.clone();
                if let Some(name) = find_descendant(key.clone(), Rule::name) {
                    classify_name(name, base, TokenKind::Property, spans);
                } else {
                    let string = find_descendant(key, Rule::string)?;
                    emit(&string, base, TokenKind::Property, None, spans);
                }
                if let Some(value) = expressions.get(1) {
                    visit(value.clone(), source, base, max_depth, spans)?;
                }
            }
            _ => return None,
        }
        Some(())
    }

    fn classify_type_expression(
        pair: Pair<'_, Rule>,
        base: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        let name = find_descendant(pair, Rule::name)?;
        classify_type_name(name, base, spans);
        Some(())
    }

    fn classify_type_name(pair: Pair<'_, Rule>, base: usize, spans: &mut Vec<SemanticSpan>) {
        let segments = name_segments(pair);
        let final_index = segments.len().saturating_sub(1);
        for (index, segment) in segments.into_iter().enumerate() {
            emit(
                &segment,
                base,
                if index == final_index {
                    TokenKind::Type
                } else {
                    TokenKind::Namespace
                },
                None,
                spans,
            );
        }
    }

    fn classify_callable(pair: Pair<'_, Rule>, base: usize, spans: &mut Vec<SemanticSpan>) {
        let segments = name_segments(pair);
        let final_index = segments.len().saturating_sub(1);
        let is_qualified = segments.len() > 1;
        for (index, segment) in segments.into_iter().enumerate() {
            let kind = if index < final_index {
                TokenKind::Namespace
            } else if is_qualified
                || matches!(segment.as_str(), "decimal" | "datetime" | "duration" | "ip")
            {
                TokenKind::Function
            } else {
                TokenKind::Macro
            };
            emit(&segment, base, kind, None, spans);
        }
    }

    fn classify_name(
        pair: Pair<'_, Rule>,
        base: usize,
        final_kind: TokenKind,
        spans: &mut Vec<SemanticSpan>,
    ) {
        let segments = name_segments(pair);
        let final_index = segments.len().saturating_sub(1);
        for (index, segment) in segments.into_iter().enumerate() {
            emit(
                &segment,
                base,
                if index == final_index {
                    final_kind
                } else {
                    TokenKind::Namespace
                },
                None,
                spans,
            );
        }
    }

    fn name_segments(pair: Pair<'_, Rule>) -> Vec<Pair<'_, Rule>> {
        pair.into_inner()
            .filter(|child| {
                matches!(
                    child.as_rule(),
                    Rule::any_ident | Rule::common_ident | Rule::special_ident
                )
            })
            .collect()
    }

    fn classify_direct_child(
        pair: Pair<'_, Rule>,
        rule: Rule,
        base: usize,
        kind: TokenKind,
        modifier: Option<TokenModifier>,
        spans: &mut Vec<SemanticSpan>,
    ) {
        if let Some(child) = pair.into_inner().find(|child| child.as_rule() == rule) {
            emit(&child, base, kind, modifier, spans);
        }
    }

    fn find_descendant(pair: Pair<'_, Rule>, rule: Rule) -> Option<Pair<'_, Rule>> {
        if pair.as_rule() == rule {
            return Some(pair);
        }
        pair.into_inner()
            .find_map(|child| find_descendant(child, rule))
    }

    fn emit(
        pair: &Pair<'_, Rule>,
        base: usize,
        kind: TokenKind,
        modifier: Option<TokenModifier>,
        spans: &mut Vec<SemanticSpan>,
    ) {
        let span = pair.as_span();
        spans.push(SemanticSpan::new(
            base + span.start(),
            base + span.end(),
            kind,
            modifier,
        ));
    }
}

mod temporal {
    use pest::Parser;
    use pest::iterators::Pair;
    use pest_derive::Parser;

    use super::SemanticSpan;
    use crate::syntax::{SyntaxKind as TokenKind, SyntaxModifier as TokenModifier};

    #[derive(Parser)]
    #[grammar = "extension/temporal/grammar.pest"]
    struct TemporalParser;

    pub(super) fn classify_condition(
        source: &str,
        base: usize,
        max_depth: usize,
    ) -> Option<Vec<SemanticSpan>> {
        classify_entry(source, base, Rule::condition_entry, max_depth)
    }

    pub(super) fn classify_macro_body(
        source: &str,
        base: usize,
        max_depth: usize,
    ) -> Option<Vec<SemanticSpan>> {
        classify_entry(source, base, Rule::temporal_macro_body_entry, max_depth)
    }

    fn classify_entry(
        source: &str,
        base: usize,
        rule: Rule,
        max_depth: usize,
    ) -> Option<Vec<SemanticSpan>> {
        // The generated parser recurses once per nesting level, binders
        // included; the walk below recurses once per level of its tree.
        let keywords = crate::extension::temporal::parse::NESTING_KEYWORDS;
        if dogwood_syntax::nesting_depth_error::<Rule>(source, keywords, max_depth).is_some() {
            return None;
        }
        let mut pairs = TemporalParser::parse(rule, source).ok()?;
        let root = pairs.next()?;
        let mut spans = Vec::new();
        visit(root, base, &mut spans)?;
        Some(spans)
    }

    fn visit(pair: Pair<'_, Rule>, base: usize, spans: &mut Vec<SemanticSpan>) -> Option<()> {
        match pair.as_rule() {
            Rule::conjunct_or_since => visit_since(pair, base, spans),
            Rule::predicate => visit_predicate(pair, base, spans),
            Rule::field_path => {
                for child in pair
                    .into_inner()
                    .filter(|child| child.as_rule() == Rule::ident)
                {
                    emit(&child, base, TokenKind::Property, None, spans);
                }
                Some(())
            }
            Rule::context_field => {
                emit_prefix(&pair, "context", base, TokenKind::Variable, None, spans)?;
                for child in pair
                    .into_inner()
                    .filter(|child| child.as_rule() == Rule::ident)
                {
                    emit(&child, base, TokenKind::Property, None, spans);
                }
                Some(())
            }
            Rule::scope_field => {
                for child in pair.into_inner() {
                    match child.as_rule() {
                        Rule::scope_root => {
                            emit(&child, base, TokenKind::Variable, None, spans);
                        }
                        Rule::ident => emit(&child, base, TokenKind::Property, None, spans),
                        _ => {}
                    }
                }
                Some(())
            }
            Rule::entity => {
                classify_entity(pair, base, spans);
                Some(())
            }
            Rule::decimal_lit => {
                emit_prefix(&pair, "decimal", base, TokenKind::Function, None, spans)?;
                for child in pair.into_inner() {
                    visit(child, base, spans)?;
                }
                Some(())
            }
            Rule::tp_op => visit_prefixed(pair, "tp", base, spans),
            Rule::exists_op => visit_prefixed(pair, "exists", base, spans),
            Rule::once_op => visit_prefixed(pair, "formerly", base, spans),
            Rule::previous_op => visit_prefixed(pair, "previous", base, spans),
            Rule::sum_expr => visit_aggregation(pair, "sum", base, spans),
            Rule::count_expr => visit_aggregation(pair, "count", base, spans),
            Rule::for_binders => visit_prefixed(pair, "for", base, spans),
            Rule::within => visit_prefixed(pair, "within", base, spans),
            Rule::call => {
                for child in pair.into_inner() {
                    if child.as_rule() == Rule::ident {
                        emit(&child, base, TokenKind::Macro, None, spans);
                    } else {
                        visit(child, base, spans)?;
                    }
                }
                Some(())
            }
            Rule::typed_binder => {
                for child in pair.into_inner() {
                    match child.as_rule() {
                        Rule::binder_slot => {
                            classify_binder(child, base, true, spans)?;
                        }
                        Rule::type_expr => classify_type(child, base, spans),
                        _ => visit(child, base, spans)?,
                    }
                }
                Some(())
            }
            Rule::binder_slot => classify_binder(pair, base, false, spans),
            Rule::type_expr => {
                classify_type(pair, base, spans);
                Some(())
            }
            Rule::within_payload | Rule::interval_lit => {
                let children = pair.into_inner().collect::<Vec<_>>();
                match children.as_slice() {
                    [param] if param.as_rule() == Rule::param_ref => {
                        emit(param, base, TokenKind::Parameter, None, spans);
                    }
                    [integer, unit]
                        if integer.as_rule() == Rule::integer
                            && unit.as_rule() == Rule::time_unit =>
                    {
                        emit(integer, base, TokenKind::Number, None, spans);
                        emit(unit, base, TokenKind::Number, None, spans);
                    }
                    _ => return None,
                }
                Some(())
            }
            Rule::event_kind => {
                emit(&pair, base, TokenKind::Event, None, spans);
                Some(())
            }
            Rule::param_ref => {
                emit(&pair, base, TokenKind::Parameter, None, spans);
                Some(())
            }
            Rule::binder_ref | Rule::ident => {
                emit(&pair, base, TokenKind::Variable, None, spans);
                Some(())
            }
            Rule::integer => {
                emit(&pair, base, TokenKind::Number, None, spans);
                Some(())
            }
            Rule::string => {
                emit(&pair, base, TokenKind::String, None, spans);
                Some(())
            }
            Rule::kw_true | Rule::kw_false => {
                emit(&pair, base, TokenKind::Keyword, None, spans);
                Some(())
            }
            Rule::scope_root | Rule::time_unit | Rule::EOI => Some(()),
            _ => {
                for child in pair.into_inner() {
                    visit(child, base, spans)?;
                }
                Some(())
            }
        }
    }

    fn visit_since(pair: Pair<'_, Rule>, base: usize, spans: &mut Vec<SemanticSpan>) -> Option<()> {
        let children = pair.into_inner().collect::<Vec<_>>();
        match children.as_slice() {
            [left] if left.as_rule() == Rule::neg_conjunct => {}
            [left, within, right]
                if left.as_rule() == Rule::neg_conjunct
                    && within.as_rule() == Rule::within
                    && right.as_rule() == Rule::atom =>
            {
                emit_between(left, within, "since", base, TokenKind::Keyword, None, spans)?;
            }
            _ => return None,
        }
        for child in children {
            visit(child, base, spans)?;
        }
        Some(())
    }

    fn visit_prefixed(
        pair: Pair<'_, Rule>,
        keyword: &str,
        base: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        emit_prefix(&pair, keyword, base, TokenKind::Keyword, None, spans)?;
        for child in pair.into_inner() {
            visit(child, base, spans)?;
        }
        Some(())
    }

    fn visit_aggregation(
        pair: Pair<'_, Rule>,
        keyword: &str,
        base: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        emit_prefix(&pair, keyword, base, TokenKind::Keyword, None, spans)?;
        let children = pair.into_inner().collect::<Vec<_>>();
        let for_binders = children
            .iter()
            .find(|child| child.as_rule() == Rule::for_binders)?;
        let condition = children
            .iter()
            .find(|child| child.as_rule() == Rule::condition)?;
        emit_between(
            for_binders,
            condition,
            "where",
            base,
            TokenKind::Keyword,
            None,
            spans,
        )?;
        for child in children {
            visit(child, base, spans)?;
        }
        Some(())
    }

    fn visit_predicate(
        pair: Pair<'_, Rule>,
        base: usize,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        for child in pair.into_inner() {
            match child.as_rule() {
                Rule::qualified_action => classify_qualified_action(child, base, spans),
                Rule::event_kind => emit(&child, base, TokenKind::Event, None, spans),
                _ => visit(child, base, spans)?,
            }
        }
        Some(())
    }

    fn classify_qualified_action(pair: Pair<'_, Rule>, base: usize, spans: &mut Vec<SemanticSpan>) {
        let children = pair.into_inner().collect::<Vec<_>>();
        let identifiers = children
            .iter()
            .filter(|child| child.as_rule() == Rule::ident)
            .cloned()
            .collect::<Vec<_>>();
        let final_index = identifiers.len().saturating_sub(1);
        for (index, identifier) in identifiers.into_iter().enumerate() {
            emit(
                &identifier,
                base,
                if index == final_index {
                    TokenKind::Type
                } else {
                    TokenKind::Namespace
                },
                None,
                spans,
            );
        }
        if let Some(string) = children
            .into_iter()
            .find(|child| child.as_rule() == Rule::string)
        {
            emit(&string, base, TokenKind::String, None, spans);
        }
    }

    fn classify_entity(pair: Pair<'_, Rule>, base: usize, spans: &mut Vec<SemanticSpan>) {
        classify_qualified_action(pair, base, spans);
    }

    fn classify_binder(
        pair: Pair<'_, Rule>,
        base: usize,
        declaration: bool,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        let child = pair.into_inner().next()?;
        let kind = if child.as_rule() == Rule::param_ref {
            TokenKind::Parameter
        } else {
            TokenKind::Variable
        };
        emit(
            &child,
            base,
            kind,
            declaration.then_some(TokenModifier::Declaration),
            spans,
        );
        Some(())
    }

    fn classify_type(pair: Pair<'_, Rule>, base: usize, spans: &mut Vec<SemanticSpan>) {
        let identifiers = pair
            .into_inner()
            .filter(|child| child.as_rule() == Rule::ident)
            .collect::<Vec<_>>();
        let final_index = identifiers.len().saturating_sub(1);
        for (index, identifier) in identifiers.into_iter().enumerate() {
            emit(
                &identifier,
                base,
                if index == final_index {
                    TokenKind::Type
                } else {
                    TokenKind::Namespace
                },
                None,
                spans,
            );
        }
    }

    fn emit(
        pair: &Pair<'_, Rule>,
        base: usize,
        kind: TokenKind,
        modifier: Option<TokenModifier>,
        spans: &mut Vec<SemanticSpan>,
    ) {
        let span = pair.as_span();
        spans.push(SemanticSpan::new(
            base + span.start(),
            base + span.end(),
            kind,
            modifier,
        ));
    }

    fn emit_prefix(
        pair: &Pair<'_, Rule>,
        literal: &str,
        base: usize,
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
        spans.push(SemanticSpan::new(base + start, base + end, kind, modifier));
        Some(())
    }

    fn emit_between(
        left: &Pair<'_, Rule>,
        right: &Pair<'_, Rule>,
        literal: &str,
        base: usize,
        kind: TokenKind,
        modifier: Option<TokenModifier>,
        spans: &mut Vec<SemanticSpan>,
    ) -> Option<()> {
        let left_span = left.as_span();
        let right_span = right.as_span();
        let input = left_span.get_input();
        if input.as_ptr() != right_span.get_input().as_ptr() {
            return None;
        }
        let start = skip_trivia(input, left_span.end(), right_span.start())?;
        let end = start.checked_add(literal.len())?;
        if end > right_span.start() || input.get(start..end)? != literal {
            return None;
        }
        spans.push(SemanticSpan::new(base + start, base + end, kind, modifier));
        Some(())
    }

    fn skip_trivia(input: &str, mut cursor: usize, end: usize) -> Option<usize> {
        let bytes = input.as_bytes();
        while cursor < end {
            while cursor < end && bytes[cursor].is_ascii_whitespace() {
                cursor += 1;
            }
            if cursor + 1 < end && bytes[cursor] == b'/' && bytes[cursor + 1] == b'/' {
                cursor += 2;
                while cursor < end && !matches!(bytes[cursor], b'\n' | b'\r') {
                    cursor += 1;
                }
                continue;
            }
            break;
        }
        input.is_char_boundary(cursor).then_some(cursor)
    }
}
