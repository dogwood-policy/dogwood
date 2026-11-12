//! The Dogwood parser.
//!
//! Built on the shared `dogwood-syntax` Pest grammar, a translation of Cedar's
//! policy grammar extended with the dialect-marker condition form (`when
//! temporal { ... }`, `unless provider { ... }`). The parse tree is walked
//! into the surface [`crate::ast`].
//!
//! The body of a `when`/`unless` clause is parsed into a structured
//! [`crate::ast::Expr`] tree via [`build_expr`] — a tree-walk over the
//! Cedar expression-precedence tower (`expr → or → and → rel → add →
//! mult → unary → member → primary`). An extension marker (`temporal
//! { … }` / `provider { … }`) is admitted as a `primary`, so it becomes
//! an [`crate::ast::Expr::Extension`] leaf and may appear anywhere in the
//! expression, not just as a whole clause. The policy scope is likewise
//! parsed into structured loc-bearing `cedar_ast` constraints by
//! [`build_scope`], so a scope error points at the offending token.

use cedar_ast::{ActionConstraint, EntityReference, PrincipalConstraint, ResourceConstraint};
use cedar_policy::pst;
use cedar_policy_core::ast as cedar_ast;
use cedar_policy_core::parser::Loc;
use cedar_policy_core::parser::unescape::to_unescaped_string;
use dogwood_syntax::{Pair, ParseOptions, Rule};
use rustc_literal_escaper::{EscapeError, unescape_str};

use crate::ast::{
    Annotation, BinOp, Cond, CondKeyword, Effect, Expr, ExprKind, MacroBody, MacroDef, MacroParam,
    Policy, PolicySet, Scope, UnOp,
};
use crate::error::{RawParseError, Span};
use crate::extension::temporal;
use crate::extension::{Dialect, Extension};

use std::cell::Cell;

// Tracks whether expression parsing is currently inside a scope constraint
// (as opposed to a condition body). Used by `resolve_name` to tailor error
// messages — scope context can suggest `is Type`, condition context cannot.
thread_local! {
    static IN_SCOPE_CONTEXT: Cell<bool> = const { Cell::new(false) };
}

/// RAII guard that sets `IN_SCOPE_CONTEXT` to `true` on creation and resets
/// it to `false` on drop — even if the enclosed code panics.
struct ScopeContextGuard;

impl ScopeContextGuard {
    fn enter() -> Self {
        IN_SCOPE_CONTEXT.with(|c| c.set(true));
        ScopeContextGuard
    }
}

impl Drop for ScopeContextGuard {
    fn drop(&mut self) {
        IN_SCOPE_CONTEXT.with(|c| c.set(false));
    }
}

fn span_of(pair: &Pair<'_>) -> Span {
    let s = pair.as_span();
    Span::new(s.start(), s.end())
}

fn err(message: impl Into<String>, span: Span) -> RawParseError {
    RawParseError {
        message: message.into(),
        span,
    }
}

/// Reject a tree measured `depth` deep when that exceeds `limit`
/// ([`ParseOptions::max_depth`](dogwood_syntax::ParseOptions::max_depth)).
///
/// Flat text builds deep trees (`!!!…x`, `a && b && …`, `x.a.b.…`), and
/// every later pass over a tree, its drop included, may recurse once per
/// level. The builders construct chains with loops, and a tree of any depth
/// is freed without recursion (see `deep_drop`), so a too-deep tree exists
/// only between its construction and this check on the finished root;
/// nothing recurses over it in between.
fn check_depth(depth: usize, limit: usize, span: Span) -> Result<(), RawParseError> {
    if depth > limit {
        return Err(err(
            format!("expression nested deeper than the limit of {limit}"),
            span,
        ));
    }
    Ok(())
}

/// Build a whole expression (a condition body, a scope operand, or a `def
/// cedar` body) and reject it if its finished tree, temporal subterms
/// included, is deeper than `limit`. This measured check on the root is the
/// depth bound; the builders below do not count.
fn build_root(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    let expr = match pair.as_rule() {
        Rule::extension_marker => build_extension_marker(pair, limit)?,
        _ => build_expr(pair, limit)?,
    };
    check_depth(expr_depth(&expr), limit, expr.span)?;
    Ok(expr)
}

/// The depth of `expr`, measured with an explicit stack so that measuring a
/// deep tree cannot itself overflow.
pub(crate) fn expr_depth(expr: &Expr) -> usize {
    tree_measure(DepthNode::Expr(expr)).depth
}

/// The depth of a temporal condition; see [`expr_depth`].
pub(crate) fn condition_depth(condition: &temporal::ast::Condition) -> usize {
    tree_measure(DepthNode::Condition(condition)).depth
}

/// The depth of a temporal term; see [`expr_depth`].
pub(crate) fn term_depth(term: &temporal::ast::Term) -> usize {
    tree_measure(DepthNode::Term(term)).depth
}

/// The number of nodes in `expr` (every `Expr`, temporal `Condition`, `Term`,
/// and aggregation node), the measure [`ParseOptions::max_nodes`] bounds,
/// counted with an explicit stack like [`expr_depth`].
pub(crate) fn expr_size(expr: &Expr) -> usize {
    tree_size(DepthNode::Expr(expr))
}

/// The number of nodes in a temporal condition; see [`expr_size`].
pub(crate) fn condition_size(condition: &temporal::ast::Condition) -> usize {
    tree_size(DepthNode::Condition(condition))
}

/// The number of nodes in a temporal term; see [`expr_size`].
pub(crate) fn term_size(term: &temporal::ast::Term) -> usize {
    tree_size(DepthNode::Term(term))
}

/// A tree's depth and its number of nodes, from one walk.
#[derive(Debug, Clone, Copy)]
struct TreeMeasure {
    depth: usize,
    size: usize,
}

fn tree_size(root: DepthNode<'_>) -> usize {
    tree_measure(root).size
}

enum DepthNode<'a> {
    Expr(&'a Expr),
    Condition(&'a temporal::ast::Condition),
    Term(&'a temporal::ast::Term),
    Agg(&'a temporal::ast::AggExpr),
}

/// The depth and size of the tree under `root`; the walk keeps its own stack,
/// so a deep tree cannot overflow the thread's.
fn tree_measure(root: DepthNode<'_>) -> TreeMeasure {
    use DepthNode as Node;
    use temporal::ast::{AggExprKind, CallArg, ConditionKind, Term};

    let mut max = 0;
    let mut size = 0;
    let mut stack = vec![(root, 1)];
    while let Some((node, depth)) = stack.pop() {
        max = max.max(depth);
        size += 1;
        let mut push = |child| stack.push((child, depth + 1));
        match node {
            Node::Expr(e) => match &e.kind {
                ExprKind::Lit(_)
                | ExprKind::Var(_)
                | ExprKind::Slot(_)
                | ExprKind::ParamRef { .. } => {}
                ExprKind::Extension(Extension::Temporal(t)) => push(Node::Condition(&t.condition)),
                ExprKind::UnaryApp { expr, .. }
                | ExprKind::GetAttr { expr, .. }
                | ExprKind::Like { expr, .. } => push(Node::Expr(expr)),
                // The parser keeps `e has a.b.c` as one node with a flat path,
                // but lowering (`cedarify::to_ast`, through Cedar 4.11's
                // `ExprBuilder::extended_has_attr`, which has no flat node and
                // desugars every path) spells a path of `k` segments as a
                // left-nested `&&` of `k` `has` tests, the last over a `GetAttr`
                // chain of `k - 1`: `e` ends up exactly `k + 1` levels below the
                // root `&&` (one, for a single segment). Measure that, so a long
                // path is refused here, before anything recurses over the
                // lowered tree.
                ExprKind::HasAttr { expr, attrs } => {
                    let below = attrs.len() + usize::from(attrs.len() > 1);
                    stack.push((Node::Expr(expr), depth + below.max(1)));
                }
                ExprKind::BinaryApp { left, right, .. } => {
                    push(Node::Expr(left));
                    push(Node::Expr(right));
                }
                ExprKind::Is { expr, in_expr, .. } => {
                    push(Node::Expr(expr));
                    if let Some(in_expr) = in_expr {
                        push(Node::Expr(in_expr));
                    }
                }
                ExprKind::IfThenElse {
                    cond,
                    then_expr,
                    else_expr,
                } => {
                    push(Node::Expr(cond));
                    push(Node::Expr(then_expr));
                    push(Node::Expr(else_expr));
                }
                ExprKind::Set(elems) | ExprKind::Call { args: elems, .. } => {
                    elems.iter().for_each(|e| push(Node::Expr(e)));
                }
                ExprKind::Record(map) => map.values().for_each(|e| push(Node::Expr(e))),
                ExprKind::MethodCall { receiver, args, .. } => {
                    push(Node::Expr(receiver));
                    args.iter().for_each(|e| push(Node::Expr(e)));
                }
            },
            Node::Condition(c) => match &c.kind {
                ConditionKind::And { left, right }
                | ConditionKind::Or { left, right }
                | ConditionKind::Since { left, right, .. } => {
                    push(Node::Condition(left));
                    push(Node::Condition(right));
                }
                ConditionKind::Not { inner: body }
                | ConditionKind::Formerly { body, .. }
                | ConditionKind::Previous { body, .. }
                | ConditionKind::Exists { body, .. } => push(Node::Condition(body)),
                ConditionKind::Predicate(p) => {
                    p.args.iter().for_each(|a| push(Node::Term(&a.value)))
                }
                ConditionKind::Comparison { left, right, .. } => {
                    push(Node::Term(left));
                    push(Node::Term(right));
                }
                ConditionKind::Call(call) => {
                    for arg in &call.args {
                        match arg {
                            CallArg::Condition(c) => push(Node::Condition(c)),
                            CallArg::Term(t) => push(Node::Term(t)),
                            CallArg::Within(_) => {}
                        }
                    }
                }
                ConditionKind::Refine { base, fields, .. } => {
                    push(Node::Condition(base));
                    fields.iter().for_each(|a| push(Node::Term(&a.value)));
                }
                ConditionKind::Tp { .. } | ConditionKind::SigilRef { .. } => {}
            },
            Node::Term(t) => match t {
                Term::Array(items) => items.iter().for_each(|t| push(Node::Term(t))),
                Term::Agg(agg) => push(Node::Agg(agg)),
                Term::Arith { left, right, .. } => {
                    push(Node::Term(left));
                    push(Node::Term(right));
                }
                Term::Entity { .. }
                | Term::Integer(_)
                | Term::Decimal(_)
                | Term::String(_)
                | Term::Bool(_)
                | Term::ContextField(_)
                | Term::ScopeField(_)
                | Term::Var(_)
                | Term::Wildcard
                | Term::ParamRef(_)
                | Term::BinderRef(_) => {}
            },
            Node::Agg(a) => match &a.kind {
                AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => {
                    push(Node::Condition(body));
                }
                AggExprKind::Call(call) => {
                    for arg in &call.args {
                        match arg {
                            CallArg::Condition(c) => push(Node::Condition(c)),
                            CallArg::Term(t) => push(Node::Term(t)),
                            CallArg::Within(_) => {}
                        }
                    }
                }
            },
        }
    }
    TreeMeasure { depth: max, size }
}

/// Translate a pest grammar `Rule` name into a user-facing description.
/// Cedar's parser uses human-friendly phrasing; this maps Dogwood's pest rule
/// names to comparable descriptions so error messages read naturally.
fn rule_display(rule: &Rule) -> &'static str {
    match rule {
        // Top-level
        Rule::policies => "`permit`, `forbid`, or a macro definition",
        Rule::policy => "policy",
        Rule::def_decl => "macro definition",
        Rule::EOI => "end of input",

        // Effect
        Rule::effect => "'permit' or 'forbid'",
        Rule::kw_permit => "'permit'",
        Rule::kw_forbid => "'forbid'",

        // Scope
        Rule::scope => "scope",
        Rule::variable_def => "scope variable",
        Rule::kw_principal => "'principal'",
        Rule::kw_action => "'action'",
        Rule::kw_resource => "'resource'",

        // Conditions
        Rule::cond => "condition clause",
        Rule::cond_kw => "'when' or 'unless'",
        Rule::kw_when => "'when'",
        Rule::kw_unless => "'unless'",
        Rule::extension_marker => "temporal block",
        Rule::dialect_tag => "`temporal`",
        Rule::guardrails_tag => "`{`",
        Rule::block_inner => "block body",

        // Expressions
        Rule::expr => "expression",
        Rule::if_expr => "'if' expression",
        Rule::or => "expression",
        Rule::and => "expression",
        Rule::rel => "expression",
        Rule::add => "expression",
        Rule::mult => "expression",
        Rule::unary => "expression",
        Rule::member => "expression",
        Rule::primary => "expression",
        Rule::paren_expr => "'('",
        Rule::list => "'['",
        Rule::record => "'{'",

        // Operators
        Rule::rel_op => "comparison operator",
        Rule::rel_op_tail => "comparison",
        Rule::add_op => "'+' or '-'",
        Rule::mult_op => "'*'",
        Rule::bang_run => "'!'",
        Rule::dash_run => "'-'",
        Rule::bang => "'!'",
        Rule::dash => "'-'",

        // Keywords in expressions
        Rule::kw_if => "'if'",
        Rule::kw_then => "'then'",
        Rule::kw_else => "'else'",
        Rule::kw_in => "'in'",
        Rule::kw_has => "'has'",
        Rule::kw_like => "'like'",
        Rule::kw_is => "'is'",
        Rule::kw_true => "'true'",
        Rule::kw_false => "'false'",
        Rule::kw_context => "'context'",

        // Has / like / is tails
        Rule::has_tail => "'has'",
        Rule::has_rhs => "attribute name",
        Rule::has_if_rhs => "attribute name",
        Rule::like_tail => "'like'",
        Rule::is_tail => "'is'",

        // Member access
        Rule::mem_access => "'.', '(', or '['",
        Rule::access_field => "'.'",
        Rule::access_call => "'('",
        Rule::access_index => "'['",

        // Names, refs, identifiers
        Rule::name => "name",
        Rule::ref_ => "entity reference",
        Rule::ref_record => "entity record",
        Rule::ref_init => "entity record field",
        Rule::ident => "identifier",
        Rule::bare_ident => "identifier",
        Rule::common_ident => "identifier",
        Rule::special_ident => "identifier",
        Rule::any_ident => "identifier",

        // Literals
        Rule::literal => "literal",
        Rule::number => "number",
        Rule::string => "string literal",

        // Slots
        Rule::slot => "template slot",
        Rule::slot_principal => "'?principal'",
        Rule::slot_resource => "'?resource'",
        Rule::slot_other => "template slot",

        // Records / sets elements
        Rule::rec_init => "record entry",
        Rule::rec_init_if => "'if' record key",
        Rule::rec_init_expr => "record entry",

        // Annotations
        Rule::annotation => "annotation",

        // Macros
        Rule::def_kind => "'cedar' or 'temporal'",
        Rule::kw_def => "'def'",
        Rule::kw_def_cedar => "'cedar'",
        Rule::kw_def_temporal => "'temporal'",
        Rule::param_list => "parameter list",
        Rule::param => "parameter",

        // Implicit / whitespace (should not appear in errors)
        Rule::WHITESPACE => "whitespace",
        Rule::COMMENT => "comment",
        Rule::ident_start => "identifier",
        Rule::ident_cont => "identifier",
        Rule::policy_entry => "policy",
        Rule::expr_entry => "expression",
    }
}

/// Format a pest `Error<Rule>` into a Cedar-style error message.
///
/// Cedar's parser typically produces messages like:
///   - `unexpected token 'X'` — when the parser found something unexpected
///   - `unexpected end of input` — at EOF
///   - `invalid policy effect: X` — for semantic checks
///
/// This function translates pest's raw `ErrorVariant` (which lists expected
/// grammar rule names) into comparable human-readable messages, preferring the
/// "unexpected token" style when we can identify what the parser found.
fn format_pest_error(e: &pest::error::Error<Rule>, src: &str) -> String {
    match &e.variant {
        pest::error::ErrorVariant::CustomError { message } => message.clone(),
        pest::error::ErrorVariant::ParsingError {
            positives,
            negatives,
        } => {
            // Determine what was found at the error position.
            let at_pos = match e.location {
                pest::error::InputLocation::Pos(p) => p,
                pest::error::InputLocation::Span((s, _)) => s,
            };
            let found_token = extract_token(src, at_pos);

            // ── Missing-paren heuristic ──────────────────────────────────
            // When pest backtracks to the top level after failing inside a
            // policy or macro, we lose context. Detect common "missing `(`"
            // patterns by looking at the error position and what follows.
            if let Some(ref token) = found_token {
                if (token == "permit" || token == "forbid")
                    && positives.iter().any(|r| matches!(r, Rule::policies))
                {
                    // pest failed the `policy` branch and is reporting at the
                    // `permit`/`forbid` token. Check what follows it.
                    let after_token = src[at_pos + token.len()..].trim_start();
                    if !after_token.starts_with('(') {
                        let next = extract_token(src, src.len() - after_token.len());
                        let next_str = next.as_deref().unwrap_or("end of input");
                        return format!(
                            "expected `(` after `{token}` to begin the scope, found `{next_str}`"
                        );
                    }
                }
                if token == "def" && positives.iter().any(|r| matches!(r, Rule::policies)) {
                    // pest failed the `def_decl` branch. Scan forward to find
                    // where `(` was expected: after `def <kind> <name>`.
                    let rest = src[at_pos..].trim_start();
                    let words: Vec<&str> = rest
                        .splitn(4, |c: char| c.is_whitespace() || c == '(' || c == ')')
                        .filter(|s| !s.is_empty())
                        .collect();
                    // Pattern: def <kind> <name> — next non-whitespace should be `(`
                    if words.len() >= 3
                        && words[0] == "def"
                        && (words[1] == "cedar" || words[1] == "temporal")
                    {
                        let name = words[2];
                        // Find position after the macro name
                        if let Some(name_pos) = rest.find(name) {
                            let after_name = rest[name_pos + name.len()..].trim_start();
                            if !after_name.starts_with('(') {
                                let found_char = after_name
                                    .chars()
                                    .next()
                                    .map(|c| c.to_string())
                                    .unwrap_or_else(|| "end of input".to_string());
                                return format!(
                                    "expected `(` after macro name `{name}`, found `{found_char}`"
                                );
                            }
                        }
                    }
                }
            }

            // ── Missing semicolon / condition at EOF ─────────────────────
            // If we're at EOF and the source ends with `)`, the user likely
            // forgot `;` or a condition clause after the scope.
            if found_token.is_none() {
                let trimmed = src[..at_pos].trim_end();
                if trimmed.ends_with(')') {
                    return "unexpected end of input; expected `;` to end the policy, \
                            or `when`/`unless` to add a condition"
                        .to_string();
                }
            }

            // ── Missing `when`/`unless` before `{` ───────────────────────
            // If `{` appears right after `)`, the user forgot the condition
            // keyword.
            if let Some(ref token) = found_token {
                if token == "{" {
                    let before = src[..at_pos].trim_end();
                    if before.ends_with(')') {
                        return "expected `when` or `unless` before `{`; \
                                condition bodies must be preceded by a keyword"
                            .to_string();
                    }
                }
            }

            // ── Standard formatting ──────────────────────────────────────
            // If we have negatives (tokens that should NOT have appeared),
            // use them. Otherwise format based on what was expected.
            if !negatives.is_empty() {
                // pest reports negatives when a specific token was found that
                // shouldn't be there. Format as "unexpected token `X`".
                let neg_names: Vec<&str> = negatives.iter().map(|r| rule_display(r)).collect();
                if let Some(token) = &found_token {
                    format!("unexpected token `{token}`")
                } else {
                    format!("unexpected {}", neg_names.join(", "))
                }
            } else if positives.is_empty() {
                // Neither positives nor negatives — shouldn't happen, but
                // fall back to something reasonable.
                if let Some(token) = &found_token {
                    format!("unexpected token `{token}`")
                } else {
                    "unexpected end of input".to_string()
                }
            } else {
                // Only positives: format as "unexpected token `X`" when we
                // can identify what was found (Cedar style), with a hint
                // about what was expected.
                let descriptions = deduplicate_descriptions(positives);
                if let Some(token) = &found_token {
                    if descriptions.len() <= 3 {
                        format!(
                            "unexpected token `{token}`, expected {}",
                            descriptions.join(", ")
                        )
                    } else {
                        format!("unexpected token `{token}`")
                    }
                } else {
                    // At EOF
                    if descriptions.len() <= 3 {
                        format!(
                            "unexpected end of input, expected {}",
                            descriptions.join(", ")
                        )
                    } else {
                        "unexpected end of input".to_string()
                    }
                }
            }
        }
    }
}

/// Deduplicate rule descriptions (many rules map to the same display string,
/// e.g. multiple expression-level rules all display as "expression").
fn deduplicate_descriptions(rules: &[Rule]) -> Vec<&'static str> {
    // A `bang` or `dash` is only ever expected as one more `!` or `-` in a
    // run, which says nothing about what is missing.
    let informative: Vec<&Rule> = rules
        .iter()
        .filter(|r| !matches!(r, Rule::bang | Rule::dash))
        .collect();
    let rules: Vec<&Rule> = if informative.is_empty() {
        rules.iter().collect()
    } else {
        informative
    };
    let mut descs: Vec<&str> = rules.into_iter().map(rule_display).collect();
    descs.sort_unstable();
    descs.dedup();
    descs
}

/// Extract the token at `pos` in `src` for error messages. Returns `None` at
/// EOF. Attempts to grab a meaningful token (identifier, keyword, number,
/// string start, or single punctuation character).
fn extract_token(src: &str, pos: usize) -> Option<String> {
    let remaining = src.get(pos..)?;
    if remaining.is_empty() {
        return None;
    }

    let first = remaining.chars().next()?;

    // Identifier / keyword: grab the whole word.
    if first.is_ascii_alphabetic() || first == '_' {
        let end = remaining
            .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .unwrap_or(remaining.len());
        return Some(remaining[..end].to_string());
    }

    // Template slot: `?principal`, `?resource`, or `?ident`.
    if first == '?' {
        let rest = &remaining[1..];
        let end = rest
            .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .unwrap_or(rest.len());
        return Some(remaining[..1 + end].to_string());
    }

    // Number: grab consecutive digits.
    if first.is_ascii_digit() {
        let end = remaining
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(remaining.len());
        return Some(remaining[..end].to_string());
    }

    // String literal: show the opening quote + a prefix.
    if first == '"' {
        let close = remaining[1..].find('"').map(|i| i + 2);
        let end = close.unwrap_or_else(|| {
            // Unclosed string: truncate at ~20 bytes on a char boundary.
            remaining
                .char_indices()
                .take_while(|(i, _)| *i <= 20)
                .last()
                .map(|(i, c)| i + c.len_utf8())
                .unwrap_or(remaining.len())
                .min(remaining.len())
        });
        return Some(remaining[..end].to_string());
    }

    // Multi-character operators: `::`, `==`, `!=`, `<=`, `>=`, `||`, `&&`.
    // All targets are 2 ASCII bytes, so a failing boundary check means no
    // match is possible (the first char is multi-byte).
    if remaining.len() >= 2 && remaining.is_char_boundary(2) {
        let two = &remaining[..2];
        if matches!(two, "::" | "==" | "!=" | "<=" | ">=" | "||" | "&&") {
            return Some(two.to_string());
        }
    }

    // Single character.
    Some(first.to_string())
}

/// Parse a `.dw` policy set into its policies and macro definitions.
///
/// Returns all policies on success, or the collected parse errors.
///
/// [`parse_policies_with`] at the default [`ParseOptions`].
#[cfg(test)]
pub fn parse_policies(src: &str) -> Result<PolicySet, Vec<RawParseError>> {
    parse_policies_with(src, &ParseOptions::default())
}

/// [`parse_policies`] under `options`.
///
/// Every depth is bounded by `options.max_depth`, by default
/// [`dogwood_syntax::DEFAULT_MAX_DEPTH`], 32: source nesting deeper than the
/// limit and an expression tree deeper than the limit, temporal blocks
/// included, are each a parse error. Nesting counts each open bracket and
/// each keyword that introduces an operand (`if`; in a temporal block,
/// `exists`, `where`, `formerly`, `previous`, `since`, `count`, `sum`, and
/// `for`); only a closing bracket subtracts, so sibling keywords in one
/// bracket level accumulate. Real policies measure at most 9 levels of
/// nesting and 16 of expression depth. At the default limit, parsing, macro
/// expansion, and lowering fit a 2 MiB thread stack in a debug build, which
/// a test enforces, so too-deep text is a parse error, never a stack
/// overflow; a caller who raises the limit owns the stack the deeper trees
/// need.
pub fn parse_policies_with(
    src: &str,
    options: &ParseOptions,
) -> Result<PolicySet, Vec<RawParseError>> {
    let limit = options.max_depth;
    // Strip a leading UTF-8 BOM (U+FEFF) if present — editors and Windows
    // tools sometimes prepend it, and the grammar doesn't expect it.
    let (_, src) = dogwood_syntax::split_bom(src);
    // Shared `.dw` source for scope entity-UID `Loc`s (so a scope error
    // points at the offending token, not the whole rule).
    let dw_src: std::sync::Arc<str> = std::sync::Arc::from(src);
    let mut pairs = match dogwood_syntax::parse_with(Rule::policies, src, options) {
        Ok(p) => p,
        Err(e) => {
            // Convert the pest syntax error into a single RawParseError
            // with a best-effort span.
            let (start, end) = match e.location {
                pest::error::InputLocation::Pos(p) => (p, (p + 1).min(src.len().max(p + 1))),
                pest::error::InputLocation::Span((s, e)) => (s, e),
            };
            return Err(vec![err(format_pest_error(&e, src), Span::new(start, end))]);
        }
    };

    // `policies` is the single top-level pair.
    let policies_pair = pairs.next().expect("policies rule always yields one pair");

    let mut policies = Vec::new();
    let mut defs = Vec::new();
    let mut errors = Vec::new();

    for pair in policies_pair.into_inner() {
        match pair.as_rule() {
            Rule::policy => match build_policy(pair, &dw_src, limit) {
                Ok(p) => policies.push(p),
                Err(e) => errors.push(e),
            },
            Rule::def_decl => match build_def_decl(pair, limit) {
                Ok(d) => defs.push(d),
                Err(e) => errors.push(e),
            },
            Rule::EOI => {}
            _ => {}
        }
    }

    if errors.is_empty() {
        Ok(PolicySet { policies, defs })
    } else {
        Err(errors)
    }
}

/// The recursion of the generated policy parser over `source`: the maximum,
/// over every root-to-leaf path of its pair tree, of the pairs on the path
/// that re-enter the expression language. A test helper, for checking that
/// [`dogwood_syntax::nesting_estimate`] over-approximates it; parsed with no
/// depth limit.
///
/// The counted rules, read from `grammar.pest`:
///
/// - `expr`, the only rule that appears nested inside itself. Every nested
///   `expr` is entered through a bracket the scan counts (`paren_expr`,
///   `list`, `record`'s `rec_init`, `access_call`, `access_index`, a scope's
///   `variable_def` inside the head's parentheses, a condition's braces) or
///   through an `if` (`if_expr`, `rec_init_if`). `add`, `member`, and
///   `primary` re-enter themselves only through `expr`.
/// - `extension_marker`, one level for the block it opens, as the builder
///   counts it. Its body is the temporal grammar's, a separate parse that
///   [`temporal_reentries`](crate::temporal_reentries) measures.
/// - A `def cedar` body, parsed separately with `expr_entry`, under its
///   definition's braces as the builder parses it; its root `expr` counts.
///
/// `block_inner` recurses on nested braces, but it is atomic and has no inner
/// pairs to count; the scan counts its braces regardless.
#[doc(hidden)]
pub fn policy_reentries(source: &str) -> Result<usize, String> {
    let unlimited = ParseOptions::default().max_depth(usize::MAX);
    let (_, source) = dogwood_syntax::split_bom(source);
    let pairs = dogwood_syntax::parse_with(Rule::policies, source, &unlimited)
        .map_err(|e| e.to_string())?;
    let mut deepest = 0;
    let mut stack: Vec<(Pair<'_>, usize)> = pairs.map(|pair| (pair, 0)).collect();
    while let Some((pair, above)) = stack.pop() {
        let rule = pair.as_rule();
        let here = above + usize::from(matches!(rule, Rule::expr | Rule::extension_marker));
        deepest = deepest.max(here);
        if rule == Rule::def_decl {
            let cedar = pair.clone().into_inner().any(|child| {
                child.as_rule() == Rule::def_kind
                    && child
                        .clone()
                        .into_inner()
                        .any(|kind| kind.as_rule() == Rule::kw_def_cedar)
            });
            let body = pair
                .clone()
                .into_inner()
                .find(|child| child.as_rule() == Rule::block_inner);
            if let (true, Some(body)) = (cedar, body) {
                let body = dogwood_syntax::parse_with(Rule::expr_entry, body.as_str(), &unlimited)
                    .map_err(|e| e.to_string())?;
                stack.extend(body.map(|pair| (pair, here)));
            }
        }
        stack.extend(pair.into_inner().map(|child| (child, here)));
    }
    Ok(deepest)
}

/// `def_decl = "def" def_kind ident "(" param_list? ")" "{" body "}" ";"`.
fn build_def_decl(pair: Pair<'_>, limit: usize) -> Result<MacroDef, RawParseError> {
    let span = span_of(&pair);
    let mut kind: Option<DefKind> = None;
    let mut name = String::new();
    let mut params: Vec<MacroParam> = Vec::new();
    let mut body_text: Option<(String, Span)> = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::def_kind => {
                let tok = child
                    .into_inner()
                    .next()
                    .expect("def_kind has a keyword child");
                kind = Some(match tok.as_rule() {
                    Rule::kw_def_cedar => DefKind::Cedar,
                    Rule::kw_def_temporal => DefKind::Temporal,
                    other => unreachable!("unexpected def_kind child: {other:?}"),
                });
            }
            Rule::ident => name = child.as_str().to_string(),
            Rule::param_list => {
                for p in child.into_inner().filter(|p| p.as_rule() == Rule::param) {
                    let param_span = span_of(&p);
                    // `param = ${ "?" ~ ident }` — inner ident captures
                    // the name without the leading `?`.
                    let pname = p
                        .into_inner()
                        .find(|c| c.as_rule() == Rule::ident)
                        .map(|c| c.as_str().to_string())
                        .ok_or_else(|| err("macro parameter missing a name", param_span))?;
                    params.push(MacroParam {
                        span: param_span,
                        name: pname,
                    });
                }
            }
            Rule::block_inner => {
                body_text = Some((child.as_str().to_string(), span_of(&child)));
            }
            _ => {}
        }
    }
    let kind = kind.ok_or_else(|| err("macro definition missing a kind", span))?;
    let (body_src, body_span) =
        body_text.ok_or_else(|| err("macro definition missing a body", span))?;
    let body = match kind {
        DefKind::Cedar => {
            let expr = parse_cedar_macro_body(&body_src, body_span, limit)?;
            MacroBody::Cedar(expr)
        }
        DefKind::Temporal => temporal::parse_macro_body(&body_src, limit)
            .map_err(|e| err(format!("in `def temporal` body: {e}"), body_span))?,
    };
    Ok(MacroDef {
        span,
        name,
        params,
        body,
    })
}

#[derive(Debug, Clone, Copy)]
enum DefKind {
    Cedar,
    Temporal,
}

/// Parse a `def cedar` body as a cedar expression. The body lives between
/// the macro definition's `{` and `}` — we run the standard `expr_entry`
/// rule and rebase any error span back into the original source.
fn parse_cedar_macro_body(src: &str, body_span: Span, limit: usize) -> Result<Expr, RawParseError> {
    let options = ParseOptions::default().max_depth(limit);
    let mut pairs = dogwood_syntax::parse_with(Rule::expr_entry, src, &options).map_err(|e| {
        let (start, end) = match e.location {
            pest::error::InputLocation::Pos(p) => (p, (p + 1).min(src.len().max(p + 1))),
            pest::error::InputLocation::Span((s, e)) => (s, e),
        };
        err(
            format!("in `def cedar` body: {}", format_pest_error(&e, src)),
            Span::new(body_span.start + start, body_span.start + end),
        )
    })?;
    let entry = pairs.next().expect("expr_entry yields one pair");
    let expr_pair = entry
        .into_inner()
        .find(|p| p.as_rule() == Rule::expr)
        .ok_or_else(|| err("empty `def cedar` body", body_span))?;
    // `src` is the body alone, so an error's span is relative to the body;
    // rebase it into the file, as the pest error above is.
    build_root(expr_pair, limit).map_err(|e| RawParseError {
        message: e.message,
        span: Span::new(body_span.start + e.span.start, body_span.start + e.span.end),
    })
}

fn build_policy(
    pair: Pair<'_>,
    dw_src: &std::sync::Arc<str>,
    limit: usize,
) -> Result<Policy, RawParseError> {
    let span = span_of(&pair);
    let mut annotations = Vec::new();
    let mut effect: Option<Effect> = None;
    let mut scope: Option<Scope> = None;
    let mut conditions = Vec::new();

    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::annotation => annotations.push(build_annotation(child)?),
            Rule::effect => {
                let text = child.as_str();
                effect = Some(match text {
                    "permit" => Effect::Permit,
                    "forbid" => Effect::Forbid,
                    other => {
                        return Err(err(
                            format!("policy effect must be `permit` or `forbid`, found `{other}`"),
                            span_of(&child),
                        ));
                    }
                });
            }
            Rule::scope => {
                scope = Some(build_scope(child, dw_src, limit)?);
            }
            Rule::cond => conditions.push(build_cond(child, limit)?),
            _ => {}
        }
    }

    Ok(Policy {
        span,
        annotations,
        effect: effect.ok_or_else(|| err("policy is missing an effect", span))?,
        scope: scope.ok_or_else(|| err("policy is missing a scope", span))?,
        conditions,
    })
}

fn build_annotation(pair: Pair<'_>) -> Result<Annotation, RawParseError> {
    let mut key = String::new();
    let mut value = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::any_ident => key = child.as_str().to_string(),
            Rule::string => {
                // Decode the value with Cedar's escaper — the same `decode_string`
                // every other string literal uses — so an annotation means the
                // same thing in Dogwood as in Cedar (`@a("x\"y")` is `x"y`, not
                // the verbatim `x\"y`; an invalid escape is a parse error). This
                // was `trim_matches('"')` with no decode, which diverged from
                // Cedar and mis-stored any escape-bearing value.
                value = Some(decode_string(child.as_str(), span_of(&child))?);
            }
            _ => {}
        }
    }
    Ok(Annotation { key, value })
}

// =========================================================================
// build_scope — the policy head → loc-bearing `cedar_ast` scope constraints
// =========================================================================

/// The parsed tail of a `variable_def`, role-neutral; mapped to the
/// role-specific `cedar_ast` constraint by [`build_scope`].
enum ScopeTail {
    /// No constraint (`principal` / `action` / `resource` bare).
    Any,
    /// `== operand` (`is_in == false`) or `in operand` (`is_in == true`).
    Op { is_in: bool, operand: Expr },
    /// `is Type` with an optional `in operand`.
    Is {
        ty: cedar_ast::EntityType,
        in_op: Option<Expr>,
    },
}

/// Build a structured [`Scope`] from the `scope` rule
/// (`variable_def { "," variable_def }`). Each `variable_def` is keyed by
/// its leading variable name (`principal` / `action` / `resource`).
///
/// `dw_src` is the shared `.dw` source, used to stamp each scope entity
/// UID's `Loc` so scope-error diagnostics point at the token.
fn build_scope(
    pair: Pair<'_>,
    dw_src: &std::sync::Arc<str>,
    limit: usize,
) -> Result<Scope, RawParseError> {
    let span = span_of(&pair);
    let mut principal = PrincipalConstraint::any();
    let mut action = ActionConstraint::any();
    let mut resource = ResourceConstraint::any();
    let mut seen_principal = false;
    let mut seen_action = false;
    let mut seen_resource = false;

    for vd in pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::variable_def)
    {
        let vd_span = span_of(&vd);
        let (role, tail) = build_variable_def(vd, limit)?;
        match role.as_str() {
            "principal" => {
                if seen_principal {
                    return Err(err("duplicate `principal` in scope", vd_span));
                }
                seen_principal = true;
                principal = principal_constraint(tail, vd_span, dw_src)?;
            }
            "resource" => {
                if seen_resource {
                    return Err(err("duplicate `resource` in scope", vd_span));
                }
                seen_resource = true;
                resource = resource_constraint(tail, vd_span, dw_src)?;
            }
            "action" => {
                if seen_action {
                    return Err(err("duplicate `action` in scope", vd_span));
                }
                seen_action = true;
                action = action_constraint(tail, vd_span, dw_src)?;
            }
            other => {
                let msg = if seen_principal && seen_action && seen_resource {
                    format!("this policy has an extra element in the scope: `{other}`")
                } else {
                    format!(
                        "unexpected scope variable `{other}`; expected \
                         `principal`, `action`, or `resource`"
                    )
                };
                return Err(err(msg, vd_span));
            }
        }
    }

    Ok(Scope {
        span,
        principal,
        action,
        resource,
    })
}

/// Parse one `variable_def` into its role name and role-neutral tail.
fn build_variable_def(pair: Pair<'_>, limit: usize) -> Result<(String, ScopeTail), RawParseError> {
    let span = span_of(&pair);
    let mut children = pair.into_inner().peekable();

    let role = children
        .next()
        .filter(|p| p.as_rule() == Rule::any_ident)
        .map(|p| p.as_str().to_string())
        .ok_or_else(|| err("scope variable is missing its name", span))?;

    let mut is_type: Option<cedar_ast::EntityType> = None;
    let mut op: Option<(String, Expr)> = None;

    while let Some(child) = children.next() {
        match child.as_rule() {
            // Legacy `principal : User` colon form — direct the author to `is`.
            Rule::name => {
                return Err(err(
                    "the `principal : Type` scope form is not supported; \
                     use `principal is Type`",
                    span_of(&child),
                ));
            }
            Rule::kw_is => {
                let add = children
                    .next()
                    .filter(|p| p.as_rule() == Rule::add)
                    .ok_or_else(|| err("`is` is missing an entity type", span))?;
                is_type = Some(extract_entity_type(add, span)?);
            }
            Rule::rel_op => {
                let op_str = child.as_str().trim().to_string();
                let expr = children
                    .next()
                    .filter(|p| p.as_rule() == Rule::expr)
                    .ok_or_else(|| err("scope operator is missing its operand", span))?;
                let _guard = ScopeContextGuard::enter();
                let result = build_root(expr, limit);
                drop(_guard);
                op = Some((op_str, result?));
            }
            _ => {}
        }
    }

    let tail = match (is_type, op) {
        (Some(ty), None) => ScopeTail::Is { ty, in_op: None },
        (Some(ty), Some((op_str, operand))) if op_str == "in" => ScopeTail::Is {
            ty,
            in_op: Some(operand),
        },
        (Some(_), Some((op_str, _))) => {
            return Err(err(
                format!("`is Type {op_str} ...` is not valid; only `is Type in ...` is allowed"),
                span,
            ));
        }
        (None, Some((op_str, operand))) => match op_str.as_str() {
            "==" => ScopeTail::Op {
                is_in: false,
                operand,
            },
            "in" => ScopeTail::Op {
                is_in: true,
                operand,
            },
            "=" => {
                return Err(err(
                    "`=` is not a valid operator in this scope; did you mean `==`?",
                    span,
                ));
            }
            other => {
                return Err(err(
                    format!("scope only allows `==` or `in`, found `{other}`"),
                    span,
                ));
            }
        },
        (None, None) => ScopeTail::Any,
    };

    Ok((role, tail))
}

/// Map a parsed tail to a `PrincipalConstraint`.
fn principal_constraint(
    tail: ScopeTail,
    span: Span,
    src: &std::sync::Arc<str>,
) -> Result<PrincipalConstraint, RawParseError> {
    Ok(match tail {
        ScopeTail::Any => PrincipalConstraint::any(),
        ScopeTail::Op {
            is_in: false,
            operand,
        } => PrincipalConstraint::new(cedar_ast::PrincipalOrResourceConstraint::Eq(
            expr_to_entity_ref(&operand, span, src, "principal")?,
        )),
        ScopeTail::Op {
            is_in: true,
            operand,
        } => PrincipalConstraint::new(cedar_ast::PrincipalOrResourceConstraint::In(
            expr_to_entity_ref(&operand, span, src, "principal")?,
        )),
        ScopeTail::Is { ty, in_op: None } => {
            PrincipalConstraint::is_entity_type(std::sync::Arc::new(ty))
        }
        ScopeTail::Is {
            ty,
            in_op: Some(op),
        } => PrincipalConstraint::new(cedar_ast::PrincipalOrResourceConstraint::IsIn(
            std::sync::Arc::new(ty),
            expr_to_entity_ref(&op, span, src, "principal")?,
        )),
    })
}

/// Map a parsed tail to a `ResourceConstraint` (same shape as principal).
fn resource_constraint(
    tail: ScopeTail,
    span: Span,
    src: &std::sync::Arc<str>,
) -> Result<ResourceConstraint, RawParseError> {
    Ok(match tail {
        ScopeTail::Any => ResourceConstraint::any(),
        ScopeTail::Op {
            is_in: false,
            operand,
        } => ResourceConstraint::new(cedar_ast::PrincipalOrResourceConstraint::Eq(
            expr_to_entity_ref(&operand, span, src, "resource")?,
        )),
        ScopeTail::Op {
            is_in: true,
            operand,
        } => ResourceConstraint::new(cedar_ast::PrincipalOrResourceConstraint::In(
            expr_to_entity_ref(&operand, span, src, "resource")?,
        )),
        ScopeTail::Is { ty, in_op: None } => {
            ResourceConstraint::is_entity_type(std::sync::Arc::new(ty))
        }
        ScopeTail::Is {
            ty,
            in_op: Some(op),
        } => ResourceConstraint::new(cedar_ast::PrincipalOrResourceConstraint::IsIn(
            std::sync::Arc::new(ty),
            expr_to_entity_ref(&op, span, src, "resource")?,
        )),
    })
}

/// Map a parsed tail to an `ActionConstraint`. Actions cannot use `is`,
/// cannot carry slots, and may compare against a *list* (`action in [...]`).
fn action_constraint(
    tail: ScopeTail,
    span: Span,
    src: &std::sync::Arc<str>,
) -> Result<ActionConstraint, RawParseError> {
    Ok(match tail {
        ScopeTail::Any => ActionConstraint::any(),
        ScopeTail::Op {
            is_in: false,
            operand,
        } => ActionConstraint::Eq(expr_to_action_uid(&operand, span, src)?),
        ScopeTail::Op {
            is_in: true,
            operand,
        } => ActionConstraint::In(expr_to_action_uid_list(&operand, span, src)?),
        ScopeTail::Is { .. } => {
            return Err(err(
                "`action is Type` is not valid in the action scope",
                span,
            ));
        }
    })
}

/// Clone `uid`, re-stamping its `Loc` to point at `token_span` in the `.dw`
/// source `src`. The scope operand's euid was built by `build_ref` with no
/// loc; here we attach the token's `.dw` span so Cedar's RBAC validator can
/// report scope errors against it.
fn euid_with_loc(
    uid: &cedar_ast::EntityUID,
    token_span: Span,
    src: &std::sync::Arc<str>,
) -> cedar_ast::EntityUID {
    let loc = Loc::new(token_span.start..token_span.end, std::sync::Arc::clone(src));
    cedar_ast::EntityUID::from_components(uid.entity_type().clone(), uid.eid().clone(), Some(loc))
}

/// An entity reference or template slot (for principal/resource scopes),
/// with the entity UID's `Loc` set to the operand's `.dw` token span.
fn expr_to_entity_ref(
    expr: &Expr,
    span: Span,
    src: &std::sync::Arc<str>,
    scope_var: &str,
) -> Result<EntityReference, RawParseError> {
    match &expr.kind {
        ExprKind::Lit(cedar_ast::Literal::EntityUID(uid)) => Ok(EntityReference::euid(
            std::sync::Arc::new(euid_with_loc(uid, expr.span, src)),
        )),
        ExprKind::Slot(_) => {
            let loc = Loc::new(expr.span.start..expr.span.end, std::sync::Arc::clone(src));
            Ok(EntityReference::Slot(Some(loc)))
        }
        ExprKind::ParamRef { name } => Err(err(
            format!(
                "`?{name}` is not a recognized template slot; \
                 did you mean `?{scope_var}`?"
            ),
            span,
        )),
        _ => Err(err(
            format!(
                "expected an entity reference (`Ns::Type::\"id\"`) or \
                 a template slot (`?{scope_var}`)"
            ),
            span,
        )),
    }
}

/// A bare action entity reference (for action scopes — no slots allowed),
/// with its `Loc` set to the operand's `.dw` token span.
fn expr_to_action_uid(
    expr: &Expr,
    span: Span,
    src: &std::sync::Arc<str>,
) -> Result<std::sync::Arc<cedar_ast::EntityUID>, RawParseError> {
    match &expr.kind {
        ExprKind::Lit(cedar_ast::Literal::EntityUID(uid)) => {
            Ok(std::sync::Arc::new(euid_with_loc(uid, expr.span, src)))
        }
        _ => Err(err(
            "action scope expects an action reference (`Ns::Action::\"id\"`)",
            span,
        )),
    }
}

/// One or a list of action references (`action in [A::"a", A::"b"]`).
fn expr_to_action_uid_list(
    expr: &Expr,
    span: Span,
    src: &std::sync::Arc<str>,
) -> Result<Vec<std::sync::Arc<cedar_ast::EntityUID>>, RawParseError> {
    match &expr.kind {
        ExprKind::Set(elems) => elems
            .iter()
            .map(|e| expr_to_action_uid(e, span, src))
            .collect(),
        _ => Ok(vec![expr_to_action_uid(expr, span, src)?]),
    }
}

fn build_cond(pair: Pair<'_>, limit: usize) -> Result<Cond, RawParseError> {
    let span = span_of(&pair);
    let mut keyword: Option<CondKeyword> = None;
    let mut body: Option<Expr> = None;

    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::cond_kw => {
                keyword = Some(match child.as_str() {
                    "when" => CondKeyword::When,
                    "unless" => CondKeyword::Unless,
                    other => {
                        return Err(err(
                            format!(
                                "condition keyword must be `when` or `unless`, found `{other}`"
                            ),
                            span_of(&child),
                        ));
                    }
                });
            }
            // The tagged form `when temporal { … }` — the marker sits
            // directly under `cond`; dispatch it to the dialect parser.
            Rule::extension_marker => body = Some(build_root(child, limit)?),
            // The untagged form `when { <expr> }` — a structured Cedar
            // expression (which may itself contain markers as primaries).
            Rule::expr => body = Some(build_root(child, limit)?),
            _ => {}
        }
    }

    let keyword = keyword.ok_or_else(|| err("condition is missing when/unless", span))?;
    let body = body.ok_or_else(|| err("condition is missing a body", span))?;

    Ok(Cond {
        span,
        keyword,
        body,
    })
}

/// Build an [`Expr::Extension`] from an `extension_marker` pair
/// (`temporal { … }`): dispatch the braced body to the temporal
/// sub-parser. (`guardrails { … }` is not an extension marker — it is
/// transparent sugar for a bare Cedar clause, handled in [`build_cond`].)
///
/// The marker is one node, and the temporal tree's root sits one level
/// below it; the root measure counts both.
fn build_extension_marker(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    let span = span_of(&pair);
    let mut dialect: Option<Dialect> = None;
    let mut block: Option<(String, Span)> = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::dialect_tag => dialect = Dialect::from_marker(child.as_str()),
            Rule::block_inner => block = Some((child.as_str().to_string(), span_of(&child))),
            _ => {}
        }
    }
    let (inner, inner_span) =
        block.ok_or_else(|| err("extension marker is missing a body", span))?;
    let extension = match dialect {
        Some(Dialect::Temporal) => {
            crate::extension::temporal::Temporal::parse_at(&inner, inner_span, limit)
                .map(Extension::Temporal)
                .map_err(|msg| err(msg, inner_span))?
        }
        None => return Err(err("unrecognized extension marker", span)),
    };
    Ok(Expr::new(ExprKind::Extension(extension), span))
}

/// The `.dw` span of a fold/chain production (`a && b && c`, `a + b`, …),
/// matching Cedar's attribution: the span of the whole chain pest pair with
/// leading/trailing trivia (whitespace, comments the pair captured) trimmed
/// off. Cedar derives a chain node's location from its CST node boundary,
/// which (a) includes a parenthesized operand's parens and (b) covers the
/// whole chain — and it stamps **every** folded node in the chain with that
/// same span (its `and_naryl` behavior). So all binary nodes a fold loop
/// produces for one chain share this span.
fn chain_span(pair: &Pair<'_>) -> Span {
    let sp = pair.as_span();
    let (start, text) = (sp.start(), sp.as_str());
    // Trim trailing trivia: the `and`/`or`/`add`/… pest rules can capture
    // trailing whitespace before the next token. Cedar ends at the last
    // significant byte of the chain.
    let trimmed = text.trim_end();
    Span::new(start, start + trimmed.len())
}

// =========================================================================
// build_expr — the Cedar expression-precedence tower → ast::Expr
// =========================================================================
//
// Walks `expr → or → and → rel → add → mult → unary → member → primary`.
// The recursive spine becomes the surface `ast::Expr`; operators use
// Dogwood's own `BinOp` / `UnOp`, while value-leaf payloads (literals, vars,
// entity types, patterns) reuse `cedar_policy_core::ast` types directly.
// `cedarify::to_ast` later lowers this to loc-bearing Cedar `ast::Expr`.

/// Build an [`Expr`] from an `expr` pair.
///
/// The builders do not count depth: chains fold through loops, and the
/// finished tree is measured once at [`build_root`], which `limit` reaches
/// only for the temporal sub-parse inside an extension marker.
fn build_expr(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    let inner = pair.into_inner().next().expect("expr has one alternative");
    match inner.as_rule() {
        Rule::if_expr => build_if(inner, limit),
        Rule::or => build_or(inner, limit),
        other => unreachable!("unexpected expr child: {other:?}"),
    }
}

/// `if_expr := if expr then expr else expr`.
fn build_if(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    let span = span_of(&pair);
    let mut exprs = pair.into_inner().filter(|p| p.as_rule() == Rule::expr);
    let cond = build_expr(exprs.next().expect("if condition"), limit)?;
    let then_expr = build_expr(exprs.next().expect("then branch"), limit)?;
    let else_expr = build_expr(exprs.next().expect("else branch"), limit)?;
    Ok(Expr::new(
        ExprKind::IfThenElse {
            cond: Box::new(cond),
            then_expr: Box::new(then_expr),
            else_expr: Box::new(else_expr),
        },
        span,
    ))
}

/// `or := and { "||" and }` — left-associative `||`.
fn build_or(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    let span = chain_span(&pair);
    let mut iter = pair.into_inner().filter(|p| p.as_rule() == Rule::and);
    let mut acc = build_and(iter.next().expect("or has an and"), limit)?;
    for next in iter {
        let right = build_and(next, limit)?;
        acc = Expr::new(
            ExprKind::BinaryApp {
                op: BinOp::Or,
                left: Box::new(acc),
                right: Box::new(right),
            },
            span,
        );
    }
    Ok(acc)
}

/// `and := rel { "&&" rel }` — left-associative `&&`.
fn build_and(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    let span = chain_span(&pair);
    let mut iter = pair.into_inner().filter(|p| p.as_rule() == Rule::rel);
    let mut acc = build_rel(iter.next().expect("and has a rel"), limit)?;
    for next in iter {
        let right = build_rel(next, limit)?;
        acc = Expr::new(
            ExprKind::BinaryApp {
                op: BinOp::And,
                left: Box::new(acc),
                right: Box::new(right),
            },
            span,
        );
    }
    Ok(acc)
}

/// `rel := add ( rel_op_tail | has_tail | like_tail | is_tail )?`.
fn build_rel(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    let span = span_of(&pair);
    let rel_chain_span = chain_span(&pair);
    let mut iter = pair.into_inner();
    let add = iter.next().expect("rel has an add");
    let Some(tail) = iter.next() else {
        return build_add(add, limit);
    };
    let lhs = build_add(add, limit)?;
    match tail.as_rule() {
        Rule::rel_op_tail => build_rel_op_tail(lhs, tail, rel_chain_span, limit),
        Rule::has_tail => Ok(Expr::new(
            ExprKind::HasAttr {
                expr: Box::new(lhs),
                attrs: extract_has_path(tail)?,
            },
            span,
        )),
        Rule::like_tail => {
            let add = tail
                .into_inner()
                .find(|p| p.as_rule() == Rule::add)
                .expect("like has an add");
            Ok(Expr::new(
                ExprKind::Like {
                    expr: Box::new(lhs),
                    pattern: extract_pattern(add, span)?,
                },
                span,
            ))
        }
        Rule::is_tail => build_is_tail(lhs, tail, span, limit),
        other => unreachable!("unexpected rel tail: {other:?}"),
    }
}

/// `rel_op_tail := (rel_op add)+` — a comparison. `span` is the enclosing
/// `rel` chain span (see [`chain_span`]); Cedar stamps the node with it.
///
/// The grammar accepts a chain `a == b == c`, but Cedar rejects one, as we
/// do: folding it would silently read `(a == b) == c`, which for Bool
/// operands inverts `a == false == false`. A chain must be parenthesized.
fn build_rel_op_tail(
    lhs: Expr,
    pair: Pair<'_>,
    span: Span,
    limit: usize,
) -> Result<Expr, RawParseError> {
    let mut iter = pair.into_inner();
    let op = parse_rel_op(&iter.next().expect("rel_op_tail has a rel_op"))?;
    let right = build_add(
        iter.next().expect("rel_op is followed by an add"),
        limit,
    )?;
    if iter.next().is_some() {
        return Err(err(
            "multiple relational operators (>, ==, in, etc.) must be used with parentheses to make ordering explicit",
            span,
        ));
    }
    Ok(Expr::new(
        ExprKind::BinaryApp {
            op,
            left: Box::new(lhs),
            right: Box::new(right),
        },
        span,
    ))
}

fn parse_rel_op(pair: &Pair<'_>) -> Result<BinOp, RawParseError> {
    Ok(match pair.as_str().trim() {
        "<" => BinOp::Less,
        "<=" => BinOp::LessEq,
        ">" => BinOp::Greater,
        ">=" => BinOp::GreaterEq,
        "==" => BinOp::Eq,
        "!=" => BinOp::NotEq,
        "in" => BinOp::In,
        "=" => {
            return Err(err(
                "`=` is not a valid operator in this scope; did you mean `==`?",
                span_of(pair),
            ));
        }
        other => unreachable!("unexpected rel_op `{other}`"),
    })
}

/// `is_tail := is add ( in add )?`. The first `add` is an entity *type*
/// (not a value expression); the optional second is a value.
fn build_is_tail(
    lhs: Expr,
    pair: Pair<'_>,
    span: Span,
    limit: usize,
) -> Result<Expr, RawParseError> {
    let mut adds = pair.into_inner().filter(|p| p.as_rule() == Rule::add);
    let type_add = adds.next().expect("is has a type operand");
    let entity_type = extract_entity_type(type_add, span)?;
    let in_expr = match adds.next() {
        Some(add) => Some(Box::new(build_add(add, limit)?)),
        None => None,
    };
    Ok(Expr::new(
        ExprKind::Is {
            expr: Box::new(lhs),
            entity_type,
            in_expr,
        },
        span,
    ))
}

/// `add := mult { add_op mult }` — left-associative `+` / `-`.
fn build_add(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    let span = chain_span(&pair);
    let mut iter = pair.into_inner().peekable();
    let mut acc = build_mult(iter.next().expect("add has a mult"), limit)?;
    while let Some(op_pair) = iter.next() {
        debug_assert_eq!(op_pair.as_rule(), Rule::add_op);
        let op = match op_pair.as_str().trim() {
            "+" => BinOp::Add,
            "-" => BinOp::Sub,
            other => unreachable!("unexpected add_op `{other}`"),
        };
        let right = build_mult(iter.next().expect("add_op followed by mult"), limit)?;
        acc = Expr::new(
            ExprKind::BinaryApp {
                op,
                left: Box::new(acc),
                right: Box::new(right),
            },
            span,
        );
    }
    Ok(acc)
}

/// `mult := unary { mult_op unary }`. Cedar supports only `*`; `/` and
/// `%` are rejected (they parse but Cedar has no such operators).
fn build_mult(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    let span = chain_span(&pair);
    let mut iter = pair.into_inner().peekable();
    let mut acc = build_unary(iter.next().expect("mult has a unary"), limit)?;
    while let Some(op_pair) = iter.next() {
        debug_assert_eq!(op_pair.as_rule(), Rule::mult_op);
        let op = match op_pair.as_str().trim() {
            "*" => BinOp::Mul,
            other => {
                return Err(err(
                    format!("`{other}` is not a supported operator"),
                    span_of(&op_pair),
                ));
            }
        };
        let right = build_unary(iter.next().expect("mult_op followed by unary"), limit)?;
        acc = Expr::new(
            ExprKind::BinaryApp {
                op,
                left: Box::new(acc),
                right: Box::new(right),
            },
            span,
        );
    }
    Ok(acc)
}

/// `unary := { "!" }* member | { "-" }* member`.
///
/// As in Cedar, a run of `-` directly before a number token folds its
/// innermost `-` into the literal (`-5` is `Long(-5)`, `--5` is
/// `Neg(Long(-5))`), and every other `!` or `-` is a `Not` or `Neg` node.
fn build_unary(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    // The unary node's span is the whole `unary` production, trivia-trimmed —
    // paren-inclusive on the operand (`!(x)` ends at the `)`), matching Cedar.
    let unary_span = chain_span(&pair);
    let mut prefix: Option<(UnOp, usize)> = None;
    let mut member_pair = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::bang_run => prefix = Some((UnOp::Not, child.into_inner().count())),
            Rule::dash_run => prefix = Some((UnOp::Neg, child.into_inner().count())),
            Rule::member => member_pair = Some(child),
            _ => {}
        }
    }
    let member_pair = member_pair.expect("unary has a member");
    let Some((op, mut count)) = prefix else {
        return build_member(member_pair, limit);
    };

    // Only a *directly* negated number token folds; a parenthesized `-(5)`
    // keeps a `Neg` over the positive literal. 2^63 fits i64 only negated,
    // so build_literal rejects it, as Cedar does; directly negated, it is
    // `Long(i64::MIN)`. The folded literal keeps the number token's span:
    // Cedar spans the digits, not the leading `-`.
    let folded = match bare_number_text(&member_pair) {
        Some(digits) if op == UnOp::Neg => match digits.parse::<u64>() {
            Ok(n) if n <= 1 << 63 => {
                let primary = member_pair.clone().into_inner().next();
                let digits_span = span_of(&primary.expect("member has a primary"));
                Some(Expr::new(
                    ExprKind::Lit(cedar_ast::Literal::Long((n as i64).wrapping_neg())),
                    digits_span,
                ))
            }
            _ => None,
        },
        _ => None,
    };
    if folded.is_some() {
        count -= 1;
    }
    let mut expr = match folded {
        Some(literal) => literal,
        None => build_member(member_pair, limit)?,
    };
    for _ in 0..count {
        expr = Expr::new(
            ExprKind::UnaryApp {
                op,
                expr: Box::new(expr),
            },
            unary_span,
        );
    }
    Ok(expr)
}

/// `member := primary { mem_access }`. Folds attribute access, index
/// access, function calls (`decimal(x)`), and method calls
/// (`xs.contains(y)`) onto the base. Each `mem_access` wraps one of
/// `access_field` / `access_call` / `access_index`.
fn build_member(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    // Cedar attributes every `GetAttr` in an access chain (`x.a.b.c`,
    // `x["k"]`) with the span of the *whole* member expression — not an
    // incremental sub-span — so we match that for span-compatibility with
    // Cedar's own parser (the base primary keeps its own narrow span).
    let member_span = span_of(&pair);
    let mut children = pair.into_inner();
    let primary = children.next().expect("member has a primary");

    // Unwrap each `mem_access` to its inner accessor up front so we can
    // look ahead (a `.field` followed by `(args)` is a method call).
    let accessors: Vec<Pair<'_>> = children
        .filter(|p| p.as_rule() == Rule::mem_access)
        .map(|p| p.into_inner().next().expect("mem_access has a child"))
        .collect();
    let mut iter = accessors.into_iter().peekable();

    // A bare-name primary immediately followed by a call is an extension
    // function application (`decimal("…")`), not a variable. The `member`
    // child is a `primary` wrapper, so look at what it wraps.
    let primary_inner_is_name = primary
        .clone()
        .into_inner()
        .next()
        .is_some_and(|p| p.as_rule() == Rule::name);
    let mut base =
        if primary_inner_is_name && iter.peek().map(|p| p.as_rule()) == Some(Rule::access_call) {
            let name = primary.into_inner().next().expect("primary wraps a name");
            let call = iter.next().expect("peeked call");
            build_function_call(&name, call, limit)?
        } else {
            build_primary(primary, limit)?
        };

    while let Some(acc) = iter.next() {
        match acc.as_rule() {
            Rule::access_field => {
                let field = field_name(&acc);
                // `.method(args)` when a call follows the field access.
                if iter.peek().map(|p| p.as_rule()) == Some(Rule::access_call) {
                    let call = iter.next().expect("peeked call");
                    base = build_method_call(base, &field, call, member_span.start, limit)?;
                } else {
                    base = Expr::new(
                        ExprKind::GetAttr {
                            expr: Box::new(base),
                            attr: field,
                        },
                        member_span,
                    );
                }
            }
            Rule::access_index => {
                // Cedar index access uses a string-literal key
                // (`a["k"]`), equivalent to `a.k`.
                let key = index_key(&acc)?;
                base = Expr::new(
                    ExprKind::GetAttr {
                        expr: Box::new(base),
                        attr: key,
                    },
                    member_span,
                );
            }
            Rule::access_call => {
                return Err(err(
                    "unexpected call: only extension functions and methods can be called",
                    span_of(&acc),
                ));
            }
            other => unreachable!("unexpected mem_access child: {other:?}"),
        }
    }
    Ok(base)
}

/// The identifier of an `access_field` (`. any_ident`).
fn field_name(pair: &Pair<'_>) -> String {
    pair.clone()
        .into_inner()
        .find(|p| p.as_rule() == Rule::any_ident)
        .map(|p| p.as_str().to_string())
        .expect("access_field has an any_ident")
}

/// The string key of an `access_index` (`[ "k" ]`).
fn index_key(pair: &Pair<'_>) -> Result<String, RawParseError> {
    let span = span_of(pair);
    let expr = pair
        .clone()
        .into_inner()
        .find(|p| p.as_rule() == Rule::expr)
        .ok_or_else(|| err("empty index access", span))?;
    // Drill to a string literal; Cedar only allows a string key here.
    match string_literal_of(&expr) {
        Some(s) => s,
        None => Err(err(
            "index access requires a string-literal key, e.g. `record[\"field\"]`",
            span,
        )),
    }
}

/// If `expr` is exactly a string literal, return its decoded value. The outer
/// `Option` says whether it is one; the inner `Result` carries an escape error.
fn string_literal_of(expr: &Pair<'_>) -> Option<Result<String, RawParseError>> {
    // expr → or → and → rel → add → mult → unary → member → primary →
    // literal → string. Walk the single-child chain; bail if it branches.
    let mut cur = expr.clone();
    loop {
        let rule = cur.as_rule();
        if rule == Rule::string {
            let span = span_of(&cur);
            return Some(decode_string(cur.as_str(), span));
        }
        let mut children = cur.clone().into_inner();
        let first = children.next()?;
        if children.next().is_some() {
            return None; // more than one child: not a lone literal
        }
        cur = first;
    }
}

/// Extension function application: `decimal("…")`, `ip("…")`, etc., or
/// an unresolved macro call. Built-in names become a surface [`UnOp`] / [`BinOp`]
/// application; any other name is left as [`Expr::Call`] for the macro expansion
/// pass to resolve (it errors out if the name isn't a declared macro either).
fn build_function_call(
    name_pair: &Pair<'_>,
    call: Pair<'_>,
    limit: usize,
) -> Result<Expr, RawParseError> {
    // Span the whole application (`name(...)`), from the function name
    // through the closing paren of the call.
    let span = Span::new(span_of(name_pair).start, span_of(&call).end);
    let fname = name_path(name_pair).join("::");
    let mut args = call_args(call, limit)?;
    let op = match fname.as_str() {
        "decimal" => Some(UnOp::Decimal),
        "datetime" => Some(UnOp::Datetime),
        "duration" => Some(UnOp::Duration),
        "ip" => Some(UnOp::Ip),
        _ => None,
    };
    if let Some(op) = op {
        if args.len() != 1 {
            return Err(err(
                format!("`{fname}` takes exactly one argument, got {}", args.len()),
                span,
            ));
        }
        return Ok(Expr::new(
            ExprKind::UnaryApp {
                op,
                expr: Box::new(args.remove(0)),
            },
            span,
        ));
    }
    Ok(Expr::new(ExprKind::Call { name: fname, args }, span))
}

/// Method application: `xs.contains(y)`, `d.lessThan(e)`, `s.isEmpty()`.
fn build_method_call(
    receiver: Expr,
    method: &str,
    call: Pair<'_>,
    member_start: usize,
    limit: usize,
) -> Result<Expr, RawParseError> {
    // The node spans from the enclosing member's start (so a parenthesized
    // receiver's `(` is included, as Cedar does) through the call's closing
    // paren.
    let node_span = Span::new(member_start, span_of(&call).end);
    let mut args = call_args(call, limit)?;

    // Zero-argument (receiver-only) methods → unary ops.
    let unary = match method {
        "isEmpty" => Some(UnOp::IsEmpty),
        "isIpv4" => Some(UnOp::IsIpv4),
        "isIpv6" => Some(UnOp::IsIpv6),
        "isLoopback" => Some(UnOp::IsLoopback),
        "isMulticast" => Some(UnOp::IsMulticast),
        "toDate" => Some(UnOp::ToDate),
        "toTime" => Some(UnOp::ToTime),
        "toMilliseconds" => Some(UnOp::ToMilliseconds),
        "toSeconds" => Some(UnOp::ToSeconds),
        "toMinutes" => Some(UnOp::ToMinutes),
        "toHours" => Some(UnOp::ToHours),
        "toDays" => Some(UnOp::ToDays),
        _ => None,
    };
    if let Some(op) = unary {
        if !args.is_empty() {
            return Err(err(
                format!("`{method}` takes no arguments, got {}", args.len()),
                node_span,
            ));
        }
        return Ok(Expr::new(
            ExprKind::UnaryApp {
                op,
                expr: Box::new(receiver),
            },
            node_span,
        ));
    }

    // One-argument methods → binary ops.
    let binary = match method {
        "contains" => BinOp::Contains,
        "containsAll" => BinOp::ContainsAll,
        "containsAny" => BinOp::ContainsAny,
        "getTag" => BinOp::GetTag,
        "hasTag" => BinOp::HasTag,
        "isInRange" => BinOp::IsInRange,
        "offset" => BinOp::Offset,
        "durationSince" => BinOp::DurationSince,
        "lessThan" => BinOp::DecimalLessThan,
        "lessThanOrEqual" => BinOp::DecimalLessEq,
        "greaterThan" => BinOp::DecimalGreater,
        "greaterThanOrEqual" => BinOp::DecimalGreaterEq,
        other => {
            // Not a Cedar built-in method. It may be a *provider output
            // method* (`Ns::Fn(x).classify()`, `.maxConfidenceScore(…)`),
            // which is only resolvable once the provider declarations are
            // known — so defer it as an `ExprKind::MethodCall` rather than
            // erroring here. Lowering (`crate::cedarify`) either hoists the
            // chain (declared provider base) or rejects it as an unknown
            // method. Cedar built-in methods above still desugar eagerly, so
            // an ordinary typo on a non-provider receiver (`x.footgun()`)
            // becomes the same `unknown method` error, just at lowering time.
            let _ = other;
            return Ok(Expr::new(
                ExprKind::MethodCall {
                    receiver: Box::new(receiver),
                    method: method.to_string(),
                    args,
                },
                node_span,
            ));
        }
    };
    if args.len() != 1 {
        return Err(err(
            format!("`{method}` takes exactly one argument, got {}", args.len()),
            node_span,
        ));
    }
    Ok(Expr::new(
        ExprKind::BinaryApp {
            op: binary,
            left: Box::new(receiver),
            right: Box::new(args.remove(0)),
        },
        node_span,
    ))
}

/// Build the argument list of an `access_call`.
fn call_args(call: Pair<'_>, limit: usize) -> Result<Vec<Expr>, RawParseError> {
    call.into_inner()
        .filter(|p| p.as_rule() == Rule::expr)
        .map(|arg| build_expr(arg, limit))
        .collect()
}

/// `primary := extension_marker | literal | slot | ref_ | name |
/// paren_expr | list | record`.
fn build_primary(pair: Pair<'_>, limit: usize) -> Result<Expr, RawParseError> {
    let span = span_of(&pair);
    let inner = pair.into_inner().next().expect("primary has a child");
    match inner.as_rule() {
        Rule::extension_marker => build_extension_marker(inner, limit),
        Rule::literal => Ok(Expr::new(ExprKind::Lit(build_literal(&inner)?), span)),
        Rule::slot => build_slot(&inner),
        Rule::ref_ => Ok(Expr::new(ExprKind::Lit(build_ref(inner)?), span)),
        Rule::name => resolve_name(&inner),
        Rule::paren_expr => {
            let e = inner
                .into_inner()
                .find(|p| p.as_rule() == Rule::expr)
                .expect("paren has an expr");
            build_expr(e, limit)
        }
        Rule::list => {
            let elems = inner
                .into_inner()
                .filter(|p| p.as_rule() == Rule::expr)
                .map(|elem| build_expr(elem, limit))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::new(ExprKind::Set(elems), span))
        }
        Rule::record => build_record(inner, span, limit),
        other => unreachable!("unexpected primary child: {other:?}"),
    }
}

/// Resolve a bare `name` in value position: one of the four request
/// variables, or an error (bare names are otherwise only valid as entity
/// types or function names, handled elsewhere).
fn resolve_name(pair: &Pair<'_>) -> Result<Expr, RawParseError> {
    let s = name_path(pair).join("::");
    let var = match s.as_str() {
        "principal" => pst::Var::Principal,
        "action" => pst::Var::Action,
        "resource" => pst::Var::Resource,
        "context" => pst::Var::Context,
        other => {
            let in_scope = IN_SCOPE_CONTEXT.with(|c| c.get());
            let msg = if other.contains("::") {
                if in_scope {
                    format!(
                        "`{other}` is not a valid entity reference; try \
                         `{other}::\"<id>\"` for a specific entity, or \
                         `is {other}` to match by type"
                    )
                } else {
                    format!("`{other}` is not a valid expression")
                }
            } else {
                format!("`{other}` is not a valid variable")
            };
            return Err(err(msg, span_of(pair)));
        }
    };
    Ok(Expr::new(ExprKind::Var(var.into()), span_of(pair)))
}

/// `slot := ?principal | ?resource | ?ident`.
///
/// `?principal` / `?resource` are Cedar template slots. Any other
/// `?ident` is a macro parameter reference ([`Expr::ParamRef`]) — only
/// legal inside a macro body, but parsing accepts it everywhere so the
/// macro expansion pass can both substitute it (inside a body) and
/// reject it (everywhere else) with a clear error.
fn build_slot(pair: &Pair<'_>) -> Result<Expr, RawParseError> {
    let span = span_of(pair);
    let inner = pair.clone().into_inner().next().expect("slot has a child");
    match inner.as_rule() {
        Rule::slot_principal => Ok(Expr::new(
            ExprKind::Slot(pst::SlotId::Principal.into()),
            span,
        )),
        Rule::slot_resource => Ok(Expr::new(
            ExprKind::Slot(pst::SlotId::Resource.into()),
            span,
        )),
        Rule::slot_other => {
            // Strip the leading `?` from the captured text.
            let name = inner.as_str().trim_start_matches('?').to_string();
            Ok(Expr::new(ExprKind::ParamRef { name }, span))
        }
        other => unreachable!("unexpected slot child: {other:?}"),
    }
}

/// `literal := true | false | number | string`.
fn build_literal(pair: &Pair<'_>) -> Result<cedar_ast::Literal, RawParseError> {
    let inner = pair
        .clone()
        .into_inner()
        .next()
        .expect("literal has a child");
    match inner.as_rule() {
        Rule::kw_true => Ok(cedar_ast::Literal::from(true)),
        Rule::kw_false => Ok(cedar_ast::Literal::from(false)),
        Rule::number => {
            // Cedar's lexer treats all numeric literals as unsigned;
            // negation is a unary operator applied in build_unary. A literal
            // must fit i64 on its own: the one exception, a directly negated
            // 2^63, is built by build_unary and never reaches here.
            let n = inner.as_str().parse::<i64>().map_err(|_| {
                err(
                    format!("integer literal `{}` is out of range", inner.as_str()),
                    span_of(&inner),
                )
            })?;
            Ok(cedar_ast::Literal::Long(n))
        }
        Rule::string => {
            let span = span_of(&inner);
            Ok(cedar_ast::Literal::String(
                decode_string(inner.as_str(), span)?.into(),
            ))
        }
        other => unreachable!("unexpected literal child: {other:?}"),
    }
}

/// `ref_ := name "::" string` → an entity UID literal `Ns::Type::"eid"`.
fn build_ref(pair: Pair<'_>) -> Result<cedar_ast::Literal, RawParseError> {
    let span = span_of(&pair);
    let mut name = None;
    let mut eid = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::name => name = Some(name_path(&child)),
            Rule::string => {
                let eid_span = span_of(&child);
                eid = Some(decode_string(child.as_str(), eid_span)?);
            }
            Rule::ref_record => {
                return Err(err(
                    "entity initializer syntax `Type::{ … }` is not supported",
                    span_of(&child),
                ));
            }
            _ => {}
        }
    }
    let name = name.ok_or_else(|| err("entity reference is missing a type", span))?;
    let eid = eid.ok_or_else(|| err("entity reference is missing an id", span))?;
    let ty = make_entity_type(&name, span)?;
    let uid = cedar_ast::EntityUID::from_components(ty, cedar_ast::Eid::new(eid), None);
    Ok(cedar_ast::Literal::EntityUID(std::sync::Arc::new(uid)))
}

/// `record := "{" [ rec_init { "," rec_init } ] "}"`.
fn build_record(pair: Pair<'_>, span: Span, limit: usize) -> Result<Expr, RawParseError> {
    let mut map = std::collections::BTreeMap::new();
    for init in pair.into_inner().filter(|p| p.as_rule() == Rule::rec_init) {
        let inner = init.into_inner().next().expect("rec_init has a child");
        let (key, value) = match inner.as_rule() {
            Rule::rec_init_if => {
                let value = inner
                    .into_inner()
                    .find(|p| p.as_rule() == Rule::expr)
                    .expect("rec_init_if has a value");
                ("if".to_string(), build_expr(value, limit)?)
            }
            Rule::rec_init_expr => {
                let mut exprs = inner.into_inner().filter(|p| p.as_rule() == Rule::expr);
                let key_pair = exprs.next().expect("record key");
                let value_pair = exprs.next().expect("record value");
                (
                    record_key(&key_pair, span)?,
                    build_expr(value_pair, limit)?,
                )
            }
            other => unreachable!("unexpected rec_init child: {other:?}"),
        };
        // As in Cedar, a key may appear once; keys compare after decoding.
        if map.contains_key(&key) {
            return Err(err(
                format!("duplicate key `{key}` in record literal"),
                span,
            ));
        }
        map.insert(key, value);
    }
    Ok(Expr::new(ExprKind::Record(map), span))
}

/// A record key is a string literal or an unqualified name on its own, as in
/// Cedar, read from its tokens rather than its text.
fn record_key(expr: &Pair<'_>, span: Span) -> Result<String, RawParseError> {
    let invalid = || err("record keys must be identifiers or string literals", span);
    let primary = [
        Rule::or,
        Rule::and,
        Rule::rel,
        Rule::add,
        Rule::mult,
        Rule::unary,
        Rule::member,
        Rule::primary,
    ]
    .into_iter()
    .try_fold(expr.clone(), only_child)
    .ok_or_else(invalid)?;
    let leaf = primary.into_inner().next().ok_or_else(invalid)?;
    match leaf.as_rule() {
        Rule::name => match name_path(&leaf).as_slice() {
            [ident] => Ok(ident.clone()),
            _ => Err(invalid()),
        },
        Rule::literal => {
            let string = only_child(leaf, Rule::string).ok_or_else(invalid)?;
            decode_string(string.as_str(), span_of(&string))
        }
        _ => Err(invalid()),
    }
}

// ── Name / entity-type helpers ──────────────────────────────────────

/// The segments of a `name` (`Ns::User` is `["Ns", "User"]`), read from its
/// identifier tokens rather than its text, which can hold comments.
fn name_path(name: &Pair<'_>) -> Vec<String> {
    name.clone()
        .into_inner()
        .map(|ident| ident.as_str().to_string())
        .collect()
}

/// Build a `cedar_ast::EntityType` from name segments (`["Drupe",
/// "OAuthUser"]` → `Drupe::OAuthUser`), via Cedar's `pst::Name` as the
/// name-parsing helper.
fn make_entity_type(
    segments: &[String],
    span: Span,
) -> Result<cedar_ast::EntityType, RawParseError> {
    let (basename, namespace) = segments
        .split_last()
        .ok_or_else(|| err("empty entity type name", span))?;
    pst::Name::qualified(namespace.iter(), basename)
        .map(pst::EntityType::from_name)
        .map(cedar_ast::EntityType::from)
        .map_err(|e| {
            err(
                format!("invalid entity type `{}`: {e}", segments.join("::")),
                span,
            )
        })
}

/// Extract an entity *type* from an `add` subtree (the operand of `is`).
/// The operand is syntactically an expression but semantically a type
/// name, so, as in Cedar, it must be a `name` on its own, read from its
/// tokens rather than evaluated as a value.
fn extract_entity_type(add: Pair<'_>, span: Span) -> Result<cedar_ast::EntityType, RawParseError> {
    let text = add.as_str().trim();
    let name = only_child(add.clone(), Rule::mult)
        .and_then(|mult| only_child(mult, Rule::unary))
        .and_then(|unary| only_child(unary, Rule::member))
        .and_then(|member| only_child(member, Rule::primary))
        .and_then(|primary| only_child(primary, Rule::name))
        .ok_or_else(|| {
            // For the message only: say why the text is not a type name.
            let segments: Vec<String> = text.split("::").map(|s| s.trim().to_string()).collect();
            make_entity_type(&segments, span)
                .err()
                .unwrap_or_else(|| err(format!("invalid entity type `{text}`"), span))
        })?;
    make_entity_type(&name_path(&name), span)
}

/// Extract the attribute path of a `has_tail` (`has output`,
/// `has a.b.c`, `has if.x`).
fn extract_has_path(tail: Pair<'_>) -> Result<Vec<String>, RawParseError> {
    let span = span_of(&tail);
    let rhs = tail
        .into_inner()
        .find(|p| p.as_rule() == Rule::has_rhs)
        .ok_or_else(|| err("`has` is missing an attribute", span))?;
    let rhs_span = span_of(&rhs);
    let rhs_text = rhs.as_str().trim();
    let inner = rhs.into_inner().next().expect("has_rhs has a child");
    match inner.as_rule() {
        // `has if` followed by `.x.y` field accesses.
        Rule::has_if_rhs => {
            let mut attrs = vec!["if".to_string()];
            for acc in inner
                .into_inner()
                .filter(|p| p.as_rule() == Rule::mem_access)
            {
                attrs.push(has_path_field(acc, rhs_text, rhs_span)?);
            }
            Ok(attrs)
        }
        Rule::add => extract_attr_path(inner, rhs_text, rhs_span),
        other => unreachable!("unexpected has_rhs child: {other:?}"),
    }
}

/// Read the attribute path of a `has` from an `add` subtree.
///
/// The grammar admits any `add` after `has`, but, as in Cedar's `to_has_rhs`,
/// only three shapes are attribute paths: an unquoted name, an unquoted name
/// followed by `.field` accesses (`has a.b.c`), and a string literal
/// (`has "attr"`). An unquoted name is any `common_ident`, which includes words
/// Cedar reserves (`then`, `in`, `has`); `true` and `false` are literals here.
/// Everything else is an error: an operator (`a + b`, and so an
/// unquoted `tool-approval`, which is `tool - approval`), a `!` or `-` prefix,
/// parentheses, a list, a record, a qualified name, an index, or a call.
/// Reading only part of such an operand would test a different attribute from
/// the one written.
fn extract_attr_path(add: Pair<'_>, text: &str, span: Span) -> Result<Vec<String>, RawParseError> {
    let invalid = || invalid_has_rhs(text, span);
    let member = only_child(add, Rule::mult)
        .and_then(|mult| only_child(mult, Rule::unary))
        .and_then(|unary| only_child(unary, Rule::member))
        .ok_or_else(invalid)?;
    let mut parts = member.into_inner();
    let primary = parts.next().ok_or_else(invalid)?;
    let first = primary.into_inner().next().ok_or_else(invalid)?;
    match first.as_rule() {
        // An unqualified `name` is a single `common_ident`; a qualified one
        // (`A::B`) is a path, not an attribute.
        Rule::name => {
            let ident = only_child(first, Rule::common_ident).ok_or_else(invalid)?;
            let mut attrs = vec![ident.as_str().to_string()];
            for acc in parts {
                attrs.push(has_path_field(acc, text, span)?);
            }
            Ok(attrs)
        }
        // A string literal names one attribute and takes no accesses.
        Rule::literal => {
            let string = only_child(first, Rule::string).ok_or_else(invalid)?;
            if parts.next().is_some() {
                return Err(invalid());
            }
            Ok(vec![decode_string(string.as_str(), span_of(&string))?])
        }
        _ => Err(invalid()),
    }
}

/// The attribute named by one `mem_access` of a `has` path, which must be a
/// `.field` access.
fn has_path_field(acc: Pair<'_>, text: &str, span: Span) -> Result<String, RawParseError> {
    only_child(acc, Rule::access_field)
        .map(|field| field_name(&field))
        .ok_or_else(|| invalid_has_rhs(text, span))
}

fn invalid_has_rhs(text: &str, span: Span) -> RawParseError {
    err(
        format!(
            "invalid right-hand side of `has`: `{text}`; expected an attribute name, a dotted \
             path such as `a.b`, or a quoted name such as `\"a b\"` (quote a name that is not \
             an identifier, or is `true` or `false`)"
        ),
        span,
    )
}

/// The sole child of `pair`, if it has exactly one child and that child is a
/// `rule`.
fn only_child(pair: Pair<'_>, rule: Rule) -> Option<Pair<'_>> {
    let mut children = pair.into_inner();
    let child = children.next().filter(|c| c.as_rule() == rule)?;
    children.next().is_none().then_some(child)
}

/// If `member_pair` is a *direct* (non-parenthesized) number literal
/// (`member = primary ~ mem_access*` where the sole child is a `number`
/// primary), return its digit text. A parenthesized `(N)`, a nested value,
/// or anything with accessors returns `None`.
///
/// This distinguishes `-N` (fold to `Long(-N)`) from `-(N)` (a genuine
/// `Neg` over a positive literal) — matching Cedar, which only
/// constant-folds a directly-negated numeric token and otherwise keeps a
/// `Neg` wrapping the positive literal at the digit span.
fn bare_number_text(member_pair: &Pair<'_>) -> Option<String> {
    let mut children = member_pair.clone().into_inner();
    let primary = match children.next() {
        Some(p) if p.as_rule() == Rule::primary => p,
        _ => return None,
    };
    // Accessors (`.a`, `["k"]`, `(args)`) ⇒ not a bare literal.
    if children.next().is_some() {
        return None;
    }
    // The primary must be a `literal` (not `paren_expr`, list, record, …).
    let literal = match primary.into_inner().next() {
        Some(p) if p.as_rule() == Rule::literal => p,
        _ => return None,
    };
    match literal.into_inner().next() {
        Some(p) if p.as_rule() == Rule::number => Some(p.as_str().to_string()),
        _ => None,
    }
}

/// Build a `like` pattern from the `add` RHS, which must be a string
/// literal. `*` is a wildcard; `\*` a literal star.
///
/// The grammar admits any `add` after `like`, but, as in Cedar, the pattern is
/// the literal alone: an operator (`"a" + "/*"`), a prefix, an access,
/// parentheses, or any other operand is an error. Reading one literal out of
/// such an operand would match a different pattern from the one written.
fn extract_pattern(
    add: Pair<'_>,
    span: Span,
) -> Result<Vec<cedar_ast::PatternElem>, RawParseError> {
    let add_str = add.as_str().trim();
    // Take the raw string token so we can see the escapes verbatim.
    let string = only_child(add, Rule::mult)
        .and_then(|mult| only_child(mult, Rule::unary))
        .and_then(|unary| only_child(unary, Rule::member))
        .and_then(|member| only_child(member, Rule::primary))
        .and_then(|primary| only_child(primary, Rule::literal))
        .and_then(|literal| only_child(literal, Rule::string))
        .ok_or_else(|| {
            err(
                format!("`like` requires a string-literal pattern, but got `{add_str}`"),
                span,
            )
        })?;
    let raw = string.as_str();
    // Strip the surrounding quotes.
    let body = &raw[1..raw.len().saturating_sub(1)];
    build_pattern(body, span)
}

/// Convert a `like` pattern body (quotes already stripped, escapes intact) into
/// Cedar pattern elements.
///
/// This mirrors Cedar's `cedar_policy_core::parser::unescape::to_pattern`,
/// which is `pub(crate)` and so cannot be called directly. Rather than
/// re-derive the escape grammar (the divergence that
/// [`decode_string`]/`to_unescaped_string` fixed for plain string literals),
/// we drive the *same* underlying escaper Cedar's `to_pattern` uses —
/// [`rustc_literal_escaper::unescape_str`] — and apply the one pattern-specific
/// rule on top: an unescaped `*` is a wildcard, and the escape `\*` (which the
/// escaper reports as [`EscapeError::InvalidEscape`], since it is not a valid
/// *string* escape) is a literal `*`. Every other escape follows the string
/// grammar exactly, so a malformed escape (`\x`/`\u{…}` out of range, unknown
/// escape, …) is a parse error here just as it is in Cedar.
///
/// Keep this byte-for-byte faithful to Cedar's `to_pattern`; the
/// `parser::pattern_escape_differential` tests pin the agreement. When Cedar
/// makes `to_pattern` public, this should call it directly.
fn build_pattern(body: &str, span: Span) -> Result<Vec<cedar_ast::PatternElem>, RawParseError> {
    let mut out = Vec::new();
    let mut escape_err: Option<String> = None;
    let bytes = body.as_bytes();
    unescape_str(body, |range, res| match res {
        Ok(c) => out.push(if c == '*' {
            cedar_ast::PatternElem::Wildcard
        } else {
            cedar_ast::PatternElem::Char(c)
        }),
        // `\*` is not a valid *string* escape (the escaper flags it as
        // `InvalidEscape`), but it IS the pattern escape for a literal star.
        // Match on the exact byte slice, as Cedar's `to_pattern` does.
        Err(EscapeError::InvalidEscape) if bytes.get(range.clone()) == Some(br"\*".as_slice()) => {
            out.push(cedar_ast::PatternElem::Char('*'));
        }
        // The escaper also emits non-fatal warnings (unskipped whitespace,
        // multiple skipped lines); only fatal errors are real parse errors.
        Err(e) if e.is_fatal() => {
            if escape_err.is_none() {
                // Match `to_unescaped_string`'s message for the same input, so
                // pattern and string escape diagnostics read identically.
                escape_err = Some(format!(
                    "the input `{}` is not a valid escape",
                    &body[range]
                ));
            }
        }
        Err(_) => {}
    });
    match escape_err {
        Some(msg) => Err(err(msg, span)),
        None => Ok(out),
    }
}

/// Decode a string literal token (including surrounding quotes) into its
/// value. Escapes are decoded by Cedar's [`to_unescaped_string`], so a
/// malformed escape is a parse error here as it is in Cedar. Cedar reports one
/// error per bad escape; we surface the first, with the literal's span.
fn decode_string(raw: &str, span: Span) -> Result<String, RawParseError> {
    let body = &raw[1..raw.len().saturating_sub(1)];
    match to_unescaped_string(body) {
        Ok(s) => Ok(s.to_string()),
        Err(errs) => Err(err(errs.head.to_string(), span)),
    }
}

#[cfg(test)]
mod macro_parse_smoke {
    //! Smoke tests verifying that `def cedar` / `def temporal`
    //! declarations parse into [`PolicySet::defs`] (Phase 1 — no
    //! expansion yet). Lives next to the parser since the AST and the
    //! `parse_policies` entry are crate-private.

    use super::*;
    use crate::ast::ExprKind;
    use crate::extension::temporal::ast::{AggExprKind, ConditionKind, Term as TemporalTerm};

    fn parse(src: &str) -> PolicySet {
        parse_policies(src).unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
    }

    #[test]
    fn def_cedar_parses_and_lands_in_defs() {
        let ps = parse(
            r#"
                def cedar is_admin(?u) {
                    ?u == User::"alice"
                };
                permit (principal, action, resource);
            "#,
        );
        assert_eq!(ps.defs.len(), 1);
        let def = &ps.defs[0];
        assert_eq!(def.name, "is_admin");
        assert_eq!(def.params.len(), 1);
        assert_eq!(def.params[0].name, "u");
        assert!(matches!(def.body, MacroBody::Cedar(_)));
    }

    #[test]
    fn def_temporal_condition_body_parses() {
        let ps = parse(
            r#"
                def temporal recent_login(?w) {
                    formerly within 1h Drupe::Action::"Login"::request{ user: principal }
                };
            "#,
        );
        assert_eq!(ps.defs.len(), 1);
        let def = &ps.defs[0];
        match &def.body {
            MacroBody::TemporalCondition(c) => match &c.kind {
                ConditionKind::Formerly { .. } => {}
                other => panic!("expected Formerly, got {other:?}"),
            },
            other => panic!("expected TemporalCondition body, got {other:?}"),
        }
    }

    #[test]
    fn def_temporal_count_agg_parses() {
        let ps = parse(
            r#"
                def temporal count_formerly(?w, ?s) {
                    count for ($t: Timepoint). where (formerly within 1h (Drupe::Action::"Login"::request{} && tp($t)))
                };
            "#,
        );
        let def = &ps.defs[0];
        assert_eq!(def.params.len(), 2);
        assert_eq!(def.params[0].name, "w");
        assert_eq!(def.params[1].name, "s");
        match &def.body {
            MacroBody::TemporalValue(TemporalTerm::Agg(agg)) => match &agg.kind {
                AggExprKind::Count { .. } => {}
                other => panic!("expected Count, got {other:?}"),
            },
            other => panic!("expected TemporalValue(Agg) body, got {other:?}"),
        }
    }

    #[test]
    fn def_temporal_sum_agg_parses() {
        let ps = parse(
            r#"
                def temporal sum_formerly(?a, ?w, ?body) {
                    sum ?a for (?a: Long), ($t: Timepoint). where (formerly within 1h (?body && tp($t)))
                };
            "#,
        );
        let def = &ps.defs[0];
        assert_eq!(def.params.len(), 3);
        match &def.body {
            MacroBody::TemporalValue(TemporalTerm::Agg(agg)) => match &agg.kind {
                AggExprKind::Sum { .. } => {}
                other => panic!("expected Sum, got {other:?}"),
            },
            other => panic!("expected TemporalValue(Agg) body, got {other:?}"),
        }
    }

    #[test]
    fn defs_and_policies_interleave() {
        let ps = parse(
            r#"
                def cedar a(?x) { ?x };
                permit (principal, action, resource);
                def cedar b(?y) { ?y };
                permit (principal, action, resource);
            "#,
        );
        assert_eq!(ps.defs.len(), 2);
        assert_eq!(ps.policies.len(), 2);
        assert_eq!(ps.defs[0].name, "a");
        assert_eq!(ps.defs[1].name, "b");
    }

    #[test]
    fn unknown_function_call_in_cedar_body_parses_as_call() {
        let ps = parse(
            r#"
                permit (principal, action, resource)
                when { is_admin(principal) };
            "#,
        );
        let body = &ps.policies[0].conditions[0].body;
        match &body.kind {
            ExprKind::Call { name, args, .. } => {
                assert_eq!(name, "is_admin");
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected ExprKind::Call, got {other:?}"),
        }
    }

    #[test]
    fn expr_nodes_carry_dw_spans() {
        // Every `Expr` node now records its originating `.dw` byte range.
        // Assert that a sub-expression's span slices back to exactly its
        // source text — the property the cedarify `to_ast` rewrite (step 2)
        // relies on to give Cedar diagnostics `.dw`-accurate locations.
        let src = r#"permit (principal, action, resource)
                when { context.input.amount > 5 };"#;
        let ps = parse(src);
        let body = &ps.policies[0].conditions[0].body;

        // Top: `context.input.amount > 5` — a `>` comparison whose span
        // covers the whole relation.
        let (op, left, right) = match &body.kind {
            ExprKind::BinaryApp { op, left, right } => (op, left, right),
            other => panic!("expected BinaryApp, got {other:?}"),
        };
        assert_eq!(*op, BinOp::Greater);
        assert_eq!(
            &src[body.span.start..body.span.end],
            "context.input.amount > 5"
        );

        // Left operand `context.input.amount` — a nested GetAttr; its span
        // slices back to exactly that dotted path.
        assert!(
            matches!(left.kind, ExprKind::GetAttr { .. }),
            "lhs is GetAttr"
        );
        assert_eq!(
            &src[left.span.start..left.span.end],
            "context.input.amount",
            "GetAttr span is the exact `.dw` sub-expression"
        );

        // Right operand `5` — a literal whose span is just the digit.
        assert!(matches!(right.kind, ExprKind::Lit(_)), "rhs is a literal");
        assert_eq!(&src[right.span.start..right.span.end], "5");
    }
}

#[cfg(test)]
mod string_escape_differential {
    //! String-literal escape handling must agree with Cedar's, since Dogwood
    //! is an extension of Cedar. Each case parses the same policy text with
    //! both parsers and compares.

    use super::{cedar_ast, decode_string};

    /// The value Cedar's parser gives `… == "<body>"`, or `None` if it rejects
    /// the policy.
    fn cedar(body: &str) -> Option<String> {
        let src =
            format!(r#"permit(principal, action, resource) when {{ context.p == "{body}" }};"#);
        let policy = cedar_policy_core::parser::parse_policy(None, &src).ok()?;
        policy.condition().subexpressions().find_map(|e| {
            if let cedar_ast::ExprKind::Lit(cedar_ast::Literal::String(s)) = e.expr_kind() {
                Some(s.to_string())
            } else {
                None
            }
        })
    }

    /// The value Dogwood's parser gives the same literal.
    fn ours(body: &str) -> Option<String> {
        let src =
            format!(r#"permit(principal, action, resource) when {{ context.p == "{body}" }};"#);
        let set = super::parse_policies(&src).ok()?;
        let mut found = None;
        set.policies[0].conditions[0]
            .body
            .for_each_node(&mut |e: &crate::ast::Expr| {
                if let crate::ast::ExprKind::Lit(cedar_ast::Literal::String(s)) = &e.kind {
                    found = Some(s.to_string());
                }
            });
        found
    }

    #[test]
    fn matches_cedar_on_the_common_escapes() {
        for body in [
            r"plain",
            r"a\nb",
            r"a\tb",
            r"a\rb",
            r#"a\"b"#,
            r"a\\b",
            r"a\'b",
            r"\0",
            r"\u{1e}",
            r"\u{1F600}",
        ] {
            assert_eq!(ours(body), cedar(body), "disagreed on {body:?}");
        }
    }

    #[test]
    fn matches_cedar_on_hex_escapes() {
        assert_eq!(cedar(r"\x41").as_deref(), Some("A"));
        assert_eq!(ours(r"\x41"), cedar(r"\x41"));
    }

    #[test]
    fn rejects_the_escapes_cedar_rejects() {
        // `\q` is not an escape; `\*` is meaningful only in a `like` pattern.
        for body in [r"\q", r"a\zb", r"a\*b"] {
            assert_eq!(cedar(body), None, "Cedar should reject {body:?}");
            assert_eq!(ours(body), None, "Dogwood should reject {body:?}");
        }
    }

    #[test]
    fn an_escape_error_reports_as_such() {
        let src = r#"permit(principal, action, resource) when { context.p == "a\qb" };"#;
        let errs = super::parse_policies(src).expect_err("`\\q` must be rejected");
        let msg = format!("{errs:?}");
        assert!(
            !msg.contains("string-literal") && !msg.contains("attribute name"),
            "escape error should not surface as an unrelated parse error: {msg}"
        );
    }

    #[test]
    fn decode_string_takes_the_quoted_token() {
        let span = crate::error::Span::new(0, 0);
        assert_eq!(decode_string(r#""a\nb""#, span).unwrap(), "a\nb");
        assert!(decode_string(r#""a\qb""#, span).is_err());
    }
}

#[cfg(test)]
mod pattern_escape_differential {
    //! `like`-pattern escape handling must agree with Cedar's, since Dogwood is
    //! an extension of Cedar. Cedar's counterpart (`to_pattern`) is
    //! `pub(crate)`, so — exactly as `string_escape_differential` does for
    //! plain string literals — each case parses the same `like` policy with
    //! both parsers and compares the resulting pattern (or the rejection).

    use super::cedar_ast;

    /// Render Cedar's pattern for `… like "<body>"` as a string, or `None` if
    /// Cedar rejects the policy. `Pattern`'s `Display` round-trips the elems
    /// (`*` for a wildcard, `\*` for a literal star), so it is a faithful,
    /// order-preserving key for comparison.
    fn cedar(body: &str) -> Option<String> {
        let src =
            format!(r#"permit(principal, action, resource) when {{ context.p like "{body}" }};"#);
        let policy = cedar_policy_core::parser::parse_policy(None, &src).ok()?;
        policy.condition().subexpressions().find_map(|e| {
            if let cedar_ast::ExprKind::Like { pattern, .. } = e.expr_kind() {
                Some(pattern.to_string())
            } else {
                None
            }
        })
    }

    /// Render Dogwood's pattern for the same policy, or `None` if we reject it.
    fn ours(body: &str) -> Option<String> {
        let src =
            format!(r#"permit(principal, action, resource) when {{ context.p like "{body}" }};"#);
        let set = super::parse_policies(&src).ok()?;
        // `Like` lives at the top of the (single) condition body; render its
        // elems through Cedar's `Pattern` so the key matches `cedar()`.
        if let crate::ast::ExprKind::Like { pattern, .. } = &set.policies[0].conditions[0].body.kind
        {
            Some(cedar_ast::Pattern::from(pattern.clone()).to_string())
        } else {
            None
        }
    }

    #[test]
    fn matches_cedar_on_the_common_escapes_and_wildcards() {
        for body in [
            r"plain",
            r"a*b",  // wildcard
            r"a\*b", // literal star — legal only in a pattern
            r"\\*",  // literal backslash, then wildcard
            r"a\\b", // literal backslash
            r"a\nb",
            r"a\tb",
            r"a\rb",
            r#"a\"b"#,
            r"\0",
            r"\u{1e}",
            r"\u{1F600}",
        ] {
            assert_eq!(ours(body), cedar(body), "disagreed on {body:?}");
        }
    }

    #[test]
    fn matches_cedar_on_hex_and_underscored_unicode() {
        // The two silent-mis-decode facets: `\xHH` and `_`-separated `\u{…}`.
        assert_eq!(cedar(r"\x41").as_deref(), Some("A"));
        assert_eq!(ours(r"\x41"), cedar(r"\x41"));
        assert_eq!(cedar(r"\u{4_1}").as_deref(), Some("A"));
        assert_eq!(ours(r"\u{4_1}"), cedar(r"\u{4_1}"));
    }

    #[test]
    fn rejects_the_escapes_cedar_rejects() {
        // Unknown escape, out-of-range hex, empty/out-of-range/lone-surrogate
        // unicode — all parse errors in Cedar, all previously accepted here.
        for body in [
            r"a\qb",
            r"a\bb",
            r"\xFF",
            r"\x4",
            r"\u{}",
            r"\u{110000}",
            r"\u{D800}",
        ] {
            assert_eq!(cedar(body), None, "Cedar should reject {body:?}");
            assert_eq!(ours(body), None, "Dogwood should reject {body:?}");
        }
    }

    #[test]
    fn an_escape_error_reports_as_such() {
        let src = r#"permit(principal, action, resource) when { context.p like "a\qb" };"#;
        let errs = super::parse_policies(src).expect_err("`\\q` must be rejected");
        let msg = format!("{errs:?}");
        assert!(
            msg.contains("not a valid escape"),
            "pattern escape error should report as an escape error: {msg}"
        );
        assert!(
            !msg.contains("requires a string-literal pattern"),
            "escape error must not surface as the unrelated non-string-pattern error: {msg}"
        );
    }
}

#[cfg(test)]
mod negated_2_pow_63 {
    use super::cedar_ast;
    use crate::ast::ExprKind;

    #[test]
    fn is_i64_min_in_any_spelling_as_in_cedar() {
        // Cedar reads the digits by value, so leading zeros don't matter.
        for n in ["-9223372036854775808", "-0009223372036854775808"] {
            let src = format!("permit(principal, action, resource) when {{ {n} == 0 }};");
            assert!(
                cedar_policy_core::parser::parse_policy(None, &src).is_ok(),
                "Cedar: `{n}`"
            );
            let mut set = super::parse_policies(&src).expect("parses");
            let body = set.policies.remove(0).conditions.remove(0).body;
            let ExprKind::BinaryApp { left, .. } = &body.kind else {
                panic!("expected `== 0`, got {body:?}");
            };
            let is_min = matches!(left.kind, ExprKind::Lit(cedar_ast::Literal::Long(i64::MIN)));
            assert!(is_min, "for `{n}`, got {left:?}");
        }
    }
}

#[cfg(test)]
mod block_comments {
    //! A `//` comment inside a raw-captured block (`temporal { … }`, a `def`
    //! body) runs to the end of the line, as it does for the sub-parsers
    //! that read the block. Before, the capture ignored comments, so a `}`
    //! in a comment closed the block early and the rest of the comment line
    //! parsed as live policy.

    use super::parse_policies;

    /// (number of policies, number of defs), or the first error message.
    fn shape(src: &str) -> Result<(usize, usize), String> {
        parse_policies(src)
            .map(|set| (set.policies.len(), set.defs.len()))
            .map_err(|errs| errs.first().map(|e| e.message.clone()).unwrap_or_default())
    }

    const HIDDEN_PERMIT: &str = r#"// }; permit (principal, action, resource) when temporal { formerly within 1h A::Action::"Read"::request{}"#;

    #[test]
    fn a_comment_in_a_temporal_block_cannot_end_the_policy() {
        let src = format!(
            "permit (principal, action == A::Action::\"Login\", resource);\n\
             forbid (principal, action, resource) when temporal {{ formerly within 1h A::Action::\"X\"::request{{}}\n\
             \x20 {HIDDEN_PERMIT}\n\
             \x20 && formerly within 1h A::Action::\"Write\"::request{{}}\n\
             }};\n"
        );
        assert_eq!(shape(&src), Ok((2, 0)), "the comment must not add a policy");
    }

    #[test]
    fn a_comment_in_a_def_body_cannot_end_the_def() {
        let src = format!(
            "def temporal m() {{ formerly within 1h A::Action::\"X\"::request{{}}\n\
             \x20 {HIDDEN_PERMIT}\n\
             \x20 && formerly within 1h A::Action::\"Write\"::request{{}}\n\
             }};\n\
             permit (principal, action == A::Action::\"Login\", resource) when temporal {{ m() }};\n"
        );
        assert_eq!(shape(&src), Ok((1, 1)), "the comment must not add a policy");
    }

    #[test]
    fn unbalanced_braces_and_quotes_in_a_comment_are_inert() {
        for comment in [
            "// closes here }",
            "// TODO: request{ input.user",
            "// the \"x",
            "// }}{{\"\"",
        ] {
            for body_first in [true, false] {
                let atom = r#"formerly within 1h A::Action::"X"::request{}"#;
                let body = if body_first {
                    format!("{atom}\n  {comment}\n")
                } else {
                    format!("\n  {comment}\n  {atom}\n")
                };
                let policy =
                    format!("forbid (principal, action, resource) when temporal {{{body}}};");
                assert_eq!(shape(&policy), Ok((1, 0)), "{policy:?}");
                let def = format!("def temporal m() {{{body}}};\n{policy}");
                assert_eq!(shape(&def), Ok((1, 1)), "{def:?}");
            }
        }
    }

    #[test]
    fn a_double_slash_inside_a_string_is_not_a_comment() {
        let src = r#"forbid (principal, action, resource) when temporal {
  formerly within 1h A::Action::"Fetch"::request{ input.url: "http://h/}" } // a real comment }
};"#;
        assert_eq!(shape(src), Ok((1, 0)));
    }

    #[test]
    fn a_comment_runs_to_the_end_of_the_line() {
        // The closing `}` is inside the comment, so the block never closes on
        // this line. It used to close the block, turning the rest of a
        // comment into code.
        let src = r#"forbid (principal, action, resource) when temporal { formerly within 1h A::Action::"X"::request{} // note };"#;
        assert!(shape(src).is_err(), "the `}}` is part of the comment");
    }
}
#[cfg(test)]
mod def_cedar_body_spans {
    /// An error the builder raises inside a `def cedar` body is located in the
    /// body, not counted from the start of the file.
    #[test]
    fn a_builder_error_in_a_def_cedar_body_points_at_the_body() {
        let src = "permit (principal, action, resource);\ndef cedar m(?x) { foo };";
        let errs = super::parse_policies(src).expect_err("`foo` is not a variable");
        let foo = src.find("foo").expect("foo");
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert_eq!(
            (errs[0].span.start, errs[0].span.end),
            (foo, foo + 3),
            "{errs:?}"
        );
        assert!(errs[0].message.contains("not a valid variable"), "{errs:?}");
    }
}
