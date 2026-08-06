//! The Dogwood parser.
//!
//! Built on a `pest` grammar (`grammar.pest`) that is a translation of
//! Cedar's policy grammar extended with the dialect-marker condition
//! form (`when temporal { ... }`, `unless provider { ... }`). The
//! parse tree is walked into the surface [`crate::ast`].
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

use pest::Parser;
use pest_derive::Parser;

use cedar_ast::{ActionConstraint, EntityReference, PrincipalConstraint, ResourceConstraint};
use cedar_policy::pst;
use cedar_policy_core::ast as cedar_ast;
use cedar_policy_core::parser::Loc;

use crate::ast::{
    Annotation, BinOp, Cond, CondKeyword, Effect, Expr, ExprKind, MacroBody, MacroDef, MacroParam,
    Policy, PolicySet, Scope, UnOp,
};
use crate::error::{RawParseError, Span};
use crate::extension::temporal;
use crate::extension::{Dialect, Extension};

use std::cell::Cell;

#[derive(Parser)]
#[grammar = "parser/grammar.pest"]
struct DogwoodParser;

type Pair<'i> = pest::iterators::Pair<'i, Rule>;

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
    let mut descs: Vec<&str> = rules.iter().map(|r| rule_display(r)).collect();
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

///
/// Returns all policies on success, or the collected parse errors.
pub fn parse_policies(src: &str) -> Result<PolicySet, Vec<RawParseError>> {
    // Strip a leading UTF-8 BOM (U+FEFF) if present — editors and Windows
    // tools sometimes prepend it, and the grammar doesn't expect it.
    let src = src.strip_prefix('\u{FEFF}').unwrap_or(src);
    // Shared `.dw` source for scope entity-UID `Loc`s (so a scope error
    // points at the offending token, not the whole rule).
    let dw_src: std::sync::Arc<str> = std::sync::Arc::from(src);
    let mut pairs = match DogwoodParser::parse(Rule::policies, src) {
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
            Rule::policy => match build_policy(pair, &dw_src) {
                Ok(p) => policies.push(p),
                Err(e) => errors.push(e),
            },
            Rule::def_decl => match build_def_decl(pair) {
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

/// `def_decl = "def" def_kind ident "(" param_list? ")" "{" body "}" ";"`.
fn build_def_decl(pair: Pair<'_>) -> Result<MacroDef, RawParseError> {
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
            let expr = parse_cedar_macro_body(&body_src, body_span)?;
            MacroBody::Cedar(expr)
        }
        DefKind::Temporal => temporal::parse_macro_body(&body_src)
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
fn parse_cedar_macro_body(src: &str, body_span: Span) -> Result<Expr, RawParseError> {
    let mut pairs = DogwoodParser::parse(Rule::expr_entry, src).map_err(|e| {
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
    build_expr(expr_pair)
}

fn build_policy(pair: Pair<'_>, dw_src: &std::sync::Arc<str>) -> Result<Policy, RawParseError> {
    let span = span_of(&pair);
    let mut annotations = Vec::new();
    let mut effect: Option<Effect> = None;
    let mut scope: Option<Scope> = None;
    let mut conditions = Vec::new();

    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::annotation => annotations.push(build_annotation(child)),
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
                scope = Some(build_scope(child, dw_src)?);
            }
            Rule::cond => conditions.push(build_cond(child)?),
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

fn build_annotation(pair: Pair<'_>) -> Annotation {
    let mut key = String::new();
    let mut value = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::any_ident => key = child.as_str().to_string(),
            Rule::string => {
                // Strip the surrounding double quotes; leave inner
                // escapes verbatim (semantic decode is not needed here).
                let raw = child.as_str();
                value = Some(raw.trim_matches('"').to_string());
            }
            _ => {}
        }
    }
    Annotation { key, value }
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
fn build_scope(pair: Pair<'_>, dw_src: &std::sync::Arc<str>) -> Result<Scope, RawParseError> {
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
        let (role, tail) = build_variable_def(vd)?;
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
fn build_variable_def(pair: Pair<'_>) -> Result<(String, ScopeTail), RawParseError> {
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
                let result = build_expr(expr);
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

fn build_cond(pair: Pair<'_>) -> Result<Cond, RawParseError> {
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
            Rule::extension_marker => body = Some(build_extension_marker(child)?),
            // The untagged form `when { <expr> }` — a structured Cedar
            // expression (which may itself contain markers as primaries).
            Rule::expr => body = Some(build_expr(child)?),
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
fn build_extension_marker(pair: Pair<'_>) -> Result<Expr, RawParseError> {
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
        Some(Dialect::Temporal) => crate::extension::temporal::Temporal::parse(&inner, inner_span)
            .map(Extension::Temporal)
            .map_err(|msg| err(msg, inner_span))?,
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
fn build_expr(pair: Pair<'_>) -> Result<Expr, RawParseError> {
    let inner = pair.into_inner().next().expect("expr has one alternative");
    match inner.as_rule() {
        Rule::if_expr => build_if(inner),
        Rule::or => build_or(inner),
        other => unreachable!("unexpected expr child: {other:?}"),
    }
}

/// `if_expr := if expr then expr else expr`.
fn build_if(pair: Pair<'_>) -> Result<Expr, RawParseError> {
    let span = span_of(&pair);
    let mut exprs = pair.into_inner().filter(|p| p.as_rule() == Rule::expr);
    let cond = build_expr(exprs.next().expect("if condition"))?;
    let then_expr = build_expr(exprs.next().expect("then branch"))?;
    let else_expr = build_expr(exprs.next().expect("else branch"))?;
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
fn build_or(pair: Pair<'_>) -> Result<Expr, RawParseError> {
    let span = chain_span(&pair);
    let mut iter = pair.into_inner().filter(|p| p.as_rule() == Rule::and);
    let mut acc = build_and(iter.next().expect("or has an and"))?;
    for next in iter {
        let right = build_and(next)?;
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
fn build_and(pair: Pair<'_>) -> Result<Expr, RawParseError> {
    let span = chain_span(&pair);
    let mut iter = pair.into_inner().filter(|p| p.as_rule() == Rule::rel);
    let mut acc = build_rel(iter.next().expect("and has a rel"))?;
    for next in iter {
        let right = build_rel(next)?;
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
fn build_rel(pair: Pair<'_>) -> Result<Expr, RawParseError> {
    let span = span_of(&pair);
    let rel_chain_span = chain_span(&pair);
    let mut iter = pair.into_inner();
    let lhs = build_add(iter.next().expect("rel has an add"))?;
    match iter.next() {
        None => Ok(lhs),
        Some(tail) => match tail.as_rule() {
            Rule::rel_op_tail => build_rel_op_tail(lhs, tail, rel_chain_span),
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
            Rule::is_tail => build_is_tail(lhs, tail, span),
            other => unreachable!("unexpected rel tail: {other:?}"),
        },
    }
}

/// `rel_op_tail := (rel_op add)+` — a chain of comparisons, folded left.
/// `span` is the enclosing `rel` chain span (see [`chain_span`]); Cedar
/// stamps every node of the relation chain with it.
fn build_rel_op_tail(lhs: Expr, pair: Pair<'_>, span: Span) -> Result<Expr, RawParseError> {
    let mut acc = lhs;
    let mut iter = pair.into_inner().peekable();
    while let Some(op_pair) = iter.next() {
        debug_assert_eq!(op_pair.as_rule(), Rule::rel_op);
        let op = parse_rel_op(&op_pair)?;
        let add = iter.next().expect("rel_op is followed by an add");
        let right = build_add(add)?;
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
fn build_is_tail(lhs: Expr, pair: Pair<'_>, span: Span) -> Result<Expr, RawParseError> {
    let mut adds = pair.into_inner().filter(|p| p.as_rule() == Rule::add);
    let type_add = adds.next().expect("is has a type operand");
    let entity_type = extract_entity_type(type_add, span)?;
    let in_expr = match adds.next() {
        Some(add) => Some(Box::new(build_add(add)?)),
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
fn build_add(pair: Pair<'_>) -> Result<Expr, RawParseError> {
    let span = chain_span(&pair);
    let mut iter = pair.into_inner().peekable();
    let mut acc = build_mult(iter.next().expect("add has a mult"))?;
    while let Some(op_pair) = iter.next() {
        debug_assert_eq!(op_pair.as_rule(), Rule::add_op);
        let op = match op_pair.as_str().trim() {
            "+" => BinOp::Add,
            "-" => BinOp::Sub,
            other => unreachable!("unexpected add_op `{other}`"),
        };
        let right = build_mult(iter.next().expect("add_op followed by mult"))?;
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
fn build_mult(pair: Pair<'_>) -> Result<Expr, RawParseError> {
    let span = chain_span(&pair);
    let mut iter = pair.into_inner().peekable();
    let mut acc = build_unary(iter.next().expect("mult has a unary"))?;
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
        let right = build_unary(iter.next().expect("mult_op followed by unary"))?;
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
fn build_unary(pair: Pair<'_>) -> Result<Expr, RawParseError> {
    // The unary node's span is the whole `unary` production, trivia-trimmed —
    // paren-inclusive on the operand (`!(x)` ends at the `)`), matching Cedar.
    let unary_span = chain_span(&pair);
    let mut prefix: Option<(UnOp, usize)> = None;
    let mut member_pair = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::bang_run => prefix = Some((UnOp::Not, child.as_str().matches('!').count())),
            Rule::dash_run => prefix = Some((UnOp::Neg, child.as_str().matches('-').count())),
            Rule::member => member_pair = Some(child),
            _ => {}
        }
    }
    let member_pair = member_pair.expect("unary has a member");

    // Detect if the member is a bare number literal `9223372036854775808`
    // (the 2^63 special case). This literal is stored as Long(i64::MIN)
    // by build_literal; the first negation prefix is its sign. We must
    // only absorb that negation when it's a direct literal — NOT when the
    // i64::MIN comes from a parenthesized sub-expression like
    // `-((-9223372036854775808))`, which must overflow at runtime, and NOT
    // when 9223372036854775808 appears nested inside a list/record/call.
    //
    // We inspect the parse tree (member_pair) rather than the built Expr
    // because after build_member both cases produce Long(i64::MIN) and
    // are indistinguishable.
    let is_bare_2_63 = prefix.as_ref().is_some_and(|(op, _)| *op == UnOp::Neg)
        && is_member_bare_number(&member_pair, "9223372036854775808");
    // Only a *directly* negated number token folds (`-5` ⇒ `Long(-5)`); a
    // parenthesized `-(5)` keeps a `Neg` over the positive literal, matching
    // Cedar's own constant-folding (and its span attribution).
    let member_is_bare_number = bare_number_text(&member_pair).is_some();

    let mut expr = build_member(member_pair)?;
    if let Some((op, mut count)) = prefix {
        // If the member is the bare 2^63 literal, absorb one negation:
        // `Long(i64::MIN)` is already the correct value for `-2^63`.
        if is_bare_2_63 && count > 0 {
            count -= 1;
        }
        for _ in 0..count {
            // Fold negation on integer literals: `-N` becomes `Long(-N)`
            // directly rather than `UnaryApp(Neg, Long(N))` — but only for a
            // *direct* numeric token, so `-(N)` stays a `Neg`. Keep the
            // literal's own (number-token) span — Cedar spans the digits, not
            // the leading `-`, so preserving `expr.span` matches Cedar's own
            // attribution rather than widening to the whole unary span.
            if op == UnOp::Neg
                && member_is_bare_number
                && let ExprKind::Lit(cedar_ast::Literal::Long(n)) = &expr.kind
            {
                let n = *n;
                if n != i64::MIN {
                    let lit_span = expr.span;
                    expr = Expr::new(ExprKind::Lit(cedar_ast::Literal::Long(-n)), lit_span);
                    continue;
                }
                // n == i64::MIN: do NOT fold — emit UnaryApp(Neg) so
                // Cedar's evaluator produces an overflow error at
                // runtime.
            }
            expr = Expr::new(
                ExprKind::UnaryApp {
                    op,
                    expr: Box::new(expr),
                },
                unary_span,
            );
        }
    }
    Ok(expr)
}

/// `member := primary { mem_access }`. Folds attribute access, index
/// access, function calls (`decimal(x)`), and method calls
/// (`xs.contains(y)`) onto the base. Each `mem_access` wraps one of
/// `access_field` / `access_call` / `access_index`.
fn build_member(pair: Pair<'_>) -> Result<Expr, RawParseError> {
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
            build_function_call(&name, call)?
        } else {
            build_primary(primary)?
        };

    while let Some(acc) = iter.next() {
        match acc.as_rule() {
            Rule::access_field => {
                let field = field_name(&acc);
                // `.method(args)` when a call follows the field access.
                if iter.peek().map(|p| p.as_rule()) == Some(Rule::access_call) {
                    let call = iter.next().expect("peeked call");
                    base = build_method_call(base, &field, call, member_span.start)?;
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
        .unwrap_or_else(|| pair.as_str().trim_start_matches('.').trim().to_string())
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
        Some(s) => Ok(s),
        None => Err(err(
            "index access requires a string-literal key, e.g. `record[\"field\"]`",
            span,
        )),
    }
}

/// If `expr` is exactly a string literal, return its decoded value.
fn string_literal_of(expr: &Pair<'_>) -> Option<String> {
    // expr → or → and → rel → add → mult → unary → member → primary →
    // literal → string. Walk the single-child chain; bail if it branches.
    let mut cur = expr.clone();
    loop {
        let rule = cur.as_rule();
        if rule == Rule::string {
            return Some(decode_string(cur.as_str()));
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
fn build_function_call(name_pair: &Pair<'_>, call: Pair<'_>) -> Result<Expr, RawParseError> {
    // Span the whole application (`name(...)`), from the function name
    // through the closing paren of the call.
    let span = Span::new(span_of(name_pair).start, span_of(&call).end);
    let fname = name_pair.as_str().trim();
    let mut args = call_args(call)?;
    let op = match fname {
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
    Ok(Expr::new(
        ExprKind::Call {
            name: fname.to_string(),
            args,
        },
        span,
    ))
}

/// Method application: `xs.contains(y)`, `d.lessThan(e)`, `s.isEmpty()`.
fn build_method_call(
    receiver: Expr,
    method: &str,
    call: Pair<'_>,
    member_start: usize,
) -> Result<Expr, RawParseError> {
    // The node spans from the enclosing member's start (so a parenthesized
    // receiver's `(` is included, as Cedar does) through the call's closing
    // paren.
    let node_span = Span::new(member_start, span_of(&call).end);
    let mut args = call_args(call)?;

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
fn call_args(call: Pair<'_>) -> Result<Vec<Expr>, RawParseError> {
    call.into_inner()
        .filter(|p| p.as_rule() == Rule::expr)
        .map(build_expr)
        .collect()
}

/// `primary := extension_marker | literal | slot | ref_ | name |
/// paren_expr | list | record`.
fn build_primary(pair: Pair<'_>) -> Result<Expr, RawParseError> {
    let span = span_of(&pair);
    let inner = pair.into_inner().next().expect("primary has a child");
    match inner.as_rule() {
        Rule::extension_marker => build_extension_marker(inner),
        Rule::literal => Ok(Expr::new(ExprKind::Lit(build_literal(&inner)?), span)),
        Rule::slot => build_slot(&inner),
        Rule::ref_ => Ok(Expr::new(ExprKind::Lit(build_ref(inner)?), span)),
        Rule::name => resolve_name(&inner),
        Rule::paren_expr => {
            let e = inner
                .into_inner()
                .find(|p| p.as_rule() == Rule::expr)
                .expect("paren has an expr");
            build_expr(e)
        }
        Rule::list => {
            let elems = inner
                .into_inner()
                .filter(|p| p.as_rule() == Rule::expr)
                .map(build_expr)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::new(ExprKind::Set(elems), span))
        }
        Rule::record => build_record(inner, span),
        other => unreachable!("unexpected primary child: {other:?}"),
    }
}

/// Resolve a bare `name` in value position: one of the four request
/// variables, or an error (bare names are otherwise only valid as entity
/// types or function names, handled elsewhere).
fn resolve_name(pair: &Pair<'_>) -> Result<Expr, RawParseError> {
    let s = pair.as_str().trim();
    let var = match s {
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
            // Parse as u64 first (matching Cedar's grammar). Cedar's lexer
            // treats all numeric literals as unsigned; negation is a unary
            // operator applied in build_unary. The one u64 value that
            // doesn't fit i64 is 2^63 — valid only as (-2^63) = i64::MIN.
            let n = inner.as_str().parse::<u64>().map_err(|_| {
                err(
                    format!("integer literal `{}` is out of range", inner.as_str()),
                    span_of(&inner),
                )
            })?;
            match i64::try_from(n) {
                Ok(i) => Ok(cedar_ast::Literal::Long(i)),
                Err(_) if n == 9223372036854775808 => {
                    // 2^63: only valid under negation (becomes i64::MIN).
                    // Store as i64::MIN directly; build_unary will absorb
                    // the negation rather than wrapping in UnaryApp(Neg).
                    Ok(cedar_ast::Literal::Long(i64::MIN))
                }
                Err(_) => Err(err(
                    format!("integer literal `{}` is out of range", inner.as_str()),
                    span_of(&inner),
                )),
            }
        }
        Rule::string => Ok(cedar_ast::Literal::String(
            decode_string(inner.as_str()).into(),
        )),
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
            Rule::name => name = Some(child.as_str().to_string()),
            Rule::string => eid = Some(decode_string(child.as_str())),
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
    let segments = name_segments(&name);
    let ty = make_entity_type(&segments, span)?;
    let uid = cedar_ast::EntityUID::from_components(ty, cedar_ast::Eid::new(eid), None);
    Ok(cedar_ast::Literal::EntityUID(std::sync::Arc::new(uid)))
}

/// `record := "{" [ rec_init { "," rec_init } ] "}"`.
fn build_record(pair: Pair<'_>, span: Span) -> Result<Expr, RawParseError> {
    let mut map = std::collections::BTreeMap::new();
    for init in pair.into_inner().filter(|p| p.as_rule() == Rule::rec_init) {
        let inner = init.into_inner().next().expect("rec_init has a child");
        match inner.as_rule() {
            Rule::rec_init_if => {
                let value = inner
                    .into_inner()
                    .find(|p| p.as_rule() == Rule::expr)
                    .expect("rec_init_if has a value");
                map.insert("if".to_string(), build_expr(value)?);
            }
            Rule::rec_init_expr => {
                let mut exprs = inner.into_inner().filter(|p| p.as_rule() == Rule::expr);
                let key_pair = exprs.next().expect("record key");
                let value_pair = exprs.next().expect("record value");
                let key = record_key(&key_pair, span)?;
                map.insert(key, build_expr(value_pair)?);
            }
            other => unreachable!("unexpected rec_init child: {other:?}"),
        }
    }
    Ok(Expr::new(ExprKind::Record(map), span))
}

/// A record key is a string literal or a bare identifier.
fn record_key(expr: &Pair<'_>, span: Span) -> Result<String, RawParseError> {
    if let Some(s) = string_literal_of(expr) {
        return Ok(s);
    }
    // Otherwise expect a bare identifier (a single-segment name).
    let text = expr.as_str().trim();
    if !text.is_empty() && !text.contains(|c: char| c.is_whitespace() || c == ':') {
        return Ok(text.to_string());
    }
    Err(err(
        "record keys must be identifiers or string literals",
        span,
    ))
}

// ── Name / entity-type helpers ──────────────────────────────────────

/// Split a `::`-qualified name into its segments.
fn name_segments(name: &str) -> Vec<String> {
    name.split("::").map(|s| s.trim().to_string()).collect()
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
/// name, so we read its dotted/`::`-qualified name rather than evaluating
/// it as a value.
fn extract_entity_type(add: Pair<'_>, span: Span) -> Result<cedar_ast::EntityType, RawParseError> {
    let text = add.as_str().trim();
    let segments = name_segments(text);
    make_entity_type(&segments, span)
}

/// Extract the attribute path of a `has_tail` (`has output`,
/// `has a.b.c`, `has if.x`).
fn extract_has_path(tail: Pair<'_>) -> Result<Vec<String>, RawParseError> {
    let span = span_of(&tail);
    let rhs = tail
        .into_inner()
        .find(|p| p.as_rule() == Rule::has_rhs)
        .ok_or_else(|| err("`has` is missing an attribute", span))?;
    let inner = rhs.into_inner().next().expect("has_rhs has a child");
    match inner.as_rule() {
        // `has if` followed by `.x.y` field accesses.
        Rule::has_if_rhs => {
            let mut attrs = vec!["if".to_string()];
            for acc in inner
                .into_inner()
                .filter(|p| p.as_rule() == Rule::mem_access)
            {
                if let Some(field) = acc.into_inner().find(|p| p.as_rule() == Rule::access_field) {
                    attrs.push(field_name(&field));
                }
            }
            Ok(attrs)
        }
        // A normal `add`: a member whose primary name is the first attr,
        // with `.field` accesses for the rest.
        Rule::add => extract_attr_path(inner, span),
        other => unreachable!("unexpected has_rhs child: {other:?}"),
    }
}

/// Read a dotted attribute path (`a.b.c`) from an `add` subtree.
/// Also accepts a string literal as the first attribute (`has "attr"`),
/// matching Cedar's grammar which allows quoted attribute names.
fn extract_attr_path(add: Pair<'_>, span: Span) -> Result<Vec<String>, RawParseError> {
    // Drill to the single `member`.
    let member = find_descendant(add, Rule::member)
        .ok_or_else(|| err("expected an attribute path", span))?;
    let mut attrs = Vec::new();
    for child in member.into_inner() {
        match child.as_rule() {
            Rule::primary => {
                // Try bare identifier first, then fall back to string literal.
                if let Some(name) = find_descendant(child.clone(), Rule::name) {
                    attrs.push(name.as_str().trim().to_string());
                } else if let Some(lit) = find_descendant(child.clone(), Rule::literal) {
                    if let Some(s) = find_descendant(lit, Rule::string) {
                        attrs.push(decode_string(s.as_str()));
                    } else {
                        return Err(err("expected an attribute name", span));
                    }
                } else {
                    return Err(err("expected an attribute name", span));
                }
            }
            Rule::mem_access => {
                if let Some(field) = child
                    .into_inner()
                    .find(|p| p.as_rule() == Rule::access_field)
                {
                    attrs.push(field_name(&field));
                }
            }
            _ => {}
        }
    }
    if attrs.is_empty() {
        return Err(err("expected an attribute name", span));
    }
    Ok(attrs)
}

/// Find the first descendant pair with the given rule (depth-first),
/// descending only through single-child chains plus direct children.
fn find_descendant(pair: Pair<'_>, rule: Rule) -> Option<Pair<'_>> {
    if pair.as_rule() == rule {
        return Some(pair);
    }
    for child in pair.into_inner() {
        if let Some(found) = find_descendant(child, rule) {
            return Some(found);
        }
    }
    None
}

/// Check if a `member` parse-tree node is exactly a bare numeric literal
/// with the given text value — no parentheses, no method calls, no
/// indexing, no nesting inside lists/records. This is used to identify
/// the raw token `9223372036854775808` that needs one negation absorbed
/// vs the same value arriving from a sub-expression.
fn is_member_bare_number(member_pair: &Pair<'_>, expected_text: &str) -> bool {
    bare_number_text(member_pair).is_some_and(|t| t == expected_text)
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
fn extract_pattern(
    add: Pair<'_>,
    span: Span,
) -> Result<Vec<cedar_ast::PatternElem>, RawParseError> {
    // Find the raw string token so we can see the escapes verbatim.
    let add_str = add.as_str().trim();
    let string = find_descendant(add, Rule::string).ok_or_else(|| {
        err(
            format!("`like` requires a string-literal pattern, but got `{add_str}`"),
            span,
        )
    })?;
    let raw = string.as_str();
    // Strip the surrounding quotes.
    let body = &raw[1..raw.len().saturating_sub(1)];
    Ok(build_pattern(body))
}

/// Convert a `like` pattern body (quotes already stripped, escapes
/// intact) into Cedar pattern elements.
fn build_pattern(body: &str) -> Vec<cedar_ast::PatternElem> {
    let mut out = Vec::new();
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '*' => out.push(cedar_ast::PatternElem::Wildcard),
            '\\' => {
                match chars.next() {
                    Some('*') => out.push(cedar_ast::PatternElem::Char('*')),
                    Some('\\') => out.push(cedar_ast::PatternElem::Char('\\')),
                    Some('n') => out.push(cedar_ast::PatternElem::Char('\n')),
                    Some('t') => out.push(cedar_ast::PatternElem::Char('\t')),
                    Some('r') => out.push(cedar_ast::PatternElem::Char('\r')),
                    Some('0') => out.push(cedar_ast::PatternElem::Char('\0')),
                    Some('"') => out.push(cedar_ast::PatternElem::Char('"')),
                    Some('\'') => out.push(cedar_ast::PatternElem::Char('\'')),
                    Some('u') => {
                        // `\u{HEX}` — unicode escape.
                        if chars.peek() == Some(&'{') {
                            chars.next();
                            let mut hex = String::new();
                            let mut saw_close = false;
                            while let Some(&d) = chars.peek() {
                                if d == '}' {
                                    chars.next();
                                    saw_close = true;
                                    break;
                                }
                                hex.push(d);
                                chars.next();
                            }
                            let decoded = if saw_close {
                                u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32)
                            } else {
                                None
                            };
                            match decoded {
                                Some(c) => out.push(cedar_ast::PatternElem::Char(c)),
                                None => {
                                    // Malformed: pass through as literal chars.
                                    out.push(cedar_ast::PatternElem::Char('\\'));
                                    out.push(cedar_ast::PatternElem::Char('u'));
                                    out.push(cedar_ast::PatternElem::Char('{'));
                                    for ch in hex.chars() {
                                        out.push(cedar_ast::PatternElem::Char(ch));
                                    }
                                    if saw_close {
                                        out.push(cedar_ast::PatternElem::Char('}'));
                                    }
                                }
                            }
                        } else {
                            out.push(cedar_ast::PatternElem::Char('\\'));
                            out.push(cedar_ast::PatternElem::Char('u'));
                        }
                    }
                    Some(other) => out.push(cedar_ast::PatternElem::Char(other)),
                    None => out.push(cedar_ast::PatternElem::Char('\\')),
                }
            }
            other => out.push(cedar_ast::PatternElem::Char(other)),
        }
    }
    out
}

/// Decode a string literal token (including surrounding quotes) into its
/// value. Handles the standard Cedar escapes; the value (not the exact
/// spelling) is what matters for lowering, since the `cedar_ast::Literal`
/// re-encodes on `Display`.
fn decode_string(raw: &str) -> String {
    let body = &raw[1..raw.len().saturating_sub(1)];
    let mut out = String::with_capacity(body.len());
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            Some('0') => out.push('\0'),
            Some('\\') => out.push('\\'),
            Some('"') => out.push('"'),
            Some('\'') => out.push('\''),
            Some('*') => out.push('*'),
            Some('u') => {
                // `\u{HEX}` — parse the braced hex; pass through if malformed.
                if chars.peek() == Some(&'{') {
                    chars.next();
                    let mut hex = String::new();
                    while let Some(&d) = chars.peek() {
                        if d == '}' {
                            chars.next();
                            break;
                        }
                        hex.push(d);
                        chars.next();
                    }
                    match u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32) {
                        Some(decoded) => out.push(decoded),
                        None => {
                            out.push_str("\\u{");
                            out.push_str(&hex);
                            out.push('}');
                        }
                    }
                } else {
                    out.push('\\');
                    out.push('u');
                }
            }
            Some(other) => {
                out.push('\\');
                out.push(other);
            }
            None => out.push('\\'),
        }
    }
    out
}

#[cfg(test)]
mod macro_parse_smoke {
    //! Smoke tests verifying that `def cedar` / `def temporal`
    //! declarations parse into [`PolicySet::defs`] (Phase 1 — no
    //! expansion yet). Lives next to the parser since the AST and the
    //! `parse_policies` entry are crate-private.

    use super::*;
    use crate::ast::ExprKind;
    use crate::extension::temporal::ast::{AggExprKind, ConditionKind};

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
            MacroBody::TemporalAgg(agg) => match &agg.kind {
                AggExprKind::Count { .. } => {}
                other => panic!("expected Count, got {other:?}"),
            },
            other => panic!("expected TemporalAgg body, got {other:?}"),
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
            MacroBody::TemporalAgg(agg) => match &agg.kind {
                AggExprKind::Sum { .. } => {}
                other => panic!("expected Sum, got {other:?}"),
            },
            other => panic!("expected TemporalAgg body, got {other:?}"),
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
