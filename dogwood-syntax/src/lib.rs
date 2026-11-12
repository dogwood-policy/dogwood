//! Shared, source-preserving syntax support for Dogwood (`.dw`) policy files.
//!
//! This crate owns the policy grammar used by the semantic parser and exposes
//! the lossless token stream and structural spans needed by the formatter.
//! It deliberately stops before AST construction, macro expansion, schema
//! resolution, or any other semantic operation.

use pest::Parser as _;

mod generated {
    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "grammar.pest"]
    pub(super) struct DogwoodParser;
}

#[doc(hidden)]
pub use generated::Rule;

/// A byte range `[start, end)` in Dogwood source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { start, end }
    }

    pub fn contains(self, other: Span) -> bool {
        self.start <= other.start && other.end <= self.end
    }

    pub fn text(self, source: &str) -> &str {
        &source[self.start..self.end]
    }
}

/// A pair produced by the shared Dogwood policy grammar.
#[doc(hidden)]
pub type Pair<'source> = pest::iterators::Pair<'source, Rule>;

/// The pairs produced by the shared Dogwood policy grammar.
#[doc(hidden)]
pub type Pairs<'source> = pest::iterators::Pairs<'source, Rule>;

/// The default limit on the depth of the tree the parser will build.
///
/// One limit bounds every kind of depth. The parser and its passes count the
/// levels of the tree they build, macro expansion included, temporal blocks
/// included, and reject a tree deeper than the limit before they build it.
/// The generated parsers cannot count their own recursion, so a lexical scan
/// over-estimates it before each runs; see [`nesting_depth_error`].
///
/// The default is 32, and at the default exceeding the limit is a parse
/// error, never a stack overflow. Real policies measure at most 9 levels of
/// nesting and 16 of expression depth. The default is what parses, expands,
/// lowers, and validates on a 2 MiB thread stack in a debug build with
/// headroom, which a test enforces; at the default a text parses identically
/// on every host, thread, and build profile.
///
/// [`ParseOptions::max_depth`] sets another limit. A caller who raises it owns
/// the stack that later passes over the deeper trees need: the generated
/// parser and builder cost on the order of tens of KiB of stack per bracket
/// level in a debug build (measured at about 34 KiB), and the no-overflow
/// guarantee holds at the default only.
pub const DEFAULT_MAX_DEPTH: usize = 32;

/// Options for parsing Dogwood text.
///
/// `ParseOptions::default()` is what every entry point without an options
/// parameter uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct ParseOptions {
    /// The deepest finished tree the frontend returns — measured at each
    /// tree-producing boundary with an explicit-stack walker — and the
    /// deepest nesting the lexical scan admits; [`DEFAULT_MAX_DEPTH`] by
    /// default.
    ///
    /// Any value is accepted, larger than the default included. The default is
    /// what parses, expands, lowers, and validates on a 2 MiB thread stack in
    /// a debug build with headroom, which a test enforces, and the guarantee
    /// that too-deep text is a parse error rather than a stack overflow holds
    /// at the default. A caller who raises the limit owns the stack that the
    /// deeper trees need: the builder costs on the order of tens of KiB of
    /// stack per level in a debug build (measured at about 34 KiB per bracket
    /// level). A limit of 0 is accepted and admits no bracket and no
    /// operand-introducing keyword, so it rejects every policy.
    pub max_depth: usize,
    /// The most tree nodes (`Expr`, temporal `Condition`, `Term`, and
    /// aggregation nodes) that macro expansion may create for one parsed
    /// policy set, and, separately, that lowering may create for that set's
    /// temporal leaves; [`DEFAULT_MAX_NODES`] by default.
    ///
    /// Exceeding it is an error ("macro expansion exceeds the node budget of
    /// …" or "lowering exceeds the node budget of …") at the macro call or
    /// temporal leaf that exhausted it, raised before the excess is built, so
    /// the limit bounds the memory expansion and lowering use. Nodes are
    /// counted as they are allocated; nodes later dropped are not credited
    /// back. Any value is accepted. A caller who raises the limit owns the
    /// memory and time the larger trees need; a small limit rejects real
    /// policies.
    pub max_nodes: usize,
}

impl Default for ParseOptions {
    fn default() -> Self {
        ParseOptions {
            max_depth: DEFAULT_MAX_DEPTH,
            max_nodes: DEFAULT_MAX_NODES,
        }
    }
}

impl ParseOptions {
    /// These options with [`max_depth`](ParseOptions::max_depth) set to `n`.
    pub fn max_depth(self, n: usize) -> Self {
        ParseOptions {
            max_depth: n,
            ..self
        }
    }

    /// These options with [`max_nodes`](ParseOptions::max_nodes) set to `n`.
    pub fn max_nodes(self, n: usize) -> Self {
        ParseOptions {
            max_nodes: n,
            ..self
        }
    }
}

/// The policy grammar's keywords that introduce an operand, for
/// [`nesting_depth_error`]: `if`, whose condition and branches are
/// expressions that may be `if`s.
pub const POLICY_NESTING_KEYWORDS: &[&str] = &["if"];

/// [`parse_with`] at the default [`ParseOptions`].
#[doc(hidden)]
pub fn parse(rule: Rule, source: &str) -> Result<Pairs<'_>, pest::error::Error<Rule>> {
    parse_with(rule, source, &ParseOptions::default())
}

/// Parse `source` starting at a rule from the shared Dogwood policy grammar.
///
/// Most callers should use [`parse_document`]. This lower-level entry point is
/// exposed for the semantic parser, which also parses standalone Cedar macro
/// bodies with `Rule::expr_entry`.
///
/// Source nested deeper than `options.max_depth`, as [`nesting_depth_error`]
/// counts it, is a parse error located at the first bracket or `if` beyond
/// the limit.
#[doc(hidden)]
pub fn parse_with<'source>(
    rule: Rule,
    source: &'source str,
    options: &ParseOptions,
) -> Result<Pairs<'source>, pest::error::Error<Rule>> {
    if let Some(error) = nesting_depth_error(source, POLICY_NESTING_KEYWORDS, options.max_depth) {
        return Err(error);
    }
    generated::DogwoodParser::parse(rule, source)
}

/// The default limit on the number of tree nodes macro expansion and lowering
/// may create for one parsed policy set.
///
/// Nesting depth does not bound a tree's size: a macro whose body mentions its
/// parameter twice, called on its own result, doubles the tree at every level,
/// and so does lowering a nested `previous` or `since`. So macro expansion and
/// lowering count the nodes they create (`Expr`, temporal `Condition`, `Term`,
/// and aggregation nodes) and stop with an ordinary error before they allocate
/// the excess.
///
/// The limit is per parsed policy set: it is the most nodes macro expansion
/// may create for the whole set, and, separately, the most nodes lowering may
/// create for that set's temporal leaves. The count is of allocations: a node
/// created and later dropped is never credited back.
///
/// The default is 1,000,000. Over the policies in this repository's tests, the
/// most any macro expansion needs for one condition is 117 nodes and the most
/// any lowering needs for one temporal leaf is 449, so the default covers a
/// set of about 2,000 such worst-case policies. A typical leaf is far
/// smaller: `Read since within 1h Write` lowers to about 105 nodes, so a set
/// of about 9,500 such policies fits. A caller that loads larger sets passes
/// a larger limit.
///
/// [`ParseOptions::max_nodes`] sets another limit, and any value is accepted.
/// A caller who raises it owns the memory the larger trees need, and the time
/// to build them.
pub const DEFAULT_MAX_NODES: usize = 1_000_000;

/// What is left of a [`ParseOptions::max_nodes`] budget while a pass builds a
/// tree.
///
/// A pass charges each node before it creates it, and a subtree's node count
/// before it clones the subtree; a charge the budget cannot cover fails, and
/// the pass reports its own error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeBudget {
    limit: usize,
    remaining: usize,
}

/// A [`NodeBudget`] charge that the budget could not cover.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BudgetExhausted;

impl NodeBudget {
    /// A full budget of `limit` nodes.
    pub fn new(limit: usize) -> Self {
        NodeBudget {
            limit,
            remaining: limit,
        }
    }

    /// The limit this budget started from.
    pub fn limit(&self) -> usize {
        self.limit
    }

    /// Spend `n` nodes, or fail, spending nothing, if fewer than `n` remain.
    pub fn charge(&mut self, n: usize) -> Result<(), BudgetExhausted> {
        self.remaining = self.remaining.checked_sub(n).ok_or(BudgetExhausted)?;
        Ok(())
    }
}

/// The parse error for `source` nested deeper than `max_depth`, or `None` if
/// it is within the limit.
///
/// This over-estimates a generated parser's recursion; it does not measure a
/// tree. Each open bracket (`(`, `[`, `{`) and each of `keywords`, the words
/// that introduce an operand, adds a level, and only a closing bracket
/// subtracts: it closes its own level and every keyword counted inside it. A
/// keyword therefore stays counted until the bracket enclosing it closes, so
/// sibling keywords in one bracket level accumulate, even when separated by
/// `,`, `;`, or an operator. [`nesting_estimate`] is the deepest level the
/// scan reaches, the number compared against `max_depth`.
///
/// The scan is lexical: brackets and keywords inside a string literal or a
/// `//` comment do not count. A keyword counts wherever it appears as a whole
/// identifier outside strings and comments, whatever byte precedes it, so a
/// field or a name spelled like a keyword (`x.if`, `?if`, `$if`) is charged a
/// level: an over-approximation by design, since a binder list's `.` would
/// otherwise hide the keyword after it. A `"` with no closing quote does not
/// start a string, so the text after it still counts. Generic over the rule
/// type so that any grammar sharing these bracket, string, and comment
/// conventions can apply the same guard before parsing.
pub fn nesting_depth_error<R: pest::RuleType>(
    source: &str,
    keywords: &[&str],
    max_depth: usize,
) -> Option<pest::error::Error<R>> {
    let offset = nesting_violation(source, keywords, max_depth)?;
    let position = pest::Position::new(source, offset).expect("an ASCII byte is a char boundary");
    Some(pest::error::Error::new_from_pos(
        pest::error::ErrorVariant::CustomError {
            message: format!("nesting exceeds the maximum depth of {max_depth}"),
        },
        position,
    ))
}

/// The deepest level the scan of [`nesting_depth_error`] reaches in `source`:
/// the number it compares against the limit, which rejects `source` exactly
/// when this exceeds it.
pub fn nesting_estimate(source: &str, keywords: &[&str]) -> usize {
    match nesting_scan(source, keywords, usize::MAX) {
        Ok(deepest) => deepest,
        Err(_) => unreachable!("the scan's level never exceeds the number of bytes"),
    }
}

/// The byte offset of the first opener beyond `max_depth`.
fn nesting_violation(source: &str, keywords: &[&str], max_depth: usize) -> Option<usize> {
    nesting_scan(source, keywords, max_depth).err()
}

/// The scan behind [`nesting_depth_error`] and [`nesting_estimate`]: the
/// deepest level reached, or the byte offset of the first opener that takes
/// the level beyond `max_depth`.
fn nesting_scan(source: &str, keywords: &[&str], max_depth: usize) -> Result<usize, usize> {
    let bytes = source.as_bytes();
    // One entry per open bracket, plus the outermost level: the number of
    // keywords counted at that level, released when its bracket closes.
    let mut open_keywords = vec![0usize];
    let mut depth = 0usize;
    let mut deepest = 0usize;
    let mut index = 0;
    while index < bytes.len() {
        let byte = bytes[index];
        match byte {
            b'"' => {
                if let Some(len) = string_end(&source[index..]) {
                    index += len;
                    continue;
                }
            }
            b'/' if bytes.get(index + 1) == Some(&b'/') => {
                index += source[index..]
                    .find(['\n', '\r'])
                    .unwrap_or(bytes.len() - index);
                continue;
            }
            b'(' | b'[' | b'{' => {
                depth += 1;
                if depth > max_depth {
                    return Err(index);
                }
                deepest = deepest.max(depth);
                open_keywords.push(0);
            }
            b')' | b']' | b'}' => {
                if open_keywords.len() > 1 {
                    depth -= open_keywords.pop().expect("checked non-empty") + 1;
                }
            }
            _ if is_ident_byte(byte) => {
                let len = bytes[index..]
                    .iter()
                    .take_while(|byte| is_ident_byte(**byte))
                    .count();
                let word = &source[index..index + len];
                if keywords.contains(&word) {
                    depth += 1;
                    if depth > max_depth {
                        return Err(index);
                    }
                    deepest = deepest.max(depth);
                    *open_keywords
                        .last_mut()
                        .expect("outermost level is never popped") += 1;
                }
                index += len;
                continue;
            }
            _ => {}
        }
        index += 1;
    }
    Ok(deepest)
}

fn is_ident_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// Split an optional UTF-8 byte-order mark from the policy text.
///
/// Returned spans and tokens are relative to `source_without_bom`.
pub fn split_bom(source: &str) -> (&str, &str) {
    match source.strip_prefix('\u{feff}') {
        Some(rest) => ("\u{feff}", rest),
        None => ("", source),
    }
}

/// A lossless lexical token category.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Whitespace,
    Comment,
    String,
    Identifier,
    Number,
    Symbol,
    Other,
}

/// One lossless source token.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'source> {
    pub kind: TokenKind,
    pub text: &'source str,
    pub span: Span,
}

impl Token<'_> {
    pub fn is_whitespace(self) -> bool {
        self.kind == TokenKind::Whitespace
    }

    pub fn is_comment(self) -> bool {
        self.kind == TokenKind::Comment
    }
}

/// The only lexical failure possible without interpreting the grammar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnterminatedString {
    pub span: Span,
}

/// Tokenize the complete source without discarding any byte.
pub fn tokenize(source: &str) -> Result<Vec<Token<'_>>, UnterminatedString> {
    let mut tokens = Vec::new();
    let mut index = 0;

    while index < source.len() {
        let rest = &source[index..];
        let first = rest.chars().next().expect("index is inside source");

        let (kind, len) = if first.is_whitespace() {
            (TokenKind::Whitespace, take_while(rest, char::is_whitespace))
        } else if first == '"' {
            (
                TokenKind::String,
                string_end(rest).ok_or(UnterminatedString {
                    span: Span::new(index, source.len()),
                })?,
            )
        } else if rest.starts_with("//") {
            (
                TokenKind::Comment,
                rest.find(['\n', '\r']).unwrap_or(rest.len()),
            )
        } else if first.is_ascii_alphabetic() || first == '_' {
            (
                TokenKind::Identifier,
                take_while(rest, |character| {
                    character.is_ascii_alphanumeric() || character == '_'
                }),
            )
        } else if first.is_ascii_digit() {
            (
                TokenKind::Number,
                take_while(rest, |character| character.is_ascii_digit()),
            )
        } else if let Some(len) = symbol_len(rest) {
            (TokenKind::Symbol, len)
        } else {
            let len = take_while(rest, |character| {
                !character.is_whitespace()
                    && character != '"'
                    && !character.is_ascii_alphanumeric()
                    && character != '_'
                    && symbol_len_at(character).is_none()
            });
            (TokenKind::Other, len.max(first.len_utf8()))
        };

        tokens.push(Token {
            kind,
            text: &source[index..index + len],
            span: Span::new(index, index + len),
        });
        index += len;
    }

    Ok(tokens)
}

fn take_while(source: &str, predicate: impl Fn(char) -> bool) -> usize {
    source
        .char_indices()
        .find_map(|(index, character)| (!predicate(character)).then_some(index))
        .unwrap_or(source.len())
}

fn string_end(source: &str) -> Option<usize> {
    debug_assert!(source.starts_with('"'));
    let mut escaped = false;
    for (index, character) in source.char_indices().skip(1) {
        if escaped {
            escaped = false;
        } else if character == '\\' {
            escaped = true;
        } else if character == '"' {
            return Some(index + character.len_utf8());
        }
    }
    None
}

fn symbol_len(source: &str) -> Option<usize> {
    for symbol in ["::", "==", "!=", "<=", ">=", "&&", "||"] {
        if source.starts_with(symbol) {
            return Some(symbol.len());
        }
    }
    symbol_len_at(source.chars().next()?)
}

fn symbol_len_at(character: char) -> Option<usize> {
    matches!(
        character,
        '(' | ')'
            | '['
            | ']'
            | '{'
            | '}'
            | ','
            | ';'
            | '@'
            | '.'
            | ':'
            | '?'
            | '+'
            | '-'
            | '*'
            | '/'
            | '%'
            | '!'
            | '<'
            | '>'
            | '='
    )
    .then_some(character.len_utf8())
}

/// A top-level concrete-syntax item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ItemKind {
    Definition,
    Policy,
}

/// The source spans that describe one top-level definition or policy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Span,
    /// Policy annotations, the policy head, and each condition clause.
    ///
    /// Definitions have one part covering the whole definition. The final
    /// policy part includes the terminating semicolon.
    pub line_parts: Vec<Span>,
}

/// The grammar-derived outline of a complete Dogwood policy document.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Document {
    pub items: Vec<Item>,
}

/// Parse a complete policy document and retain the spans useful to
/// source-preserving tools.
pub fn parse_document(source: &str) -> Result<Document, pest::error::Error<Rule>> {
    parse_document_with(source, &ParseOptions::default())
}

/// [`parse_document`] with the given [`ParseOptions`].
pub fn parse_document_with(
    source: &str,
    options: &ParseOptions,
) -> Result<Document, pest::error::Error<Rule>> {
    let mut pairs = parse_with(Rule::policies, source, options)?;
    let policies = pairs.next().expect("policies produces one top-level pair");
    let items = policies
        .into_inner()
        .filter_map(|pair| match pair.as_rule() {
            Rule::def_decl => Some(definition_item(pair)),
            Rule::policy => Some(policy_item(pair)),
            Rule::EOI => None,
            _ => None,
        })
        .collect();
    Ok(Document { items })
}

fn definition_item(pair: Pair<'_>) -> Item {
    let span = span_of(&pair);
    Item {
        kind: ItemKind::Definition,
        span,
        line_parts: vec![span],
    }
}

fn policy_item(pair: Pair<'_>) -> Item {
    let span = span_of(&pair);
    let mut annotations = Vec::new();
    let mut conditions = Vec::new();
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::annotation => annotations.push(span_of(&child)),
            Rule::cond => conditions.push(span_of(&child)),
            _ => {}
        }
    }

    let mut line_parts = annotations.clone();
    let head_start = annotations.last().map_or(span.start, |part| part.end);
    if conditions.is_empty() {
        line_parts.push(Span::new(head_start, span.end));
    } else {
        line_parts.push(Span::new(head_start, conditions[0].start));
        for (index, condition) in conditions.iter().enumerate() {
            let end = conditions
                .get(index + 1)
                .map_or(span.end, |next| next.start);
            line_parts.push(Span::new(condition.start, end));
        }
    }
    line_parts.retain(|part| part.start < part.end);

    Item {
        kind: ItemKind::Policy,
        span,
        line_parts,
    }
}

fn span_of(pair: &Pair<'_>) -> Span {
    let span = pair.as_span();
    Span::new(span.start(), span.end())
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAX_DEPTH: usize = DEFAULT_MAX_DEPTH;

    #[test]
    fn the_node_limit_builder_sets_the_limit() {
        assert_eq!(ParseOptions::default().max_nodes, DEFAULT_MAX_NODES);
        assert_eq!(ParseOptions::default().max_nodes(7).max_nodes, 7);
    }

    #[test]
    fn a_budget_charge_that_does_not_fit_spends_nothing() {
        let mut budget = NodeBudget::new(3);
        assert_eq!(budget.charge(2), Ok(()));
        assert_eq!(budget.charge(2), Err(BudgetExhausted));
        assert_eq!(budget.charge(1), Ok(()));
        assert_eq!(budget.charge(1), Err(BudgetExhausted));
        assert_eq!(budget.charge(0), Ok(()));
        assert_eq!(budget.limit(), 3);
        assert_eq!(NodeBudget::new(0).charge(1), Err(BudgetExhausted));
        assert_eq!(NodeBudget::new(usize::MAX).charge(usize::MAX), Ok(()));
    }

    #[test]
    fn lossless_tokens_reconstruct_the_source() {
        let source =
            "// note\n@id(\"a,  b\") permit (principal, action, resource) when { a && b };";
        let tokens = tokenize(source).expect("tokenizes");
        assert_eq!(
            tokens.iter().map(|token| token.text).collect::<String>(),
            source
        );
        assert!(tokens.iter().any(|token| token.kind == TokenKind::Comment));
        assert!(tokens.iter().any(|token| token.kind == TokenKind::String));
    }

    #[test]
    fn document_outline_uses_grammar_boundaries() {
        let source = "def cedar ok(?x) { ?x == true }; \
            @id(\"a\") permit (principal, action, resource) \
            when { true } unless { false };";
        let document = parse_document(source).expect("parses");
        assert_eq!(document.items.len(), 2);
        assert_eq!(document.items[0].kind, ItemKind::Definition);
        assert_eq!(document.items[1].kind, ItemKind::Policy);
        assert_eq!(
            document.items[1]
                .line_parts
                .iter()
                .map(|span| span.text(source).trim())
                .collect::<Vec<_>>(),
            [
                "@id(\"a\")",
                "permit (principal, action, resource)",
                "when { true }",
                "unless { false };"
            ]
        );
    }

    fn policy(body: &str) -> String {
        format!("permit (principal, action, resource) when {{ {body} }};")
    }

    fn scan(source: &str) -> Option<usize> {
        nesting_violation(source, POLICY_NESTING_KEYWORDS, MAX_DEPTH)
    }

    #[test]
    fn nesting_scan_counts_brackets_and_open_keywords() {
        // The condition braces are one level.
        let at_limit = "(".repeat(MAX_DEPTH - 1);
        assert_eq!(scan(&policy(&at_limit)), None);
        let source = policy(&"[".repeat(MAX_DEPTH));
        assert_eq!(
            scan(&source),
            Some(source.find('[').expect("bracket") + MAX_DEPTH - 1)
        );
        let source = policy(&format!("{}x", "if ".repeat(MAX_DEPTH)));
        assert_eq!(scan(&source), source.rfind("if"));
        // Without keywords, only brackets count.
        assert_eq!(nesting_violation(&source, &[], MAX_DEPTH), None);
        // Only a closing bracket releases the keywords counted inside it, so
        // sibling keywords in one bracket level accumulate whatever separates
        // them: the braces and the `[` are two levels, so 30 `if`s fit.
        for separator in [", ", "; ", " && "] {
            let siblings = |n| vec!["if a then b else c"; n].join(separator);
            assert_eq!(
                scan(&policy(&format!("[{}]", siblings(MAX_DEPTH - 2)))),
                None
            );
            let source = policy(&format!("[{}]", siblings(MAX_DEPTH - 1)));
            assert_eq!(scan(&source), source.rfind("if"), "{separator:?}");
            // Nor does a separator outside every bracket release them.
            let source = siblings(MAX_DEPTH + 1);
            assert_eq!(scan(&source), source.rfind("if"), "{separator:?}");
        }
        let siblings = vec!["(if a then b else c)"; 2 * MAX_DEPTH].join(" && ");
        assert_eq!(scan(&policy(&siblings)), None);
        // `iffy` and `elif` are not `if`.
        assert_eq!(scan(&policy(&"iffy elif ".repeat(MAX_DEPTH))), None);
        // A field or a name spelled `if` counts, whatever byte precedes it:
        // the condition braces are one level, so the last `if` is too deep.
        for spelling in ["x.if ", "?if ", "$if "] {
            let source = policy(&spelling.repeat(MAX_DEPTH));
            assert_eq!(scan(&source), source.rfind("if"), "{spelling:?}");
        }
    }

    #[test]
    fn nesting_estimate_is_the_level_the_scan_compares_against_the_limit() {
        // The condition braces, five parentheses, and an `if`.
        let source = policy("(((((if a then b else c)))))");
        assert_eq!(nesting_estimate(&source, POLICY_NESTING_KEYWORDS), 7);
        assert_eq!(nesting_violation(&source, POLICY_NESTING_KEYWORDS, 7), None);
        assert_eq!(
            nesting_violation(&source, POLICY_NESTING_KEYWORDS, 6),
            source.find("if")
        );
        assert_eq!(nesting_estimate("", POLICY_NESTING_KEYWORDS), 0);
        let deep = policy(&"(".repeat(10 * MAX_DEPTH));
        assert_eq!(nesting_estimate(&deep, &[]), 10 * MAX_DEPTH + 1);
    }

    #[test]
    fn the_limit_is_the_callers() {
        let source = policy(&format!("{}true{}", "(".repeat(40), ")".repeat(40)));
        let error = parse_document(&source).expect_err("too deep at the default");
        assert!(error.to_string().contains("maximum depth of 32"), "{error}");
        parse_document_with(&source, &ParseOptions::default().max_depth(41)).expect("raised");
        let error = parse_document_with(&source, &ParseOptions::default().max_depth(40))
            .expect_err("one short");
        assert!(error.to_string().contains("maximum depth of 40"), "{error}");
        assert_eq!(ParseOptions::default().max_depth, DEFAULT_MAX_DEPTH);
    }

    #[test]
    fn nesting_scan_skips_strings_and_comments() {
        let deep = "([{".repeat(MAX_DEPTH);
        let in_string = policy(&format!("\"{deep} \\\" if {deep}\" == \"\""));
        assert_eq!(scan(&in_string), None);
        let in_comment = policy(&format!("// {deep} if\ntrue"));
        assert_eq!(scan(&in_comment), None);
        // `//` inside a string is not a comment, so the brackets after it count.
        let after_string = policy(&format!("\"//\" == {deep}"));
        assert!(scan(&after_string).is_some());
        // An unterminated `"` does not hide the brackets after it.
        let unterminated = policy(&format!("\" {deep}"));
        assert!(scan(&unterminated).is_some());
        assert!(tokenize(&unterminated).is_err());
    }

    #[test]
    fn deep_nesting_is_a_parse_error() {
        let source = policy(&format!("{}true{}", "(".repeat(10_000), ")".repeat(10_000)));
        let error = parse_document(&source).expect_err("too deep");
        assert!(error.to_string().contains("maximum depth of 32"), "{error}");
        assert_eq!(
            error.location,
            pest::error::InputLocation::Pos(source.find("((").expect("parens") + MAX_DEPTH - 1)
        );
        let at_limit = policy(&format!(
            "{}true{}",
            "(".repeat(MAX_DEPTH - 1),
            ")".repeat(MAX_DEPTH - 1)
        ));
        parse_document(&at_limit).expect("at the limit");
    }

    #[test]
    fn unterminated_strings_are_reported_by_the_lossless_lexer() {
        let source = "permit (principal, action, resource) when { \"unfinished };";
        let error = tokenize(source).expect_err("unterminated string");
        assert_eq!(error.span.start, source.find('"').expect("opening quote"));
        assert_eq!(error.span.end, source.len());
    }
}
