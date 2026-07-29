//! The `temporal` extension dialect: parses a `temporal { … }` marker
//! block body into a temporal [`ast::Condition`]. Lowering to a hoisted
//! Cedar context field lives in `crate::cedarify`; evaluation against a
//! trace lives in the monitoring engine.

pub mod ast;
pub mod check;
pub mod parse;
pub mod schema_info;
pub mod validate;

use crate::error::Span;

use ast::Condition;

/// A parsed `temporal { … }` leaf.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Temporal {
    /// The parsed temporal condition.
    pub condition: Condition,
    /// Span of the block *body* in the original `.dw` source. Its start
    /// is the base for the condition's block-relative inner spans.
    pub span: Span,
}

impl Temporal {
    /// Parse a temporal block body into a [`Temporal`] extension leaf.
    ///
    /// `body` is the verbatim text between the `temporal { … }` braces;
    /// `body_span` locates that body in the `.dw` source — its start is
    /// the base the condition's (block-relative) inner spans are measured
    /// from, so a consumer rebases an inner span by adding `span.start`.
    pub fn parse(body: &str, body_span: Span) -> Result<Temporal, String> {
        let condition = parse::parse_condition(body)?;
        // Static binding checks: aggregation `for`-domain binding and
        // `exists` range-restriction safety (§7). See `check`.
        check::check_condition(&condition, &std::collections::BTreeSet::new())?;
        // Leaf closedness: every variable must be bound by an `exists` or an
        // aggregation `for` list (free variables would evaluate unsoundly).
        // Runs before the demands rule, which presumes a closed leaf.
        check::check_leaf_closed(&condition)?;
        // Evaluation-order (demands) rule: binding-equality aggregate
        // operands, since-lefts, and filters must follow the restrictors of
        // the variables they consume. Seeded top-down over nested chains.
        check::check_demands(&condition)?;
        Ok(Temporal {
            condition,
            span: body_span,
        })
    }
}

/// Parse the body of a `def temporal` macro definition. The body is
/// either a bare aggregation expression (the value half of a `let`) or a
/// full temporal condition; the grammar's `temporal_macro_body_entry`
/// covers both. Returns the body tagged with which it parsed under so the
/// macro expander knows what call-site slot the macro is callable in.
pub fn parse_macro_body(body: &str) -> Result<crate::ast::MacroBody, String> {
    parse::parse_macro_body(body)
}
