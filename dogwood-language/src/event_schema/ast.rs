//! The event-schema DSL AST.
//!
//! An event schema is a list of [`EventDecl`]s. Each declares, for an
//! action binder (`<A>`), the fields a given event kind carries — either
//! spliced from the action via a [`Selector`] (`...inputs(A)`) or injected
//! with an explicit type (`callerPrincipal: principalType(A)`).
//!
//! This is a purely syntactic description: the selectors and the binder
//! are symbolic. Binding them to a concrete action schema (the derivation
//! that turns this into per-event field sets) is a later pass; nothing
//! here consults a schema.

use crate::error::Span;
use crate::extension::temporal::ast::Interval;

/// A parsed event schema: the ordered list of event-kind declarations, plus
/// the optional maximum-window cap.
#[derive(Debug, Clone)]
pub struct EventSchema {
    /// The `max_window = <interval>` directive, if the schema declared one.
    /// `None` means the schema did not set a cap, and derivation supplies the
    /// [`DEFAULT_MAX_WINDOW`](crate::event_schema::derive::DEFAULT_MAX_WINDOW).
    pub max_window: Option<Interval>,
    pub decls: Vec<EventDecl>,
}

/// One `[decision] event <A>::kind { fields }` declaration.
///
/// `span` and `binder` are retained for diagnostics and for the
/// derivation/decision-trigger wiring; not every field is read yet.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct EventDecl {
    pub span: Span,
    /// `true` if prefixed with `decision` — ingesting an event of this
    /// kind is a decision point that runs authorization.
    pub decision: bool,
    /// The action binder name, e.g. `A` in `<A>`.
    pub binder: String,
    /// The event kind segment, e.g. `request` / `response`.
    pub kind: String,
    pub fields: Vec<FieldSpec>,
}

/// A field entry in an event declaration's body.
///
/// `span`s are retained for diagnostics (error attribution back to the
/// schema source), though not yet read.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum FieldSpec {
    /// `...selector(A)` — splice every field the selector yields for the
    /// bound action.
    Spread { selector: Selector, span: Span },
    /// `[pin] name: <type> [= <pin>]` — inject one field with an explicit
    /// type. When `pin` is `Some`, the field is *pinned*: the pin-injection
    /// pass conjoins `name: <pin-value>` onto every predicate for this event
    /// (a correlation against the decision request). A pinned field must be a
    /// leaf (never a record type); the parser enforces that.
    Named {
        name: String,
        ty: TypeExpr,
        pin: Option<PinValue>,
        span: Span,
    },
}

/// The value a pinned field is forced to match, resolved against the decision
/// request. Kept as dotted path segments plus the reference *root* so it lowers
/// to the right temporal term:
///   * a **scope** reference (`principal` / `resource`, ± an attribute tail)
///     lowers to `Term::ScopeField` — the request scope entity / attribute;
///   * a **context** reference (`context.<path>`) lowers to `Term::ContextField`
///     — a field of the request context record.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct PinValue {
    /// The path segments the field must match. For a scope reference the first
    /// segment is the `principal` / `resource` root (e.g. `["principal"]`,
    /// `["principal", "dept"]`); for a context reference it is the
    /// `context.<...>` path without the leading `context` (`["input", "user"]`,
    /// `["__drupe", "session_id"]`).
    pub context_path: Vec<String>,
    /// Which request root the path is anchored to — determines the temporal
    /// term the pin lowers to.
    pub root: PinRoot,
    pub span: Span,
}

/// The request root a [`PinValue`] path is anchored to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PinRoot {
    /// `principal` / `resource` — the request scope entity (→ `Term::ScopeField`).
    Scope,
    /// `context.<path>` — a field of the request context record
    /// (→ `Term::ContextField`).
    Context,
}

/// The type of an injected field.
#[derive(Debug, Clone)]
pub enum TypeExpr {
    /// `selector(A)` — the type the selector yields for the bound action
    /// (e.g. `principalType(A)` is the action's principal entity type(s)).
    Selector(Selector),
    /// A concrete, possibly-qualified Cedar type name, e.g. `String`,
    /// `Long`, `Drupe::OAuthUser`. Kept as the path segments.
    Concrete(Vec<String>),
    /// `{ … }` — a nested record: the injected field becomes a group whose
    /// members are themselves field specs, addressed as `name.member`. This
    /// is how an author opts a named field into hierarchy (a spread inside
    /// the record, e.g. `{ ...inputs(A) }`, is allowed too).
    Record(Vec<FieldSpec>),
}

/// A reader over an action: the four things the derivation can pull from
/// an action's declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Selector {
    /// The action's input field record (Cedar `context.input`).
    Inputs,
    /// The action's output field record (Cedar `context.output`).
    Outputs,
    /// The action's declared `appliesTo.principalTypes`.
    PrincipalType,
    /// The action's declared `appliesTo.resourceTypes`.
    ResourceType,
}

impl Selector {
    pub fn as_str(self) -> &'static str {
        match self {
            Selector::Inputs => "inputs",
            Selector::Outputs => "outputs",
            Selector::PrincipalType => "principalType",
            Selector::ResourceType => "resourceType",
        }
    }
}
