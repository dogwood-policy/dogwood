//! Error types for the Dogwood frontend.
//!
//! Two layers of finding live here, mirroring Cedar's own `parse`-then-
//! `validate` split — and, like Cedar, **both are self-rendering
//! `miette::Diagnostic`s**: each embeds its `.dw` source (via [`SourceLoc`] or
//! a `#[source_code]` field), so `miette::Report::new(finding)` underlines the
//! offending source with no `with_source_code` call.
//!
//! * [`ParseError`] / [`ParseErrors`] / [`CedarifyError`] / [`MacroError`] —
//!   the *fatal* prefix, surfaced through [`crate::Error`] from the lowering
//!   phases ([`ParsedPolicySet::parse`](crate::policy_set::ParsedPolicySet::parse) /
//!   [`ParsedPolicySet::lower`](crate::policy_set::ParsedPolicySet::lower)) and
//!   [`ServiceSchemaBuilder::build`](crate::ServiceSchemaBuilder::build). A
//!   syntax / macro / lowering failure means there is nothing well-formed to
//!   validate. The
//!   parser/cedarify/macro passes produce internal, span-only `Raw*` errors;
//!   the pipeline boundary pairs each with the `.dw` source to build these
//!   public, self-rendering leaves.
//! * [`ValidationError`] / [`ValidationWarning`] — the *findings* from the
//!   schema-aware validator ([`Validator::validate`](crate::Validator::validate)).
//!   Each carries a [`SourceSpan`] rebased to the original `.dw` source **and**
//!   that source. They mirror Cedar's `ValidationError` / `ValidationWarning`,
//!   but each is a superset: the `Cedar` variant carries Cedar's own finding
//!   (verbatim for warnings), and the `Extension` variant carries a
//!   sublanguage-dialect finding.
//! * [`ValidationResult`] — the whole validation pass's findings,
//!   split into an error channel and a warning channel, with the same query
//!   methods as Cedar's `ValidationResult`.

use miette::{Diagnostic, SourceSpan};
use std::fmt;
use thiserror::Error;

/// A byte range `[start, end)` into the original Dogwood source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { start, end }
    }

    /// Rebase a block-relative span into the enclosing source by adding the
    /// block-body `base` offset. Used by extension validators whose inner
    /// spans are relative to their `temporal { … }` / `provider { … }`
    /// block body to produce an absolute `.dw` span.
    pub fn rebased(self, base: usize) -> Span {
        Span {
            start: base + self.start,
            end: base + self.end,
        }
    }
}

/// A placeholder `Span` (`[0, 0)`) for AST nodes that have **no source
/// location** — e.g. nodes an external client constructs programmatically
/// rather than parsing from `.dw` text.
///
/// The temporal AST node types (see [`crate::temporal_ast`]) carry a `span`
/// field, but the `Span` type *name* is intentionally not exported (spans are
/// a crate-internal source-mapping detail — a client reading a Dogwood-produced
/// tree can copy a node's `.span`, but there is no exported way to *name* the
/// type or mint a fresh one). This free function lets a downstream crate fill
/// that field — via type inference, without naming `Span` — so it can build
/// nodes from scratch without a real source offset:
///
/// ```ignore
/// use dogwood_language::{dummy_span, temporal_ast::Predicate};
/// let p = Predicate { span: dummy_span(), /* … */ };
/// ```
///
/// A dummy span only affects diagnostics' reported source location (it points at
/// offset 0); it has no effect on evaluation or compilation.
pub fn dummy_span() -> Span {
    Span { start: 0, end: 0 }
}

impl From<Span> for SourceSpan {
    fn from(span: Span) -> Self {
        SourceSpan::new(span.start.into(), span.end.saturating_sub(span.start))
    }
}

/// A located span **with its source text** — Dogwood's analog of Cedar's
/// `cedar_policy_core::parser::Loc`.
///
/// This is the self-rendering primitive behind every spanned public finding
/// (fatal [`crate::Error`] leaves and [`ValidationError`] alike). Because it
/// carries the `.dw` source (shared, `Arc<str>`) alongside the byte span, a
/// finding renders its own underlined snippet — `println!("{:?}",
/// miette::Report::new(err))` just works, with no `with_source_code` needed.
/// This mirrors Cedar, whose parse and validation errors both embed a `Loc`.
///
/// The `Diagnostic` impls that use it (via `impl_diagnostic_source_loc!`)
/// produce both the primary label and the `source_code` from these two
/// fields.
#[derive(Debug, Clone)]
pub struct SourceLoc {
    span: SourceSpan,
    src: std::sync::Arc<str>,
}

impl SourceLoc {
    /// Pair a `.dw` byte span with the shared source text it indexes into.
    pub(crate) fn new(span: Span, src: std::sync::Arc<str>) -> Self {
        SourceLoc {
            span: span.into(),
            src,
        }
    }

    /// The byte span, as a miette [`SourceSpan`].
    pub fn span(&self) -> SourceSpan {
        self.span
    }

    /// The `.dw` source text this span indexes into.
    pub fn source(&self) -> &str {
        &self.src
    }

    /// The shared source as a `miette::SourceCode` (the sized `Arc<str>`, so it
    /// coerces to `&dyn SourceCode`).
    fn source_code(&self) -> &dyn miette::SourceCode {
        &self.src
    }
}

/// Hand-implement [`miette::Diagnostic`] for a finding that carries a
/// `SourceLoc` (optionally behind an `Option`), deriving `labels()` and
/// `source_code()` from it. Analogous to Cedar-core's
/// `impl_diagnostic_from_source_loc_opt_field!`, but not identical: Cedar emits
/// a *non-primary underline with no text* (`LabeledSpan::underline`), whereas
/// this emits a **primary** label carrying the finding's `Display` message —
/// consistent with how Dogwood's derive-based findings use `#[label(primary,
/// "{message}")]`. (One visible effect: since the message is also the
/// diagnostic header, it appears both as the header and on the inline label.)
///
/// `$field` is the `SourceLoc` field; append `?` when it is `Option<SourceLoc>`.
macro_rules! impl_diagnostic_source_loc {
    ($t:ty, $field:ident) => {
        impl miette::Diagnostic for $t {
            fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
                Some(Box::new(std::iter::once(
                    miette::LabeledSpan::new_primary_with_span(
                        Some(self.to_string()),
                        self.$field.span(),
                    ),
                )))
            }
            fn source_code(&self) -> Option<&dyn miette::SourceCode> {
                Some(self.$field.source_code())
            }
        }
    };
    ($t:ty, $field:ident ?) => {
        impl miette::Diagnostic for $t {
            fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
                let loc = self.$field.as_ref()?;
                Some(Box::new(std::iter::once(
                    miette::LabeledSpan::new_primary_with_span(Some(self.to_string()), loc.span()),
                )))
            }
            fn source_code(&self) -> Option<&dyn miette::SourceCode> {
                self.$field.as_ref().map(|l| l.source_code())
            }
        }
    };
}

/// A parse-time error: the `.dw` source was syntactically invalid, or
/// a semantic check at parse time (e.g. an effect that isn't
/// `permit`/`forbid`) failed.
///
/// This is the **internal**, span-only shape the parser produces. It is paired
/// with the `.dw` source at the pipeline boundary to build the public,
/// self-rendering [`ParseError`]. Kept crate-private.
#[derive(Debug, Clone)]
pub(crate) struct RawParseError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for RawParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} (at {}..{})",
            self.message, self.span.start, self.span.end
        )
    }
}

/// An error produced while lowering Dogwood to Cedar (`cedarify`).
///
/// In the cedar-only spine this is most commonly "an extension marker
/// (`temporal`/`provider`) was used, but that extension is not yet
/// implemented". The **internal**, span-only shape; paired with the source at
/// the boundary to build the public [`CedarifyError`]. Kept crate-private.
#[derive(Debug, Clone)]
pub(crate) struct RawCedarifyError {
    pub message: String,
    pub span: Option<Span>,
}

impl fmt::Display for RawCedarifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

// ─── Public, self-rendering fatal-error leaves ───────────────────────
//
// These are the public analogs of the internal `Raw*` errors, carrying a
// `SourceLoc` (span + `.dw` source) so each renders its own underlined
// snippet. They mirror Cedar's public `ParseError` / `ParseErrors`, which wrap
// the core parser errors and self-render from an embedded `Loc`. Built at the
// pipeline boundary (`crate::api`), where the source `Arc<str>` is in scope.

/// A single Dogwood parse error, located in the `.dw` source it came from.
///
/// Self-rendering: `miette::Report::new(err)` shows the underlined snippet
/// with no `with_source_code`. Mirrors `cedar_policy::ParseError`.
#[derive(Error, Debug, Clone)]
#[error("{message}")]
#[non_exhaustive]
pub struct ParseError {
    message: String,
    loc: SourceLoc,
}

impl ParseError {
    pub(crate) fn new(message: String, loc: SourceLoc) -> Self {
        ParseError { message, loc }
    }

    /// The located span (with its source) this error points at.
    pub fn location(&self) -> &SourceLoc {
        &self.loc
    }
}

impl_diagnostic_source_loc!(ParseError, loc);

/// One or more [`ParseError`]s from a single parse. Mirrors
/// `cedar_policy::ParseErrors`: `Display` and `Diagnostic` surface the first
/// error (with the rest as miette `related` diagnostics), and
/// [`iter`](ParseErrors::iter) yields them all. Guaranteed non-empty by
/// construction (the parser only returns this when it collected ≥1 error).
#[derive(Debug, Clone)]
pub struct ParseErrors(Vec<ParseError>);

impl ParseErrors {
    pub(crate) fn new(errors: Vec<ParseError>) -> Self {
        debug_assert!(!errors.is_empty(), "ParseErrors is always non-empty");
        ParseErrors(errors)
    }

    /// Every [`ParseError`] in this batch (non-empty).
    pub fn iter(&self) -> impl Iterator<Item = &ParseError> {
        self.0.iter()
    }

    fn first(&self) -> &ParseError {
        &self.0[0]
    }
}

impl fmt::Display for ParseErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Show only the first error (Cedar does the same); the rest surface as
        // miette `related` diagnostics and via `iter()`.
        write!(f, "{}", self.first())
    }
}

impl std::error::Error for ParseErrors {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.first().source()
    }
}

// Everything except `related()` is forwarded to the first error, so a consumer
// using only `Display` / `code()` / `labels()` still gets rich info for the
// first error even without realizing there are several. `related()` exposes
// the 2nd..Nth. This mirrors `cedar_policy_core`'s `ParseErrors` exactly.
impl Diagnostic for ParseErrors {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.first().code()
    }
    fn severity(&self) -> Option<miette::Severity> {
        self.first().severity()
    }
    fn help<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.first().help()
    }
    fn url<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.first().url()
    }
    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        self.first().source_code()
    }
    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        self.first().labels()
    }
    fn diagnostic_source(&self) -> Option<&dyn Diagnostic> {
        self.first().diagnostic_source()
    }
    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn Diagnostic> + 'a>> {
        // The first error's own `related`, then the 2nd..Nth errors — matching
        // Cedar's chaining so the first error's nested diagnostics aren't lost.
        let mut errs = self.iter().map(|e| e as &dyn Diagnostic);
        errs.next().map(move |first| match first.related() {
            Some(first_related) => {
                Box::new(first_related.chain(errs)) as Box<dyn Iterator<Item = _>>
            }
            None => Box::new(errs),
        })
    }
}

/// A Dogwood-to-Cedar lowering error, located where possible in the `.dw`
/// source. Self-rendering when it carries a location.
#[derive(Error, Debug, Clone)]
#[error("{message}")]
#[non_exhaustive]
pub struct CedarifyError {
    message: String,
    loc: Option<SourceLoc>,
}

impl CedarifyError {
    pub(crate) fn new(message: String, loc: Option<SourceLoc>) -> Self {
        CedarifyError { message, loc }
    }

    /// The located span (with its source), if this error is tied to one.
    pub fn location(&self) -> Option<&SourceLoc> {
        self.loc.as_ref()
    }
}

impl_diagnostic_source_loc!(CedarifyError, loc?);

/// A macro-expansion error (`def cedar` / `def temporal`), located in the
/// `.dw` source. Self-rendering. Mirrors the shape of [`ParseError`].
#[derive(Error, Debug, Clone)]
#[error("{message}")]
#[non_exhaustive]
pub struct MacroError {
    message: String,
    loc: SourceLoc,
}

impl MacroError {
    pub(crate) fn new(message: String, loc: SourceLoc) -> Self {
        MacroError { message, loc }
    }

    /// The located span (with its source) this error points at.
    pub fn location(&self) -> &SourceLoc {
        &self.loc
    }
}

impl_diagnostic_source_loc!(MacroError, loc);

/// The findings of one schema-aware validation pass, split into an error
/// channel and a warning channel.
///
/// Mirrors Cedar's `ValidationResult`: the validator accumulates every
/// finding rather than stopping at the first, and the query methods match
/// Cedar's (`validation_passed`, `validation_passed_without_warnings`,
/// `validation_errors`, `validation_warnings`). An empty error channel means
/// the source is valid; warnings never make validation fail.
#[derive(Debug)]
pub struct ValidationResult {
    errors: Vec<ValidationError>,
    warnings: Vec<ValidationWarning>,
}

impl ValidationResult {
    /// Build a result from its two channels. Crate-internal: a
    /// `ValidationResult` is only ever produced by
    /// [`Validator::validate`](crate::Validator::validate) (mirroring
    /// `cedar_policy::ValidationResult`, which external code cannot
    /// construct).
    pub(crate) fn new(errors: Vec<ValidationError>, warnings: Vec<ValidationWarning>) -> Self {
        Self { errors, warnings }
    }

    /// `true` if validation found no errors (warnings are ignored).
    pub fn validation_passed(&self) -> bool {
        self.errors.is_empty()
    }

    /// `true` if validation found neither errors nor warnings.
    pub fn validation_passed_without_warnings(&self) -> bool {
        self.errors.is_empty() && self.warnings.is_empty()
    }

    /// The errors found, in the order they were produced.
    pub fn validation_errors(&self) -> impl Iterator<Item = &ValidationError> {
        self.errors.iter()
    }

    /// The warnings found, in the order they were produced.
    pub fn validation_warnings(&self) -> impl Iterator<Item = &ValidationWarning> {
        self.warnings.iter()
    }
}

/// A single validation *error*, tagged by the layer that produced it. Superset
/// of Cedar's `ValidationError`: the `Cedar` variant wraps Cedar's own finding,
/// the `Extension` variant carries a sublanguage-dialect finding.
///
/// **Self-rendering:** each finding carries its `.dw` source (`src`) alongside
/// its span, so `miette::Report::new(err)` underlines the offending source with
/// no `with_source_code` — matching both Cedar's own `ValidationError` (which
/// embeds a `Loc`) and Dogwood's fatal [`crate::Error`].
///
/// `#[non_exhaustive]` (as Cedar's `ValidationError` is), and `Clone` (as
/// Cedar's is) so a single finding can be lifted out of a
/// [`ValidationResult`] and rendered on its own — the `source` chain is an
/// `Arc` to keep the clone cheap.
#[derive(Error, Diagnostic, Debug, Clone)]
#[non_exhaustive]
pub enum ValidationError {
    /// Cedar's schema-aware validator rejected the lowered policy. The span
    /// is rebased from the lowered policy to the original `.dw` source.
    #[error("{message}")]
    #[diagnostic(code(cedar))]
    Cedar {
        message: String,
        #[label(primary, "{}", label.as_ref().unwrap_or(message))]
        span: SourceSpan,
        label: Option<String>,
        #[help]
        help: Option<String>,
        #[source_code]
        src: std::sync::Arc<str>,
        #[source]
        source: Option<std::sync::Arc<dyn miette::Diagnostic + Send + Sync>>,
    },

    /// A sublanguage-extension leaf failed schema-aware validation. `code`
    /// is the dialect's marker (`"temporal"` / `"provider"` / …), supplied
    /// by the dialect's own renderer — the error type does not enumerate
    /// dialects, so a new sublanguage needs no new variant here.
    #[error("{message}")]
    #[diagnostic(code(extension))]
    Extension {
        /// The dialect marker this finding came from (e.g. `"temporal"`).
        code: &'static str,
        message: String,
        #[label(primary, "{}", label.as_ref().unwrap_or(message))]
        span: SourceSpan,
        label: Option<String>,
        #[help]
        help: Option<String>,
        #[source_code]
        src: std::sync::Arc<str>,
        #[source]
        source: Option<std::sync::Arc<dyn miette::Diagnostic + Send + Sync>>,
    },
}

/// A single validation *warning*. Superset of Cedar's `ValidationWarning`:
/// the `Cedar` variant carries Cedar's own warning verbatim (so a caller
/// migrating from Cedar loses nothing), the `Extension` variant carries a
/// sublanguage-dialect warning. No dialect emits a warning today; the variant
/// exists so the warning channel is symmetric with the error channel.
///
/// Like the error type, the `Extension` variant is self-rendering (it carries
/// its `.dw` source); the `Cedar` variant forwards to Cedar's own warning,
/// which embeds its own `Loc`. `#[non_exhaustive]` and `Clone`, matching
/// `ValidationError` and Cedar's own `ValidationWarning`.
#[derive(Error, Diagnostic, Debug, Clone)]
#[non_exhaustive]
pub enum ValidationWarning {
    /// A warning from Cedar's schema-aware validator, passed through
    /// unchanged.
    #[error(transparent)]
    #[diagnostic(transparent)]
    Cedar(cedar_policy::ValidationWarning),

    /// A sublanguage-extension warning. `code` is the dialect's marker.
    #[error("{message}")]
    #[diagnostic(code(extension))]
    Extension {
        /// The dialect marker this warning came from (e.g. `"temporal"`).
        code: &'static str,
        message: String,
        #[label(primary, "{}", label.as_ref().unwrap_or(message))]
        span: SourceSpan,
        label: Option<String>,
        #[help]
        help: Option<String>,
        #[source_code]
        src: std::sync::Arc<str>,
        #[source]
        source: Option<std::sync::Arc<dyn miette::Diagnostic + Send + Sync>>,
    },
}
