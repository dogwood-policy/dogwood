//! The CLI's owned error and diagnostic types.
//!
//! The frontend's result types (`Error`, `ValidationError`, `ParseErrors`, …)
//! are `miette::Diagnostic`s built for *rendering* — they carry spans and an
//! `Arc<str>` of source, but are **not** `Serialize`. The CLI needs both a
//! human rendering (underlined snippets) *and* a stable JSON shape, so this
//! module defines:
//!
//!   * [`OpError`] — the single fatal-error type the `ops` functions return.
//!     It is *both* a [`miette::Diagnostic`] (so the CLI renders it with a
//!     graphical handler) and [`serde::Serialize`] (so `--format json` emits a
//!     stable shape).
//!   * [`Diagnostic`] — one non-fatal finding (a validation error/warning),
//!     owned and serializable.
//!
//! Both are produced by [`project`], which walks any `miette::Diagnostic` from
//! the frontend and captures its message, severity, labels, and help into
//! owned fields — pinning a deliberate JSON contract rather than serializing
//! the frontend's internal representation (which is not `Serialize` anyway).

use miette::Diagnostic as MietteDiagnostic;
use serde::Serialize;

/// The severity of a [`Diagnostic`], projected from `miette::Severity`
/// (which defaults to `Error` when a diagnostic does not specify one).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Error,
    Warning,
    Advice,
}

impl From<Option<miette::Severity>> for Severity {
    fn from(s: Option<miette::Severity>) -> Self {
        match s {
            Some(miette::Severity::Warning) => Severity::Warning,
            Some(miette::Severity::Advice) => Severity::Advice,
            // miette treats the absence of a severity as an error.
            Some(miette::Severity::Error) | None => Severity::Error,
        }
    }
}

/// One labelled span within the source a diagnostic points at: a byte range
/// and an optional per-label message. Offsets index the `.dw` (or schema)
/// source text the CLI passed in.
#[derive(Debug, Clone, Serialize)]
pub struct Label {
    /// Byte offset of the label's start in the source.
    pub start: usize,
    /// Byte length of the labelled span.
    pub len: usize,
    /// The label's own message, if it carries one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
}

/// One diagnostic finding, owned and serializable — the CLI's projection of
/// a frontend `miette::Diagnostic`. Used for the non-fatal channel (validation
/// errors/warnings); the fatal channel is [`OpError`], which wraps one of
/// these plus the source text for rendering.
#[derive(Debug, Clone, Serialize)]
pub struct Diagnostic {
    pub severity: Severity,
    /// The diagnostic's stable code (e.g. `"temporal"`), if it has one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    pub message: String,
    /// The labelled spans, in the order the diagnostic reports them. Empty for
    /// a span-less finding (e.g. an event-schema error that carries only a
    /// message).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub labels: Vec<Label>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub help: Option<String>,
    /// Whether this finding has any source-anchored span. `false` means the CLI
    /// cannot underline a snippet for it — only the message is available.
    pub spanned: bool,
}

/// Project any frontend `miette::Diagnostic` into an owned, serializable
/// [`Diagnostic`]. Captures the message (`Display`), severity, labelled spans,
/// and help text. Related/nested diagnostics are not flattened here — the
/// callers that need them (e.g. a batch of parse errors) collect each into its
/// own [`Diagnostic`].
pub fn project(d: &dyn MietteDiagnostic) -> Diagnostic {
    let labels: Vec<Label> = d
        .labels()
        .map(|iter| {
            iter.map(|ls| Label {
                start: ls.offset(),
                len: ls.len(),
                message: ls.label().map(str::to_string),
            })
            .collect()
        })
        .unwrap_or_default();
    let spanned = !labels.is_empty();
    Diagnostic {
        severity: d.severity().into(),
        code: d.code().map(|c| c.to_string()),
        message: d.to_string(),
        labels,
        help: d.help().map(|h| h.to_string()),
        spanned,
    }
}

/// The single fatal-error type the [`ops`](crate::ops) functions return. It is
/// both a [`miette::Diagnostic`] (for graphical human rendering) and
/// [`serde::Serialize`] (for JSON), and it carries the source text so the CLI
/// can render an underlined snippet with no `with_source_code`.
#[derive(Debug, Clone, Serialize)]
pub struct OpError {
    /// The primary finding (message, severity, labels, help). Boxed to keep
    /// `OpError` — and therefore every `Result<_, OpError>` the ops functions
    /// return — small (a `Diagnostic` is several `String`s and a `Vec`).
    #[serde(flatten)]
    diagnostic: Box<Diagnostic>,
    /// Any follow-on findings (e.g. the 2nd..Nth of a batch of parse errors).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    related: Vec<Diagnostic>,
    /// The source text the labels index into, retained so the miette
    /// `Diagnostic` impl can render a snippet. Not serialized (the JSON
    /// consumer has the source already).
    #[serde(skip)]
    source: Option<String>,
}

impl OpError {
    /// Build a fatal error from a frontend `miette::Diagnostic`, capturing its
    /// primary finding, any `related` diagnostics, and the `source` text so the
    /// human renderer can underline the offending span.
    pub fn from_diagnostic(d: &dyn MietteDiagnostic, source: impl Into<Option<String>>) -> Self {
        let related = d
            .related()
            .map(|iter| iter.map(project).collect())
            .unwrap_or_default();
        OpError {
            diagnostic: Box::new(project(d)),
            related,
            source: source.into(),
        }
    }

    /// Build a fatal error from a plain message with no source location — for
    /// the frontend paths that surface a bare `String` (provider/MCP errors,
    /// the span-less event-schema error).
    pub fn message(msg: impl Into<String>) -> Self {
        OpError {
            diagnostic: Box::new(Diagnostic {
                severity: Severity::Error,
                code: None,
                message: msg.into(),
                labels: Vec::new(),
                help: None,
                spanned: false,
            }),
            related: Vec::new(),
            source: None,
        }
    }
}

impl std::fmt::Display for OpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.diagnostic.message)
    }
}

impl std::error::Error for OpError {}

// The miette impl re-projects the owned fields back into miette's model, so the
// CLI's graphical handler underlines the snippet using the retained `source`.
impl MietteDiagnostic for OpError {
    fn code<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        self.diagnostic
            .code
            .as_ref()
            .map(|c| Box::new(c.clone()) as Box<dyn std::fmt::Display>)
    }

    fn severity(&self) -> Option<miette::Severity> {
        Some(match self.diagnostic.severity {
            Severity::Error => miette::Severity::Error,
            Severity::Warning => miette::Severity::Warning,
            Severity::Advice => miette::Severity::Advice,
        })
    }

    fn help<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        self.diagnostic
            .help
            .as_ref()
            .map(|h| Box::new(h.clone()) as Box<dyn std::fmt::Display>)
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        self.source.as_ref().map(|s| s as &dyn miette::SourceCode)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        if self.diagnostic.labels.is_empty() {
            return None;
        }
        let spans: Vec<miette::LabeledSpan> = self
            .diagnostic
            .labels
            .iter()
            .map(|l| miette::LabeledSpan::new(l.message.clone(), l.start, l.len))
            .collect();
        Some(Box::new(spans.into_iter()))
    }
}
