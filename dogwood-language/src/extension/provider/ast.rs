//! The information-provider data types.
//!
//! A provider invocation is written as an ordinary Cedar call,
//! `Ns::Function(args).chain… <cmp>` — there is no dedicated provider
//! grammar. At lowering time (`crate::cedarify`) a call whose name is a
//! declared provider is recognized, and its Cedar-`ast` argument and
//! output-method-chain expressions are lifted into the structured types
//! here: an [`Invocation`] (name + [`Arg`]s) plus a chain of
//! [`MethodCall`]s. The invocation is then hoisted to a
//! `context.providers.<name>` reference and evaluated out of band at
//! authorize time (see [`super::eval`]); the surrounding projection and
//! comparison stay native Cedar.
//!
//! These types are thus **detection-path-independent**: they describe a
//! provider invocation regardless of how it was written, and are consumed
//! by lowering (typing + hoisting), validation ([`super::validate`]), and
//! evaluation ([`super::eval`]).

use crate::error::Span;

/// A provider-output method call: a name plus its (possibly empty) argument
/// list, e.g. `.maxConfidenceScore()` or `.scoreAbove(decimal("0.5"))`.
///
/// Each method is a **post-processor** on the invocation's output: on
/// `Ns::Fn(args).m(margs)` the value bound into context is
/// `m(evaluate(args), margs…)`, and chains compose left to right. Zero args
/// (`.maxSeverityScore()`) is the MFOTL-parity accessor case; N args is the
/// generalization. Each method resolves to a `fn <name>(input, args…)` in
/// the provider's Rhai script (see [`super::declarations`]). The arguments
/// reuse the invocation [`Arg`] grammar, resolved against the request event
/// exactly like the base invocation's arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodCall {
    pub span: Span,
    pub name: String,
    pub args: Vec<Arg>,
}

/// A provider invocation: `Ns::Function(arg, …)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Invocation {
    pub span: Span,
    /// Namespace-qualified function name, e.g. `["Strings", "Matches"]`.
    pub function: Vec<String>,
    pub args: Vec<Arg>,
}

impl Invocation {
    /// The declaration key, e.g. `Strings::Matches`.
    pub fn key(&self) -> String {
        self.function.join("::")
    }
}

/// An invocation (or method) argument: an attribute-path reference into the
/// request, a literal, or a set. Paths are rooted at `context`, `principal`,
/// or `resource` and resolved against the request event at authorize time
/// (see `crate::api::resolve_provider_arg`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Arg {
    /// An attribute path, e.g. `["context", "input", "stock"]`,
    /// `["principal", "id"]`, `["resource", "owner"]`. The first segment is
    /// the root (`context` / `principal` / `resource`).
    Field(Vec<String>),
    String(String),
    Integer(i64),
    /// `decimal("0.5")` — payload kept as text (parsed downstream), matching
    /// the `Literal::Decimal` convention. Chiefly used for method thresholds
    /// like `scoreAbove(decimal("0.5"))`.
    Decimal(String),
    Bool(bool),
    Set(Vec<Arg>),
}
