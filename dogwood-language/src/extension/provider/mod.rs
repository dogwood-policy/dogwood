//! *Information providers* — named, externally-defined functions over
//! request data.
//!
//! An information provider is a named function over request data: a name
//! (`Ns::Fn`), an argument signature, an output type, and a configurable
//! implementation (today a sandboxed Rhai script). It is the successor to
//! the hardcoded "guardrail" classifier concept — but the set of providers
//! and *how each is evaluated* are declared in data (`providers.json`), so a
//! deployment can add a provider without changing Dogwood.
//!
//! Providers are compile-time sugar over Cedar with **no dedicated
//! syntax**: a provider invocation is an ordinary Cedar call
//! (`Ns::Fn(args).chain… <cmp>`) that `cedarify` recognizes — because the
//! name is a declared provider — and hoists to a `context.providers.<name>`
//! reference, leaving the field/method chain and comparison as native
//! Cedar. (A `guardrails { … }` clause is transparent sugar for a bare
//! Cedar clause; it is not parsed by this module.) The provider *output* is
//! evaluated into that context slot at authorize time (by running its
//! implementation — see [`eval`]); the comparison is then Cedar's to
//! evaluate.
//!
//! This module therefore provides the invocation/argument/method data types
//! ([`ast`]), the declarations schema ([`declarations`]), the authorize-time
//! evaluator ([`eval`]), and validation ([`validate`]) — but no parser and
//! no closed grammar.

pub mod ast;
pub mod declarations;
pub mod eval;
pub mod validate;

/// Whether an `ExprKind::Call` name is an information-provider invocation.
///
/// Recognition is **structural**: any namespace-qualified name (`Ns::Fn`) is
/// a provider invocation. It is not a declared-ness test — Cedar's own
/// extension functions (`decimal`/`datetime`/`duration`/`ip`) are
/// single-segment and desugared in the parser (so never reach an
/// `ExprKind::Call`), and macros are single-segment by grammar, so a
/// namespaced `Call` can only be a provider. Whether that provider is
/// *declared* is a separate question (see
/// [`declarations::ProviderDeclarations::names`]).
///
/// This is the single definition of "is a provider invocation", shared by
/// lowering (`crate::cedarify`) and the pre-lowering diagnostic accessors on
/// [`ParsedPolicySet`](crate::policy_set::ParsedPolicySet).
pub fn is_provider_name(name: &str) -> bool {
    name.contains("::")
}
