//! Extension dialects.
//!
//! A condition leaf is either bare Cedar (handled natively) or a
//! **`temporal { ... }`** marker block, whose inner body is the temporal
//! sub-language. The temporal dialect provides a sub-parser and a typed
//! AST; lowering to Cedar lives in `crate::cedarify` and leaf evaluation
//! in the monitoring engine (see [`crate`]).
//!
//! Information providers are *not* a marker dialect. A `guardrails { … }`
//! clause is transparent sugar for a bare Cedar clause (see the parser's
//! `build_cond`), and a provider invocation is an ordinary Cedar call
//! (`Ns::Fn(args)…`) recognized and hoisted at lowering time. The
//! [`provider`] module therefore holds only the invocation/argument/method
//! data types, the declarations schema, the authorize-time evaluator, and
//! validation — no sub-parser and no closed grammar. (The surface keyword
//! is `guardrails` for historical reasons; the concept is "provider"
//! everywhere else: module, declarations,
//! `context.providers`.)

pub mod dialect;
pub mod provider;
pub mod temporal;

use vstd::prelude::*;

/// The dialects an extension marker can introduce. The cedar-only
/// spine recognizes the markers but implements none of them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dialect {
    Temporal,
}

impl Dialect {
    /// Map a marker keyword to a dialect, if recognized. Only `temporal`
    /// is a marker dialect; `guardrails` is handled as sugar in the parser
    /// and never reaches here.
    pub fn from_marker(marker: &str) -> Option<Dialect> {
        match marker {
            "temporal" => Some(Dialect::Temporal),
            _ => None,
        }
    }

    pub fn marker(self) -> &'static str {
        match self {
            Dialect::Temporal => "temporal",
        }
    }
}

verus! {

/// An extension leaf in the AST: a parsed `temporal { … }` marker block.
/// Inside `verus!` (transparent) so the verified macro pass can match on
/// it; `Clone` is derived outside Verus, as for the `crate::ast` types.
#[derive(Debug, Clone)]
#[verifier::external_derive(Clone)]
pub enum Extension {
    Temporal(temporal::Temporal),
}

pub assume_specification [<Extension as Clone>::clone](_0: &Extension) -> Extension;

} // verus!
