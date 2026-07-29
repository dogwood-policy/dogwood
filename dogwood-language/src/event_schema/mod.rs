//! The event-schema DSL: a generic, schema-independent description of how
//! to derive event signatures from an action schema.
//!
//! An event schema declares, for any action binder `<A>`, what fields each
//! event kind (`request` / `response` / author-defined) carries — either
//! spliced from the action (`...inputs(A)`) or injected with an explicit
//! type (`callerPrincipal: principalType(A)`). It is parsed here into an
//! [`ast::EventSchema`]; [`derive`] binds the selectors to a concrete
//! action schema (producing per-event field sets), and [`validate`]
//! checks temporal predicates against the result. `parse` consumes all
//! three.

pub mod ast;
pub mod derive;
pub mod parse;
pub mod pin;
pub mod relativize;
pub mod validate;
