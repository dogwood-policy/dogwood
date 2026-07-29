//! The temporal evaluation model and evaluator.
//!
//! * [`value`] — the runtime value + event-trace model (`Trace`,
//!   `Event`, `EventData`, `Value`).
//! * [`log_parse`] — parse the `.log` trace wire format into a `Trace`.
//! * [`eval`] — the built-in MFOTL evaluator (`formerly`/`previous`/
//!   `since`/aggregations) over a trace.
//!
//! Authorization itself lives in [`crate`]: it lowers the policy
//! set to Cedar (`cedarify`), evaluates each extension leaf here, binds
//! the result into the request context, and runs Cedar's authorizer.

pub mod eval;
pub mod log_parse;
pub mod value;
