//! Whole-trace `.log` replay: [`parse_trace`] and [`replay_log`].
//!
//! These are conveniences over the core [`Authorizer`]
//! loop, for driving a recorded event trace (the `.log` wire format) through
//! a policy and collecting the per-timepoint verdict stream. The regression
//! corpora and the external differential-testing package use them so each
//! caller need not reimplement the loop and the verdict-stream format.

use crate::api::Error;
use crate::authorize::{Authorizer, Decision};
use crate::interpreter::value::Event;
use crate::policy_set::LoweredPolicySet;

/// Parse a `.log` trace into its sequence of [`Event`]s.
///
/// Each non-blank line is one timepoint: `@<ts> <Action>(<field>: <value>,
/// …)`. Values use Cedar surface forms (entity refs `Ns::Type::"id"`,
/// strings, integers, decimals, `true`/`false`, arrays, objects). Feed the
/// events to an [`Authorizer`] in order to replay the
/// trace.
pub fn parse_trace(log: &str) -> Result<Vec<Event>, Error> {
    crate::interpreter::log_parse::parse_trace(log)
        .map(|trace| trace.points)
        .map_err(Error::TraceParse)
}

/// Replay a whole `.log` trace through `policies` and return the
/// per-timepoint verdict stream: one `@<ts> (time point <i>): <bool>` line
/// for *every* decision point — `true` for `Allow`, `false` for `Deny` —
/// newline-joined. This is the corpus-comparison format.
///
/// Consumes the [`LoweredPolicySet`] (it drives a fresh stateful
/// [`Authorizer`], so temporal leaves see prior events as
/// history). History-only events (non-decision kinds) contribute no line.
pub fn replay_log(policies: LoweredPolicySet, log: &str) -> Result<String, Error> {
    let events = parse_trace(log)?;
    let mut authorizer = Authorizer::new(policies);

    let mut lines = Vec::new();
    for (i, event) in events.iter().enumerate() {
        let ts = event.timestamp();
        if let Some(response) = authorizer.is_authorized(event) {
            let allowed = response.decision() == Decision::Allow;
            lines.push(format!("@{ts} (time point {i}): {allowed}"));
        }
    }
    Ok(lines.join("\n"))
}
