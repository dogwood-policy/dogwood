//! The fail-closed rule shared by `replay` and `DogwoodAuthorizer::isAuthorized`.
//!
//! Cedar skips a policy whose condition errors and decides from the rest, and
//! the request context is not validated against the schema. So an argument of
//! the wrong type (or a missing one) read by a `forbid` drops that rule, and a
//! matching `permit` comes back Allow with the error attached. Both entry
//! points pass every decision through [`fail_closed`] so they agree on every
//! event.

use crate::ops::Verdict;

/// Force a deny when evaluation raised any error.
///
/// On errors the verdict becomes [`Verdict::Deny`] and `determining_rules` is
/// cleared: a forced deny was determined by no rule (the rules Cedar reports
/// are the permits it would have allowed on). Without errors, both are left as
/// Cedar decided.
pub fn fail_closed(
    verdict: &mut Verdict,
    determining_rules: &mut Vec<usize>,
    errors: &[String],
) {
    if !errors.is_empty() {
        *verdict = Verdict::Deny;
        determining_rules.clear();
    }
}
