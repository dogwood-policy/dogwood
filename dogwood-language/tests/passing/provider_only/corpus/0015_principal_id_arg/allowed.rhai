// `Access::Allowed(principalId) -> { allowed: bool }`.
//
// The single argument is the request principal's id (passed as
// `principal.id` at the call site, resolved pre-Cedar from the request
// scope). A tiny hardcoded allowlist stands in for a real membership
// lookup: `alice` is allowed, everyone else is not.
fn evaluate(principal_id) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(principal_id) == "()" {
        return #{ allowed: false };
    }

    let allowed = principal_id == "alice";
    #{ allowed: allowed }
}
