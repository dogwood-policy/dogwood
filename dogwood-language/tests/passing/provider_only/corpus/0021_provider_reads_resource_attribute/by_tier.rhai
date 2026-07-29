// `Access::ByTier(tier) -> { allowed: bool }`. Allowed iff the target
// resource is in the production tier. `tier` arrives as the resource's `tier`
// entity attribute, supplied per event in the trace's `entities(...)`
// envelope and resolved from the decision's entity store before this runs.
fn evaluate(tier) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(tier) == "()" {
        return #{ allowed: false };
    }

    #{ allowed: tier == "prod" }
}
