// `Zone::Blocked(zone) -> { blocked: bool }`. Blocks the restricted zone.
// `zone` arrives as the principal's nested `address.zone` entity attribute,
// supplied in the trace's `entities(...)` envelope and resolved from the
// decision's entity store (a two-segment path) before this runs.
fn evaluate(zone) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(zone) == "()" {
        return #{ blocked: false };
    }

    #{ blocked: zone == "restricted" }
}
