// `Access::ByDept(dept) -> { allowed: bool }`. Allowed iff the principal's
// department is engineering. `dept` arrives as the principal's `dept` entity
// attribute, supplied per event in the trace's `entities(...)` envelope and
// resolved from the decision's entity store before this runs.
fn evaluate(dept) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(dept) == "()" {
        return #{ allowed: false };
    }

    #{ allowed: dept == "eng" }
}
