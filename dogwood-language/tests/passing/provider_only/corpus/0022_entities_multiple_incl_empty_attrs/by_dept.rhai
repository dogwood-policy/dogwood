// `Access::ByDept(dept) -> { allowed: bool }`. Allowed iff the principal's
// department is engineering. `dept` arrives as the principal's `dept` entity
// attribute, supplied in the trace's `entities(...)` envelope (alongside a
// second, empty-attrs entity) and resolved from the decision's entity store.
fn evaluate(dept) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(dept) == "()" {
        return #{ allowed: false };
    }

    #{ allowed: dept == "eng" }
}
