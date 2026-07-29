// `Strings::Length(text) -> { length: Long }`, here fed a resource entity
// attribute (`resource.owner`) reached through `resource is` narrowing.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ length: -1 };
    }

    #{ length: text.len() }
}
