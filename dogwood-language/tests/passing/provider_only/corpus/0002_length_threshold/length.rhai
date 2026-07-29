// `Strings::Length(text) -> { length: Long }`.
//
// Pure Rhai — no host function needed; `len()` is built in. Shows a
// provider whose output is a number the policy compares with `<`.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ length: -1 };
    }

    #{ length: text.len() }
}
