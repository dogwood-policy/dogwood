// `Strings::Length(text) -> { length: Long }`.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    // Sentinel polarity: -1 satisfies `length < 6`, chosen so events
    // without a document are NOT blocked by this length guard.
    if type_of(text) == "()" {
        return #{ length: -1 };
    }
    #{ length: text.len() }
}
