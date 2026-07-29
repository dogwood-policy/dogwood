// `Strings::Length(text) -> { length: Long }`.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    // Sentinel polarity: -1 FAILS the forbid's `length >= 6` guard, so
    // the forbid does not fire for events without a document — the
    // PERMISSIVE direction under forbid, which is exactly the trap this
    // case pins.
    if type_of(text) == "()" {
        return #{ length: -1 };
    }
    #{ length: text.len() }
}
