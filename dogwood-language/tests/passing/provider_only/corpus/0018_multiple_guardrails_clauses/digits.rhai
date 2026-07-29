// `Strings::DigitCount(text) -> { count: Long }`.
//
// Counts the digit characters in the document via the `regex_count` host
// function (non-overlapping matches of `[0-9]`). Used by the second
// guardrail clause to reject any document containing a digit.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ count: -1 };
    }

    #{ count: regex_count("[0-9]", text) }
}
