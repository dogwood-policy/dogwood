// `Strings::Matches(text, pattern) -> { matched: Bool }`.
//
// Returns whether `pattern` matches `text`, via the `regex_is_match` host
// function. Here it backs the positive guardrail precondition (the document
// must be an all-letters name).
fn evaluate(text, pattern) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" || type_of(pattern) == "()" {
        return #{ matched: false };
    }

    #{ matched: regex_is_match(pattern, text) }
}
