// Information-provider implementation for `Strings::Matches` — a regex
// matcher. `evaluate(text, pattern)` returns `{ matched: Bool }`, using the
// built-in `regex_is_match(pattern, text)` host function.
fn evaluate(text, pattern) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" || type_of(pattern) == "()" {
        return #{ matched: false };
    }

    #{ matched: regex_is_match(pattern, text) }
}
