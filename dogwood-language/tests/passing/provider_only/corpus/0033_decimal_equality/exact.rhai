// Returns 0.5 for "half", 0.0 for empty, 1.0 otherwise.
fn evaluate(document) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(document) == "()" {
        return #{ score: parse_decimal("-1.0") };
    }

    let score = if document == "half" {
        parse_decimal("0.5")
    } else if document == "" {
        parse_decimal("0.0")
    } else {
        parse_decimal("1.0")
    };
    #{ score: score }
}
