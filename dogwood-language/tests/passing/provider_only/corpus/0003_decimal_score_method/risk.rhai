// `Content::Risk(text) -> { severityScore: decimal }`.
//
// Returns a fixed risk score per keyword. `parse_decimal` produces a
// Rhai Decimal (the engine is built with the `decimal` feature), which
// Dogwood converts to a Cedar decimal — so the policy can compare it
// with `.lessThan(decimal("0.5"))`.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ severityScore: parse_decimal("-1.0") };
    }

    let score = if text == "safe" {
        parse_decimal("0.10")
    } else if text == "spam" {
        parse_decimal("0.80")
    } else {
        parse_decimal("0.50")
    };
    #{ severityScore: score }
}
