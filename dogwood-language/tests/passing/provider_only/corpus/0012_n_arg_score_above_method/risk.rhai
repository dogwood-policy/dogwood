// `Risk::Score(text) -> { score: decimal }`, plus a method
// `above(threshold: decimal) -> bool`.
//
// `evaluate` returns a fixed risk score per keyword, built with
// `parse_decimal` (the engine is built with the `decimal` feature) so the
// value is a real Decimal.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ score: parse_decimal("-1.0") };
    }

    let score = if text == "safe" {
        parse_decimal("0.10")
    } else if text == "bad" {
        parse_decimal("0.90")
    } else {
        parse_decimal("0.50")
    };
    #{ score: score }
}

// A method takes the previous stage's value first (here the base record
// `#{ score: <decimal> }`), then its own declared arguments (the decimal
// `threshold`). It returns the method's declared output type — a Bool: is
// the score strictly greater than the threshold?
fn above(o, threshold) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(threshold) == "()" {
        return false;
    }

    o.score > threshold
}
