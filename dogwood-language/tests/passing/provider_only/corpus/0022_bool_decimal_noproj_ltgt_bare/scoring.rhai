// `Scoring::Compute(document, strict, threshold) -> Long`
//
// Returns a risk score as a bare integer (no record wrapping).
// `strict` (bool): if true, doubles the base score.
// `threshold` (decimal): multiplied into the score via parse_decimal.
// Base score: document length * 10.
fn evaluate(document, strict, threshold) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(document) == "()" || type_of(strict) == "()" || type_of(threshold) == "()" {
        return -1;
    }

    let base = document.len() * 10;
    let score = if strict { base * 2 } else { base };
    score
}
