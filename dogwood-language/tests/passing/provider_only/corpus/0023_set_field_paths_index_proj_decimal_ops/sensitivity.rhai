// `Sensitivity::Analyze(texts, category) -> { scored: decimal, raw: Long }`
//
// `texts` is a set (array) of strings to analyze; `category` selects
// the scoring algorithm. Returns a record with a decimal score and a
// raw integer count.
//
// Scoring: if category is "PII" and any text contains "ssn", score is 0.95.
// If category is "SAFE", score is 0.0 (zero — unscored).
// Otherwise score is 0.5 (moderate).
fn evaluate(texts, category) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(texts) == "()" || type_of(category) == "()" {
        return #{ scored: parse_decimal("-1.0"), raw: -1 };
    }

    let has_pii = false;
    for t in texts {
        if t.contains("ssn") {
            has_pii = true;
        }
    }

    let score = if category == "SAFE" {
        parse_decimal("0.0")
    } else if has_pii {
        parse_decimal("0.95")
    } else {
        parse_decimal("0.5")
    };

    #{ scored: score, raw: texts.len() }
}
