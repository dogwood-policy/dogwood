fn score_for(text, category) {
    if text == "violent_doc" && category == "VIOLENCE" {
        parse_decimal("0.80")
    } else if text == "hateful_doc" && category == "HATE" {
        parse_decimal("0.80")
    } else {
        parse_decimal("0.10")
    }
}

fn evaluate(text, categories) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" || type_of(categories) == "()" {
        return #{ VIOLENCE: #{ severityScore: parse_decimal("-1.0") }, HATE: #{ severityScore: parse_decimal("-1.0") } };
    }

    let out = #{};
    for category in categories {
        out[category] = #{ severityScore: score_for(text, category) };
    }
    out
}
