fn evaluate(text) {
    if type_of(text) == "()" { return #{ score: parse_decimal("1.0") }; }
    if text.contains("attack") { #{ score: parse_decimal("0.9") } }
    else if text.contains("maybe") { #{ score: parse_decimal("0.5") } }
    else { #{ score: parse_decimal("0.1") } }
}

// bucket(): decimal score -> MyGuardrails::Score id.
fn bucket(input) {
    if input.score >= parse_decimal("0.7") { "HIGH" }
    else if input.score >= parse_decimal("0.4") { "MEDIUM" }
    else { "LOW" }
}
