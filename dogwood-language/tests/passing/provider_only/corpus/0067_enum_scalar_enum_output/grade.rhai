fn evaluate(text) {
    if type_of(text) == "()" { return "HIGH"; }
    if text.contains("attack") { "HIGH" } else if text.contains("maybe") { "MEDIUM" } else { "LOW" }
}
