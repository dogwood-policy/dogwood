fn evaluate(text) {
    if type_of(text) == "()" { return #{ result: "HIGH" }; }
    if text == "case" { return #{ result: "low" }; }
    if text == "pad" { return #{ result: "LOW " }; }
    if text == "empty" { return #{ result: "" }; }
    if text == "crit" { return #{ result: "CRITICAL" }; }
    if text == "uid" { return #{ result: "MyGuardrails::Score::\"LOW\"" }; }
    if text.contains("attack") { #{ result: "HIGH" } } else { #{ result: "LOW" } }
}
