// hello -> LOW, maybe -> MEDIUM, attack -> HIGH, and `note` echoes the input.
// `note` is declared with the unknown paramType `strng`, so it falls back to
// String: the script returns a string and the policy compares it with one.
fn evaluate(text) {
    if type_of(text) == "()" { return #{ result: "HIGH", note: "" }; }   // restrictive sentinel
    if text.contains("attack") { #{ result: "HIGH", note: text } }
    else if text.contains("maybe") { #{ result: "MEDIUM", note: text } }
    else { #{ result: "LOW", note: text } }
}
