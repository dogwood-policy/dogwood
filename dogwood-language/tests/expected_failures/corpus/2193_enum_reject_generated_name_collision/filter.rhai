// hello -> LOW, maybe -> MEDIUM, attack -> HIGH. Returns the bare enum id as a
// string; Dogwood converts it to MyGuardrails::Score per the declared type.
fn evaluate(text) {
    if type_of(text) == "()" { return #{ result: "HIGH" }; }   // restrictive sentinel
    if text.contains("attack") { #{ result: "HIGH" } }
    else if text.contains("maybe") { #{ result: "MEDIUM" } }
    else { #{ result: "LOW" } }
}
