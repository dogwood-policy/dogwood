fn evaluate(text) {
    if type_of(text) == "()" { return #{ labels: ["HIGH"] }; }
    if text == "boom" { #{ labels: ["LOW", "nope"] } }      // one bad element
    else if text.contains("attack") { #{ labels: ["HIGH"] } }
    else { #{ labels: ["LOW", "MEDIUM"] } }
}
