fn evaluate(text) {
    if type_of(text) == "()" { return #{ labels: ["HIGH"] }; }
    if text.contains("attack") { #{ labels: ["MEDIUM", "HIGH"] } }
    else if text.contains("maybe") { #{ labels: ["LOW", "MEDIUM"] } }
    else { #{ labels: ["LOW"] } }
}
