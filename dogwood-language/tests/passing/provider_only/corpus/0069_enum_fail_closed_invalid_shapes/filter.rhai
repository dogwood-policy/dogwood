fn evaluate(text) {
    if type_of(text) == "()" { return #{ result: "HIGH" }; }
    if text == "unit" { return #{ result: () }; }
    if text == "array" { return #{ result: ["LOW"] }; }
    if text == "map" { return #{ result: #{ id: "LOW" } }; }
    if text == "int" { return #{ result: 3 }; }
    if text == "bool" { return #{ result: true }; }
    if text == "dec" { return #{ result: parse_decimal("1.0") }; }
    if text.contains("attack") { #{ result: "HIGH" } } else { #{ result: "LOW" } }
}
