fn evaluate(text) {
    if type_of(text) == "()" { return #{ result: "LOW" }; }
    if text == "b" { #{ result: "low" } }
    else if text == "c" { #{ result: "" } }
    else if text == "d" { #{ result: "日本 語" } }
    else { #{ result: "LOW" } }
}
