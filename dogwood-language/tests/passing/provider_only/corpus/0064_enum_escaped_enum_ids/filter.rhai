fn evaluate(text) {
    if type_of(text) == "()" { return #{ result: "needs review" }; }
    if text == "quote" { #{ result: "a\"b" } }
    else if text == "unsure" { #{ result: "needs review" } }
    else { #{ result: "ok" } }
}
