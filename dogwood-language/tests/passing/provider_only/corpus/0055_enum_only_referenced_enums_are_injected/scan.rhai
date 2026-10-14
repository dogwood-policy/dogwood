fn evaluate(text) {
    if type_of(text) == "()" { return #{ risk: "HIGH", result: "HIGH" }; }
    #{ risk: "LOW", result: "LOW" }
}
