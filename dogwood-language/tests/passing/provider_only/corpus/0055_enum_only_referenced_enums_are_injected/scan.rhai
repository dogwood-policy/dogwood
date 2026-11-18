fn evaluate(text) {
    if type_of(text) == "()" { return #{ risk: "HIGH" }; }
    #{ risk: "LOW" }
}
