fn evaluate(text) {
    if type_of(text) == "()" { return #{ result: "HIGH" }; }
    // A bare id where the declared output is a record.
    if text == "bare" { return "HIGH"; }
    // The required enum field `result` is missing.
    if text == "wrongkey" { return #{ score: "HIGH" }; }
    #{ result: "LOW" }
}
