fn evaluate(level) {
    if type_of(level) == "()" { return #{ escalate: true }; }
    #{ escalate: level == "HIGH" }
}
