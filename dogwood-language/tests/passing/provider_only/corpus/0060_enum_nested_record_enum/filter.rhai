fn evaluate(text) {
    if type_of(text) == "()" { return #{ VIOLENCE: #{ level: "HIGH" }, HATE: #{ level: "HIGH" } }; }
    let v = if text.contains("attack") { "HIGH" } else { "LOW" };
    let h = if text.contains("hate") { "HIGH" } else { "LOW" };
    #{ VIOLENCE: #{ level: v }, HATE: #{ level: h } }
}
