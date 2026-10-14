// The enum argument arrives as its bare id ("high"), not the full UID text.
fn evaluate(level) {
    if type_of(level) == "()" { return #{ escalate: true }; }
    #{ escalate: level == "high" }
}
