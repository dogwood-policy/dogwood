// The enum fields of the record arrive as their bare ids ("high"), not the full UID text.
fn evaluate(input) {
    if type_of(input) == "()" { return #{ escalate: true }; }
    #{ escalate: input.level == "high" || input.kind == "abuse" }
}
