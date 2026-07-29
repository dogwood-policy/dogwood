// `Lists::Blocked(text) -> { blocked: Bool }` — a tiny hard-coded
// denylist. (A real provider might consult an external service; the
// shape is the same — only the implementation differs.)
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ blocked: false };
    }

    let denylist = ["evil", "badword"];
    #{ blocked: denylist.contains(text) }
}
