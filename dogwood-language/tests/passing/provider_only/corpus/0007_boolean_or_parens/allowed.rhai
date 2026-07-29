// `Lists::Allowed(text) -> { allowed: Bool }`.
//
// True when the document is on a small hard-coded allowlist. Pairs with
// length.rhai under an `||` so a document passes if it is EITHER
// allowlisted OR short.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ allowed: false };
    }

    let allow = text == "readme" || text == "manifest";
    #{ allowed: allow }
}
