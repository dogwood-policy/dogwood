// Returns document length minus 5.
// Short docs get a negative diff, long docs get positive.
fn evaluate(document) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(document) == "()" {
        return #{ diff: -1 };
    }

    #{ diff: document.len() - 5 }
}
