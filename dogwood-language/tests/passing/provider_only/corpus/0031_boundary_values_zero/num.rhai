// Returns document length as a bare integer.
fn evaluate(document) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(document) == "()" {
        return -1;
    }

    document.len()
}

// Zero-arg method on a scalar: input is the integer from evaluate.
fn double(input) {
    input * 2
}
