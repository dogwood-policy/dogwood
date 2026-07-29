// `Text::Analyze(text) -> { raw: Long }`, with two chained methods.
//
// A method's first parameter is the previous pipeline stage's value:
// for `normalize()` that is the base `evaluate` record; for `clamp()`
// that is `normalize`'s integer result. Methods compose left-to-right,
// so `.normalize().clamp()` evaluates as `clamp(normalize(evaluate(text)))`.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ raw: -1 };
    }

    #{ raw: text.len() }
}

// `normalize() -> integer` = raw * 10.
fn normalize(input) {
    input.raw * 10
}

// `clamp() -> integer` = cap the incoming integer at 100.
fn clamp(input) {
    if input > 100 { 100 } else { input }
}
