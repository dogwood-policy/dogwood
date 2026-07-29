// Information-provider implementation for `Content::Classify`.
//
// `evaluate(text)` is the base invocation: it returns a record with two
// Long scores. `violence` is 90 when the text contains "kill", else 5;
// `malicious` is a fixed 3.
//
// `classify(input)` is a zero-argument METHOD (its only parameter is the
// previous stage's value — here the base record). It post-processes the
// output by returning it UNCHANGED, so the pipeline's result is exactly
// the base record. The `.violence` field projection AFTER the method is
// then plain native Cedar over that record.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ violence: -1, malicious: -1 };
    }

    #{
        violence: if text.contains("kill") { 90 } else { 5 },
        malicious: 3
    }
}

fn classify(input) {
    input
}
