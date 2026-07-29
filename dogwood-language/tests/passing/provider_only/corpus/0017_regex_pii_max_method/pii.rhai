// `Pii::Scan(text) -> { ssn: Long, email: Long }` plus the zero-argument
// output method `maxCount() -> Long`.
//
// `evaluate` counts two PII shapes in the text with the `regex_count` host
// function:
//   * SSN-like:   three-three-four digit runs, e.g. "123-45-6789"
//   * email-like: a token with an "@" and a dotted domain
// The result is a per-category count record. `maxCount` is the reduce
// accessor (reference-parity: no arguments of its own, only the previous
// stage's value) — it returns the larger of the two category counts, so
// "worst PII category count < 1" means "no PII of any tracked kind".
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ ssn: -1, email: -1 };
    }

    let ssn = regex_count("[0-9]{3}-[0-9]{2}-[0-9]{4}", text);
    let email = regex_count("[A-Za-z0-9._]+@[A-Za-z0-9.]+[.][A-Za-z]+", text);
    #{ ssn: ssn, email: email }
}

// Zero-argument output method: first (and only) parameter is the previous
// stage's value — the `evaluate` record. Returns the larger category count.
fn maxCount(input) {
    if input.ssn >= input.email { input.ssn } else { input.email }
}
