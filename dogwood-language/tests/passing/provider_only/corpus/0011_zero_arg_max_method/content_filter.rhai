// `BedrockGuardrails::ContentFilter(text) -> { violence: Long, malicious: Long }`
// plus the zero-argument output method `maxConfidenceScore() -> Long`.
//
// `evaluate` scores the text per category: a case-insensitive substring
// match bumps that category's score. `maxConfidenceScore` is the
// reference-parity accessor — it takes no arguments of its own, only the
// previous stage's value (the score record), and returns the worst of the
// two category scores.
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ violence: -1, malicious: -1 };
    }

    let lowered = to_lower(text);
    let violence = if lowered.contains("kill") { 90 } else { 5 };
    let malicious = if lowered.contains("exploit") { 80 } else { 3 };
    #{ violence: violence, malicious: malicious }
}

// Zero-argument output method: first (and only) parameter is the previous
// stage's value — the `evaluate` record. Returns the larger category score.
fn maxConfidenceScore(input) {
    if input.violence >= input.malicious { input.violence } else { input.malicious }
}
