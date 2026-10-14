// `BedrockGuardrails::ContentFilter(texts, categories)`: one record per category,
// shaped like a typical guardrail declaration. `VIOLENCE` scores 0.9 when any text
// contains "kill"; every other category scores 0.1.
fn evaluate(texts, categories) {
    let low = parse_decimal("0.1");
    // Unit argument: return the most restrictive conforming value.
    if type_of(texts) == "()" {
        let s = parse_decimal("1.0");
        let c = "HIGH";
        return #{ VIOLENCE: #{ confidenceScore: s, confidence: c }, HATE: #{ confidenceScore: low, confidence: "NONE" }, SEXUAL: #{ confidenceScore: low, confidence: "NONE" }, MISCONDUCT: #{ confidenceScore: low, confidence: "NONE" }, INSULTS: #{ confidenceScore: low, confidence: "NONE" } };
    }
    let hit = false;
    for t in texts { if to_lower(t).contains("kill") { hit = true; } }
    let s = if hit { parse_decimal("0.9") } else { low };
    let c = if hit { "HIGH" } else { "NONE" };
    #{ VIOLENCE: #{ confidenceScore: s, confidence: c }, HATE: #{ confidenceScore: low, confidence: "NONE" }, SEXUAL: #{ confidenceScore: low, confidence: "NONE" }, MISCONDUCT: #{ confidenceScore: low, confidence: "NONE" }, INSULTS: #{ confidenceScore: low, confidence: "NONE" } }
}

fn maxConfidenceScore(input) {
    let m = parse_decimal("0.0");
    for v in input.values() { if v.confidenceScore > m { m = v.confidenceScore; } }
    m
}

fn minConfidenceScore(input) {
    let m = parse_decimal("1.0");
    for v in input.values() { if v.confidenceScore < m { m = v.confidenceScore; } }
    m
}

fn count(input) {
    let n = 0;
    for v in input.values() { if v.confidenceScore >= parse_decimal("0.5") { n += 1; } }
    n
}

fn categories(input) {
    let out = [];
    for k in input.keys() { if input[k].confidenceScore >= parse_decimal("0.5") { out.push(k); } }
    out
}
