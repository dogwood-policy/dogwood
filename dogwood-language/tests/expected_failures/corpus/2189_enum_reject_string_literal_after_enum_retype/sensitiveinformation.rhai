// `BedrockGuardrails::SensitiveInformation(texts, categories)`: one record per category,
// shaped like a typical guardrail declaration. `ADDRESS` scores 0.9 when any text
// contains "ssn"; every other category scores 0.1.
fn evaluate(texts, categories) {
    let low = parse_decimal("0.1");
    // Unit argument: return the most restrictive conforming value.
    if type_of(texts) == "()" {
        let s = parse_decimal("1.0");
        let c = "HIGH";
        return #{ ADDRESS: #{ confidenceScore: s, confidence: c }, AGE: #{ confidenceScore: low, confidence: "NONE" }, CREDIT_DEBIT_CARD_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, EMAIL: #{ confidenceScore: low, confidence: "NONE" }, NAME: #{ confidenceScore: low, confidence: "NONE" }, PHONE: #{ confidenceScore: low, confidence: "NONE" }, US_SOCIAL_SECURITY_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, IP_ADDRESS: #{ confidenceScore: low, confidence: "NONE" }, URL: #{ confidenceScore: low, confidence: "NONE" }, PASSWORD: #{ confidenceScore: low, confidence: "NONE" }, USERNAME: #{ confidenceScore: low, confidence: "NONE" }, DRIVER_ID: #{ confidenceScore: low, confidence: "NONE" }, PIN: #{ confidenceScore: low, confidence: "NONE" }, AWS_ACCESS_KEY: #{ confidenceScore: low, confidence: "NONE" }, AWS_SECRET_KEY: #{ confidenceScore: low, confidence: "NONE" }, LICENSE_PLATE: #{ confidenceScore: low, confidence: "NONE" }, MAC_ADDRESS: #{ confidenceScore: low, confidence: "NONE" }, SWIFT_CODE: #{ confidenceScore: low, confidence: "NONE" }, CREDIT_DEBIT_CARD_CVV: #{ confidenceScore: low, confidence: "NONE" }, CREDIT_DEBIT_CARD_EXPIRY: #{ confidenceScore: low, confidence: "NONE" }, INTERNATIONAL_BANK_ACCOUNT_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, US_BANK_ACCOUNT_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, US_BANK_ROUTING_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, US_INDIVIDUAL_TAX_IDENTIFICATION_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, US_PASSPORT_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, VEHICLE_IDENTIFICATION_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, UK_NATIONAL_HEALTH_SERVICE_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, UK_NATIONAL_INSURANCE_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, UK_UNIQUE_TAXPAYER_REFERENCE_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, CA_HEALTH_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, CA_SOCIAL_INSURANCE_NUMBER: #{ confidenceScore: low, confidence: "NONE" } };
    }
    let hit = false;
    for t in texts { if to_lower(t).contains("ssn") { hit = true; } }
    let s = if hit { parse_decimal("0.9") } else { low };
    let c = if hit { "HIGH" } else { "NONE" };
    #{ ADDRESS: #{ confidenceScore: s, confidence: c }, AGE: #{ confidenceScore: low, confidence: "NONE" }, CREDIT_DEBIT_CARD_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, EMAIL: #{ confidenceScore: low, confidence: "NONE" }, NAME: #{ confidenceScore: low, confidence: "NONE" }, PHONE: #{ confidenceScore: low, confidence: "NONE" }, US_SOCIAL_SECURITY_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, IP_ADDRESS: #{ confidenceScore: low, confidence: "NONE" }, URL: #{ confidenceScore: low, confidence: "NONE" }, PASSWORD: #{ confidenceScore: low, confidence: "NONE" }, USERNAME: #{ confidenceScore: low, confidence: "NONE" }, DRIVER_ID: #{ confidenceScore: low, confidence: "NONE" }, PIN: #{ confidenceScore: low, confidence: "NONE" }, AWS_ACCESS_KEY: #{ confidenceScore: low, confidence: "NONE" }, AWS_SECRET_KEY: #{ confidenceScore: low, confidence: "NONE" }, LICENSE_PLATE: #{ confidenceScore: low, confidence: "NONE" }, MAC_ADDRESS: #{ confidenceScore: low, confidence: "NONE" }, SWIFT_CODE: #{ confidenceScore: low, confidence: "NONE" }, CREDIT_DEBIT_CARD_CVV: #{ confidenceScore: low, confidence: "NONE" }, CREDIT_DEBIT_CARD_EXPIRY: #{ confidenceScore: low, confidence: "NONE" }, INTERNATIONAL_BANK_ACCOUNT_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, US_BANK_ACCOUNT_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, US_BANK_ROUTING_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, US_INDIVIDUAL_TAX_IDENTIFICATION_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, US_PASSPORT_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, VEHICLE_IDENTIFICATION_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, UK_NATIONAL_HEALTH_SERVICE_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, UK_NATIONAL_INSURANCE_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, UK_UNIQUE_TAXPAYER_REFERENCE_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, CA_HEALTH_NUMBER: #{ confidenceScore: low, confidence: "NONE" }, CA_SOCIAL_INSURANCE_NUMBER: #{ confidenceScore: low, confidence: "NONE" } }
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
