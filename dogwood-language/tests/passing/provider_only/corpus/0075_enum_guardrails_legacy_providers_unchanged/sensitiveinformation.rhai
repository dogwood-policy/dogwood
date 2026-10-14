// `BedrockGuardrails::SensitiveInformation(texts, categories)`: one record per category,
// shaped like a typical guardrail declaration. `ADDRESS` scores 0.9 when any text
// contains "ssn"; every other category scores 0.1.
fn evaluate(texts, categories) {
    let low = parse_decimal("0.1");
    // Unit argument: return the most restrictive conforming value.
    if type_of(texts) == "()" {
        let s = parse_decimal("1.0");
        let c = "HIGH";
        return #{ ADDRESS: #{ confidenceScore: s }, AGE: #{ confidenceScore: low }, CREDIT_DEBIT_CARD_NUMBER: #{ confidenceScore: low }, EMAIL: #{ confidenceScore: low }, NAME: #{ confidenceScore: low }, PHONE: #{ confidenceScore: low }, US_SOCIAL_SECURITY_NUMBER: #{ confidenceScore: low }, IP_ADDRESS: #{ confidenceScore: low }, URL: #{ confidenceScore: low }, PASSWORD: #{ confidenceScore: low }, USERNAME: #{ confidenceScore: low }, DRIVER_ID: #{ confidenceScore: low }, PIN: #{ confidenceScore: low }, AWS_ACCESS_KEY: #{ confidenceScore: low }, AWS_SECRET_KEY: #{ confidenceScore: low }, LICENSE_PLATE: #{ confidenceScore: low }, MAC_ADDRESS: #{ confidenceScore: low }, SWIFT_CODE: #{ confidenceScore: low }, CREDIT_DEBIT_CARD_CVV: #{ confidenceScore: low }, CREDIT_DEBIT_CARD_EXPIRY: #{ confidenceScore: low }, INTERNATIONAL_BANK_ACCOUNT_NUMBER: #{ confidenceScore: low }, US_BANK_ACCOUNT_NUMBER: #{ confidenceScore: low }, US_BANK_ROUTING_NUMBER: #{ confidenceScore: low }, US_INDIVIDUAL_TAX_IDENTIFICATION_NUMBER: #{ confidenceScore: low }, US_PASSPORT_NUMBER: #{ confidenceScore: low }, VEHICLE_IDENTIFICATION_NUMBER: #{ confidenceScore: low }, UK_NATIONAL_HEALTH_SERVICE_NUMBER: #{ confidenceScore: low }, UK_NATIONAL_INSURANCE_NUMBER: #{ confidenceScore: low }, UK_UNIQUE_TAXPAYER_REFERENCE_NUMBER: #{ confidenceScore: low }, CA_HEALTH_NUMBER: #{ confidenceScore: low }, CA_SOCIAL_INSURANCE_NUMBER: #{ confidenceScore: low } };
    }
    let hit = false;
    for t in texts { if to_lower(t).contains("ssn") { hit = true; } }
    let s = if hit { parse_decimal("0.9") } else { low };
    let c = if hit { "HIGH" } else { "NONE" };
    #{ ADDRESS: #{ confidenceScore: s }, AGE: #{ confidenceScore: low }, CREDIT_DEBIT_CARD_NUMBER: #{ confidenceScore: low }, EMAIL: #{ confidenceScore: low }, NAME: #{ confidenceScore: low }, PHONE: #{ confidenceScore: low }, US_SOCIAL_SECURITY_NUMBER: #{ confidenceScore: low }, IP_ADDRESS: #{ confidenceScore: low }, URL: #{ confidenceScore: low }, PASSWORD: #{ confidenceScore: low }, USERNAME: #{ confidenceScore: low }, DRIVER_ID: #{ confidenceScore: low }, PIN: #{ confidenceScore: low }, AWS_ACCESS_KEY: #{ confidenceScore: low }, AWS_SECRET_KEY: #{ confidenceScore: low }, LICENSE_PLATE: #{ confidenceScore: low }, MAC_ADDRESS: #{ confidenceScore: low }, SWIFT_CODE: #{ confidenceScore: low }, CREDIT_DEBIT_CARD_CVV: #{ confidenceScore: low }, CREDIT_DEBIT_CARD_EXPIRY: #{ confidenceScore: low }, INTERNATIONAL_BANK_ACCOUNT_NUMBER: #{ confidenceScore: low }, US_BANK_ACCOUNT_NUMBER: #{ confidenceScore: low }, US_BANK_ROUTING_NUMBER: #{ confidenceScore: low }, US_INDIVIDUAL_TAX_IDENTIFICATION_NUMBER: #{ confidenceScore: low }, US_PASSPORT_NUMBER: #{ confidenceScore: low }, VEHICLE_IDENTIFICATION_NUMBER: #{ confidenceScore: low }, UK_NATIONAL_HEALTH_SERVICE_NUMBER: #{ confidenceScore: low }, UK_NATIONAL_INSURANCE_NUMBER: #{ confidenceScore: low }, UK_UNIQUE_TAXPAYER_REFERENCE_NUMBER: #{ confidenceScore: low }, CA_HEALTH_NUMBER: #{ confidenceScore: low }, CA_SOCIAL_INSURANCE_NUMBER: #{ confidenceScore: low } }
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
