// `Policy::Check(document, tags) -> { confidence: decimal, approved: Bool }`
//
// `tags` is a mixed set (e.g. ["ALLOW", "public"]). The policy check
// approves if the tags contain "ALLOW" AND the document is not "blocked".
// Confidence is 0.9 when approved, 0.1 when not.
fn evaluate(document, tags) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(document) == "()" || type_of(tags) == "()" {
        return #{ confidence: parse_decimal("-1.0"), approved: false };
    }

    let has_allow = false;
    for t in tags {
        if t == "ALLOW" {
            has_allow = true;
        }
    }

    let approved = has_allow && document != "blocked";
    let confidence = if approved {
        parse_decimal("0.9")
    } else {
        parse_decimal("0.1")
    };

    #{ confidence: confidence, approved: approved }
}
