// `Access::Level(document) -> { level: Long }`
// plus multi-arg method `checkLevel(principal_id, threshold) -> Long`
//
// `evaluate` returns a base level based on the document name.
// `checkLevel` takes the principal id string and an integer threshold;
// if the principal is "blocked", returns the threshold (causing != to
// fail), otherwise returns 0 (which != threshold succeeds).
fn evaluate(document) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(document) == "()" {
        return #{ level: -1 };
    }

    let level = if document == "secret" { 99 } else { 10 };
    #{ level: level }
}

// Multi-arg method: takes (input = previous stage output, principal_id, threshold)
fn checkLevel(input, principal_id, threshold) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(principal_id) == "()" || type_of(threshold) == "()" {
        return -1;
    }

    if principal_id == "blocked" {
        threshold
    } else {
        0
    }
}
