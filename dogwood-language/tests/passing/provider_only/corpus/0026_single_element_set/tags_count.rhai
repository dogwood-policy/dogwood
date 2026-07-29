// Returns the number of tags that match substrings in the document.
// With an empty tags set, count should always be 0.
fn evaluate(document, tags) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(document) == "()" || type_of(tags) == "()" {
        return #{ count: -1 };
    }

    let count = 0;
    for tag in tags {
        if document.contains(tag) {
            count += 1;
        }
    }
    #{ count: count }
}
