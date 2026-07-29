// `Time::WithinHours(hour) -> { ok: Bool }`.
//
// True when `hour` is within business hours (9 <= hour < 17). The `hour`
// argument comes from `context.system.hour` — a non-`input` request-context
// group — exercising that a provider reads its `context.<path>` args from the
// request context record.
fn evaluate(hour) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(hour) == "()" {
        return #{ ok: false };
    }

    #{ ok: hour >= 9 && hour < 17 }
}
