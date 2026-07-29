# 0012 — N-argument output method (`.above(decimal(…))`)

Shows a provider **method** that takes its own argument and returns a new
type. Where 0003 compared the provider's decimal output with Cedar's
`.lessThan(decimal(…))` *extension* method, here the threshold check is
pushed *inside* the provider as a declared method: `.above(threshold)`
takes a `decimal` argument and returns a `Bool`. The clause body is then a
plain boolean comparison.

- **`providers.json`** declares `Risk::Score` returning
  `{ score: decimal }`, plus an `availableMethods` entry `above` whose
  `argumentTypes` is `[{ paramType: decimal }]` and whose `outputType` is
  `bool`. Declaring a method re-types the pipeline: after `.above(…)` the
  value the policy sees is a `Bool`, not the base record.
- **`risk.rhai`** defines the base `fn evaluate(text)` (a fixed score per
  keyword via `parse_decimal`) **and** the method `fn above(o, threshold)`.
  A method's first parameter is the previous stage's value — here the base
  record `#{ score: <decimal> }` — and the rest are its own resolved
  arguments (the decimal `threshold`). It returns `o.score > threshold`.
- **`policy_1.dw`** is an `unless` guardrail: it permits `Read`
  **unless** `Risk::Score(context.input.document).above(decimal("0.5")) == true`.
  So the permit is suppressed exactly when the score is strictly above 0.5.

## What happens at authorize time

For each request the engine runs `evaluate(document)` to get the base
record, then threads it through the method chain — here just
`above(base, decimal("0.5"))` — and binds the resulting `Bool` into
`context.providers.<id>`. Cedar then evaluates `… == true` and, because the
clause is `unless`, denies when that is true.

Walking the trace (threshold = 0.5, comparison is strict `>`):

| ts  | tp | document | `evaluate` score | `above(0.5)` = `score > 0.5` | body `== true` | `unless` fires? | decision |
|-----|----|----------|------------------|------------------------------|----------------|-----------------|----------|
| @0  | 0  | `safe`   | 0.10             | `0.10 > 0.50` = **false**    | false          | no              | **Allow** |
| @10 | 1  | `bad`    | 0.90             | `0.90 > 0.50` = **true**     | true           | yes             | **Deny**  |
| @20 | 2  | `other`  | 0.50             | `0.50 > 0.50` = **false**    | false          | no              | **Allow** |

`@20` is the boundary case: 0.50 is **not** strictly greater than 0.50, so
`above` is false, the `unless` body is false, and the permit stands.

Every request emits a verdict line (`true` for Allow, `false` for Deny), so
`expected_1.out` is:

```
@0 (time point 0): true
@10 (time point 1): false
@20 (time point 2): true
```
