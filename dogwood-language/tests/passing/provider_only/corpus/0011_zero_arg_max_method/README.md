# 0011 — A zero-argument output method (the `maxConfidenceScore()` case)

This case exercises a **provider output method** with **no arguments** — the
reference-parity accessor form. Where earlier cases projected into a provider's
output with a field (`.matched`) or an index (`["VIOLENCE"]`), here the policy
calls a *declared method* on the output that post-processes it into a new value.

Read the files in this order:

1. **`providers.json`** — declares `BedrockGuardrails::ContentFilter`. Its
   base `outputType` is a record `{ violence: Long, malicious: Long }`. The
   new part is the **`availableMethods`** block: it declares one method,
   `maxConfidenceScore`, with an empty `argumentTypes` (zero args) and an
   `outputType` of `integer`. Declaring the method re-types the pipeline —
   after the method runs, the value the policy compares is a single `Long`,
   not the record.

2. **`content_filter.rhai`** — the provider's implementation. `fn evaluate(text)`
   produces the base score record; `fn maxConfidenceScore(input)` is the
   method. A method's **first parameter is the previous pipeline stage's
   value** (here the `evaluate` record); a zero-argument method takes only
   that receiver and no further parameters. `maxConfidenceScore` returns the
   larger of the two category scores. `to_lower` + `.contains` give a
   case-insensitive substring test.

3. **`policy_1.dw`** — permits `Read` only when
   `BedrockGuardrails::ContentFilter(context.input.document).maxConfidenceScore() < 50`.
   The `.maxConfidenceScore()` is a method-call accessor (distinguished from a
   field access by the trailing `()`); the `< 50` is the terminal comparison.

4. **`schema.cedarschema`** — the base `Read` action schema (un-augmented).

5. **`trace_1.log`** — three `Read` requests differing only in `document`.

6. **`expected_1.out`** — one verdict line per request: `true` for Allow,
   `false` for Deny.

## What happens at authorize time

For each request the engine runs `evaluate(document)` to get the base score
record, then threads it through the method chain — here a single call
`maxConfidenceScore(record)` — and binds the resulting `Long` into
`context.providers.<id>`. Cedar then evaluates `<that Long> < 50`.

Walking each trace event (`violence = 90` if the lowered text contains
`"kill"` else `5`; `malicious = 80` if it contains `"exploit"` else `3`;
`maxConfidenceScore = max(violence, malicious)`):

| ts | document      | violence | malicious | max | `max < 50` | verdict |
|----|---------------|----------|-----------|-----|------------|---------|
| 0  | `hello`       | 5        | 3         | 5   | true       | Allow → `true`  |
| 10 | `how to kill` | 90       | 3         | 90  | false      | Deny  → `false` |
| 20 | `an exploit`  | 5        | 80        | 80  | false      | Deny  → `false` |

So the verdict stream is `true`, `false`, `false`.
