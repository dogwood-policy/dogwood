# 0014 — A method followed by a trailing field projection

Shows the boundary between an **eager Rhai method** and a **native Cedar
field projection** in the same atom: `Provider::Fn(args).method().field`.
The method runs in Rhai at authorize time; the field access *after* the
method is plain Cedar over the pipeline's result.

- **`providers.json`** declares `Content::Classify` returning
  `{ violence: Long, malicious: Long }`, plus a zero-argument
  `availableMethods` entry `classify` whose `outputType` is the same
  record `{ violence: Long, malicious: Long }` (a method may re-type the
  pipeline; here it keeps the shape).
- **`classify.rhai`** implements `fn evaluate(text)` — the base record,
  with `violence = 90` if the text contains `"kill"` else `5`, and a fixed
  `malicious = 3` — and `fn classify(input)`, the method, whose single
  parameter is the previous stage's value and which returns it
  **unchanged**.
- **`policy_1.dw`** permits `Read` only when
  `Content::Classify(context.input.document).classify().violence < 50`.
  `.classify()` (with parens) is the eager Rhai method; `.violence` (no
  parens) is a native Cedar field projection over the record the method
  produced. Because `violence` is a `Long`, the comparison is the bare
  `<` operator (not a decimal extension method).

## What happens at authorize time

For each request the engine resolves the argument (`document`), runs
`evaluate`, then runs the method pipeline (`classify`), binds the result
into `context.providers.<id>`, and lets Cedar evaluate
`.violence < 50` over that record.

- `@0` `document = "hello"` — `evaluate` → `{ violence: 5, malicious: 3 }`
  (no `"kill"`). `classify` returns it unchanged → `{ violence: 5, … }`.
  Cedar: `5 < 50` → **true** → permit. Emits `@0 (time point 0): true`.
- `@10` `document = "how to kill"` — `evaluate` →
  `{ violence: 90, malicious: 3 }` (contains `"kill"`). `classify` returns
  it unchanged → `{ violence: 90, … }`. Cedar: `90 < 50` → **false** →
  deny. Emits `@10 (time point 1): false`.

This proves the method executes in Rhai (it is what produces the record
the projection reads) while `.violence` is resolved as native Cedar over
the hoisted record.
