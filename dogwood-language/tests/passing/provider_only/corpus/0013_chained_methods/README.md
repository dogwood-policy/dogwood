# 0013 — Chained methods on a provider's output

Shows two **methods** chained on a provider's output, threaded
left-to-right. Beyond projecting a field (`.raw`), a method
*post-processes* the value, and methods compose: `.m1().m2()` evaluates
as `m2(m1(output))`, each stage feeding the next.

- **`providers.json`** declares `Text::Analyze` returning `{ raw: Long }`,
  plus an `availableMethods` map with two zero-argument methods,
  `normalize` and `clamp`, each declared `outputType` `integer`.
- **`analyze.rhai`** implements them. A method's **first parameter is the
  previous stage's value**: `normalize`'s input is the base `evaluate`
  record (so it reads `input.raw`); `clamp`'s input is `normalize`'s
  integer result. `evaluate` returns `raw = text.len()`; `normalize()` =
  `raw * 10`; `clamp()` = cap at 100 (`if input > 100 { 100 } else { input }`).
- **`policy_1.dw`** permits `Read` only when the pipeline result is below
  100: `Text::Analyze(context.input.document).normalize().clamp() < 100`.
  The output is an integer, so the comparison uses the bare `<` operator.

## What happens

For each request the engine runs the pipeline
`clamp(normalize(evaluate(document)))`, binds the integer result into
`context.providers.<id>`, and Cedar evaluates `< 100`:

- `"ab"` — `len = 2` → `normalize` `2 * 10 = 20` → `clamp(20)` (20 not >
  100) `= 20` → `20 < 100` is **true** → Allow.
- `"abcdefghij"` — `len = 10` → `normalize` `10 * 10 = 100` → `clamp(100)`
  (100 not > 100) `= 100` → `100 < 100` is **false** → Deny.
- `"abcde"` — `len = 5` → `normalize` `5 * 10 = 50` → `clamp(50)` (50 not
  > 100) `= 50` → `50 < 100` is **true** → Allow.

So the verdict stream is `true`, `false`, `true`. Note `clamp(100) = 100`
because 100 is *not* greater than 100, and `100 < 100` is false — the
middle request is denied.
