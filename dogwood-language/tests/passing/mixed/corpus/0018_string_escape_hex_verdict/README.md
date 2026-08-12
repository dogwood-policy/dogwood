# 0018 — String-literal `\xHH` escape produces the right verdict

Regression corpus case for commit `fc46e9db`
("fix(parser): decode string literals with Cedar's unescaper").

## The bug

Dogwood shares Cedar's string-literal syntax, so a literal must decode to the
same value in both. Cedar decodes `"\x41"` to the single character `A`. Before
the fix, Dogwood's hand-rolled `decode_string` did not recognize the `\x`
escape at all and produced the four literal characters `\`, `x`, `4`, `1`.

That is not a parse error — it is a **silently wrong value**, which is the worst
kind: the policy validates cleanly and then makes the wrong decision at
runtime. Any `context.input.document == "\x41"` comparison could never match a
real `document == "A"` event, so a rule that should `permit` instead `deny`s.

## What this case exercises

The policy permits `Read` only when `context.input.document == "\x41"`.

- `@0` reads a document that IS `"A"`. Correct verdict: `true` (the literal
  decodes to `A`, the guard holds). On the buggy prefix the literal is the
  4-char string `\x41`, the guard fails, and the verdict is the wrong `false`.
- `@10` reads `"B"` as a control: `false` on both, so the case pins that the
  guard is real and not vacuously true.

Running the `mixed_cases_verdicts` harness on the pre-fix parser yields
`@0 … false` and fails the expected-verdict comparison; after the fix it yields
`@0 … true` and the case is green.
