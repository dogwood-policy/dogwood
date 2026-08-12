# 0019 — Underscore digit-separator in `\u{...}` gives the right verdict

Second wrong-verdict regression case for commit `fc46e9db` (the first is
`0018_string_escape_hex_verdict`, for `\xHH`). This one pins a *different*
buggy code path: the `\u{...}` decoder.

## The bug

Cedar decodes string escapes with Rust's escape grammar, which allows `_`
digit separators inside `\u{...}`. So `"\u{4_1}"` is the single character `A`
(code point 0x41), exactly as `"\u{41}"` is.

The pre-fix `decode_string` decoded the braced body with
`u32::from_str_radix(hex, 16)`. That function rejects underscores, so the
parse failed and the code fell into its "malformed — pass through" branch,
emitting the seven characters `\ u { 4 _ 1 }` verbatim. Like the `\xHH` facet,
this is a **silently wrong value**, not a parse error: the policy validates and
then makes the wrong decision.

## What this case exercises

The policy permits `Read` only when `context.input.document == "\u{4_1}"`.

- `@0` reads a document that IS `"A"`. Correct verdict `true` (the literal
  decodes to `A`). On the buggy prefix the literal is the 7-char string
  `\u{4_1}`, so the guard fails and the verdict is the wrong `false`.
- `@10` reads `"B"` as a control: `false` on both.

On the pre-fix parser `mixed_cases_verdicts` yields `@0 … false` and fails the
comparison; after the fix it yields `@0 … true` and the case is green.
