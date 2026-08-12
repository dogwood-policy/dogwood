# 0021 — Underscore digit-separator in a `like` pattern's `\u{...}`

Regression case for the `build_pattern` divergence — the `like`-pattern
analogue of `0019_string_escape_unicode_underscore_verdict`, pinning a
different buggy `build_pattern` code path (the `\u{...}` decoder) than `0020`.
`build_pattern` is not fixed by commit `fc46e9db`.

## The bug

Cedar decodes escapes with Rust's grammar, which permits `_` digit separators
inside `\u{...}`, so `like "\u{4_1}"` is the single-character pattern `A`. The
current `build_pattern` decodes the braced body with `u32::from_str_radix`,
which rejects underscores; the decode fails and the code falls into its
"malformed — pass through" branch, emitting the seven literal characters
`\ u { 4 _ 1 }` as the pattern. A silently wrong pattern, not a parse error.

## What this case exercises

The policy permits `Read` only when `context.input.document like "\u{4_1}"`.

- `@0` reads document `"A"`. Correct verdict `true` (the pattern is `A`). On
  the buggy parser the pattern is the literal `\u{4_1}`, so `"A"` does not match
  → wrong `false`.
- `@10` reads `"B"` as a control: `false` on both.
