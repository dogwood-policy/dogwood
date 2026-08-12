# 0020 — `\xHH` escape in a `like` pattern gives the right verdict

Regression case for the `build_pattern` divergence — the `like`-pattern
analogue of `0018_string_escape_hex_verdict`. Commit `fc46e9db` fixed the plain
string-literal decoder (`decode_string`) but explicitly left `build_pattern`
unfixed, because Cedar's counterpart `to_pattern` was `pub(crate)`. This case
pins the resulting wrong-verdict bug so a future `build_pattern` fix can be
verified against it.

## The bug

Cedar decodes `like "\x41"` to the single-character pattern `A` (it shares the
string escape grammar, plus `*`/`\*` for wildcard/literal-star). The current
`build_pattern` has no `\x` arm: the `\` case matches `Some('x') => Char('x')`
and then emits `4` and `1` as ordinary characters, so the pattern is the three
characters `x41`. That is a **silently wrong pattern**, not a parse error — the
policy validates and then matches the wrong strings.

## What this case exercises

The policy permits `Read` only when `context.input.document like "\x41"`.

- `@0` reads document `"A"`. Correct verdict `true` (the pattern is `A`). On
  the buggy parser the pattern is `x41`, so `"A"` does not match → wrong
  `false`.
- `@10` reads document `"x41"`. Correct verdict `false` (the pattern `A` does
  not match `"x41"`). On the buggy parser the pattern IS `x41`, so it matches →
  wrong `true`.

Both timepoints flip, so this case fails loudly on the buggy pattern regardless
of which direction the mis-decode is read.
