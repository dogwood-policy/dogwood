# 0203 — String equality and inequality

Numeric comparisons (0002) cover ordered fields like `shares`.
For string-typed inputs like `context.input.stock`, the operators
you reach for are `==` and `!=`.

## Denylist with `!=`

`policy_1.dw` permits `GetStockInfo` for every ticker except one:

```
when {
    context.input.stock != "BLOCKED"
};
```

String literals are written in double quotes. The comparison is
an **exact, case-sensitive match** on the entire string —
`"blocked"`, `"BLOCKED "` (trailing space), and `"BLOCKEDX"`
would all satisfy `!= "BLOCKED"`. There is no implicit
trimming or case folding.

## Allowlist with `==` and `||`

`policy_2.dw` flips the polarity: instead of naming what is
forbidden, it enumerates what is permitted.

```
when {
    context.input.stock == "AMZN"
    || context.input.stock == "MSFT"
    || context.input.stock == "GOOG"
};
```

The two policies illustrate the same trade-off as 0002 vs 0108:
write the form whose intent reads more directly. Allowlists tend
to be safer (anything new is denied by default); denylists tend
to be terser when the excluded set is small.

String equality is the bluntest tool available for matching
strings. The next case (0204) introduces `like` for glob-style
prefix and suffix patterns, which is what you want when an
exact-match enumeration would be unwieldy.
