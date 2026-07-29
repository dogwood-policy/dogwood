# 0204 — String pattern matching with `like`

Cedar's `like` operator tests whether a string matches a pattern.
The only metacharacter is `*`, which matches any sequence of
characters (including the empty string). A literal `*` is
escaped as `\*`.

## Shape

```cedar
when { context.input.stock like "A*" }
```

This matches any ticker whose first character is `A` —
`"AAPL"`, `"AMZN"`, `"A"` itself — and rejects `"MSFT"`,
`"GOOG"`, etc.

## Common patterns

| Pattern | Meaning | Matches | Doesn't match |
|---|---|---|---|
| `"A*"`    | prefix    | `"AAPL"`, `"AMZN"` | `"MSFT"` |
| `"*N"`    | suffix    | `"AMZN"`, `"TSN"`  | `"AAPL"` |
| `"*MZ*"`  | substring | `"AMZN"`, `"XMZY"` | `"AAPL"` |
| `"AAPL"`  | exact     | `"AAPL"` only      | everything else |

## When to use it

`like` is a coarse tool: it can only express prefix, suffix,
substring, and combinations thereof. Prefer an explicit set
membership check (e.g. `context.input.stock == "AAPL" ||
context.input.stock == "AMZN"`) when the set of allowed
strings is small and known. Reach for `like` when you genuinely
want a pattern — for instance, allowlisting an entire ticker
family by prefix, or filtering anything containing a substring.
