# sell_shares_temporal_subexpr

A `temporal { ... }` marker used as a **sub-expression** inside a larger Cedar
`&&` condition, rather than as the whole `when` body. The rule permits
`SellShares` when the share count clears a threshold **and** a temporal marker
holds:

```text
when { context.input.shares > 5 && temporal { formerly within 1h Drupe::Action::"SellShares"::request{} } }
```

`formerly` looks at `[0, i]` inclusive, and the bare `SellShares::request{}`
body has no correlation pins, so the current `SellShares` event always
self-matches the temporal half. That makes the Cedar `context.input.shares > 5`
conjunct the deciding factor here — which is exactly the point: the temporal
marker composes as an ordinary primary expression under `&&`.

The trace shows both outcomes:

- `@0` — alice sells 10 shares (`shares > 5`, temporal holds) -> **allow**.
- `@100` — alice sells 3 shares (`shares > 5` is false) -> **deny**.

Referenced by `guide/02-policy-language.md` — The Policy Language.
