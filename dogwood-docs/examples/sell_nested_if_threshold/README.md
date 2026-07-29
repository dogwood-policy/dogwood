# sell_nested_if_threshold

Nested `if/then/else` used as an **operand** rather than a top-level
conditional: the chained conditional computes a per-stock share cap
(`AMZN` → 10, `MSFT` → 50, everything else → 1000), and the `<=` comparison
checks the request's `shares` against it. Permits `SellShares` only when the
requested share count stays under that stock's cap.

Referenced by `guide/02-policy-language.md` — The Policy Language.
