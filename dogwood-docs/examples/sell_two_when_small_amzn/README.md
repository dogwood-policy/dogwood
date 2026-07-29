# sell_two_when_small_amzn

Two `when` clauses stacked on one rule are implicitly conjoined: **both** must
hold. Here `SellShares` is permitted only when the order is small
(`shares < 100`) **and** the stock is `"AMZN"` — equivalent to a single
`when { context.input.shares < 100 && context.input.stock == "AMZN" }`, but
split for readability.

Referenced by `guide/02-policy-language.md` — The Policy Language.
