# cedar_within_cap_if_else

A `def cedar` macro whose body is an `if/then/else` expression, encoding a
per-stock share cap: `within_cap(?stock, ?shares)` returns `?shares <= 10` for
stock `"FOO"` and `?shares <= 1000` otherwise. Two params of different types
(`String` and `Long`) are spliced into one Cedar expression.

The macro is promoted here to a full `permit` rule on `Drupe::Action::"SellShares"`,
reading `context.input.stock` and `context.input.shares` (the `SellSharesInput`
type from the Drupe schema).

Referenced by `guide/06-macros.md`.
