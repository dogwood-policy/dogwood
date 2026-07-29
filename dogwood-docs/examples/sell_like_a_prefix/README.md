# sell_like_a_prefix

The `like` operator matches a string against a wildcard pattern, where `*`
matches any number of characters. This policy permits `SellShares` only when
`context.input.stock` starts with the letter `A` (`like "A*"`).

The trace shows both outcomes:

- `@0` — alice sells `AMZN` (starts with `A`) → **allow**.
- `@100` — bob sells `AAPL` (starts with `A`) → **allow**.
- `@200` — carol sells `MSFT` (does not start with `A`) → **deny**.

Referenced by `guide/02-policy-language.md` — The Policy Language.
