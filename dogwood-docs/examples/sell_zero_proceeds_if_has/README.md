# sell_zero_proceeds_if_has

The `if C has attr then ... else false` idiom guards an optional output field.
Here `SellShares` has an optional `output` record (`output?: SellSharesOutput`),
so `if context has output then context.output.proceeds == decimal("0.0") else false`
reads `proceeds` only when the output is present and falls back to `false` when it
is absent — avoiding an error on the missing optional field.

Referenced by `guide/02-policy-language.md` — The Policy Language.
