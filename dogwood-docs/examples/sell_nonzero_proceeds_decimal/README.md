# sell_nonzero_proceeds_decimal

Decimal supports **equality only** (`==` / `!=`); ordered comparison on
decimals does not type-check. This policy permits `SellShares` only when the
sale's `proceeds` is not zero, using `!=`. The optional `output` attribute is
guarded first with `context has output` before its field is read.

Referenced by `guide/02-policy-language.md` — The Policy Language.
