# 0200 - The full set of integer comparison operators

`context.input.shares` on `SellShares` is declared `Long`, so the
full suite of ordered comparisons is available on it. This case
spreads those operators across two contrasting rules.

## The six operators

`Long` (and any other integer field) supports:

| Operator | Meaning                  |
|----------|--------------------------|
| `==`     | equal                    |
| `!=`     | not equal                |
| `<`      | strictly less than       |
| `<=`     | less than or equal       |
| `>`      | strictly greater than    |
| `>=`     | greater than or equal    |

`policy_1.dw` permits `SellShares` only when `shares` is in the
closed range `[1, 1000]` and is not exactly `777` - exercising
`>=`, `<=`, and `!=` on a single field. `policy_2.dw` adds a
`forbid` rule using `>` to block trades larger than `10000`. By
deny-overrides (see 0003), the forbid wins on any overlap, so the
effective permit shape is "in [1, 1000] and not 777".

## Contrast with `decimal`

Decimal fields - for example `context.output.proceeds` on
`SellShares` - support **only** `==` and `!=`. Writing
`context.output.proceeds < decimal("100.0")` would fail
type-checking. When you need ordered comparisons, model the field
as `Long` (as `shares` is here) or aggregate decimals into a sum
inside a temporal clause and compare the sum for equality.
