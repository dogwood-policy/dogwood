# sell_small_proceeds_decimal_method

Decimal `.lessThan(...)` method call — how decimals are ordered. Cedar decimals
are **not** comparable with `<` / `<=` (those do not type-check on `decimal`);
you must use the decimal comparison methods (`lessThan`, `lessThanOrEqual`,
`greaterThan`, `greaterThanOrEqual`).

Here the policy permits `SellShares` only when the (optional) output's
`proceeds` is below `decimal("0.5")`. Because `output` is an optional context
attribute, the condition guards it with `context has output` before projecting
`context.output.proceeds`.

Adapted to `SellSharesOutput.proceeds` (a `decimal`) because the Drupe
schema has no `severityScore` action field to compare against.

Referenced by `guide/02-policy-language.md` — The Policy Language.
