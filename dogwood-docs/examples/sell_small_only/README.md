# sell_small_only

The canonical five-part rule shape: annotation + effect + parenthesized scope
triple + a single `when` clause + terminating semicolon. It permits
`SellShares` only for small orders — 50 shares or fewer
(`context.input.shares <= 50`).

The trace exercises both outcomes:

- `@0` — alice sells exactly 50 shares → **allow** (`50 <= 50` holds).
- `@100` — bob sells 500 shares → **deny** (threshold exceeded).
- `@200` — carol sells 10 shares → **allow**.

Referenced by `guide/02-policy-language.md` — The Policy Language.
