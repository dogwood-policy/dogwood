# forbid_large_except_amzn

Mixing `when` and `unless` on a **`forbid`** rule: block large `SellShares`
(`context.input.shares > 100`), but carve out an exemption for AMZN
(`unless { context.input.stock == "AMZN" }`).

Because this bundle has only a `forbid` rule and no `permit`, every request is
denied — there is nothing that can produce an allow. What the trace shows is
*why* each request is denied:

- `@0` — alice sells 500 MSFT → the forbid **fires** (large, not AMZN) →
  `DENY  [rules: 0]` (actively blocked by the rule).
- `@100` — alice sells 500 AMZN → `unless` exempts AMZN, so the forbid does
  **not** fire → `DENY` (Cedar's default deny; no `permit` applies).
- `@200` — bob sells 50 MSFT → `when { shares > 100 }` is false, so the forbid
  does **not** fire → `DENY` (below the threshold; again default deny).

The `[rules: …]` annotation distinguishes an *actively forbidden* request from
one that simply falls through to the default deny.

Referenced by `guide/02-policy-language.md` — The Policy Language.
