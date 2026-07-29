# 0003 — Decimal output + Cedar decimal-method comparison

Shows a provider whose output is a **decimal**, compared using Cedar's
decimal extension method form (`.lessThan(decimal("..."))`) instead of a
bare operator (Cedar decimals are not comparable with `<`).

- **`providers.json`** declares `Content::Risk` returning
  `{ severityScore: decimal }`.
- **`risk.rhai`** returns a fixed score per keyword: `"safe"` → 0.10,
  `"spam"` → 0.80, anything else → 0.50. It builds the decimal with
  Rhai's `parse_decimal` (the engine is built with the `decimal`
  feature), so the value reaches Cedar as a real decimal.
- **`policy_1.dw`** permits `Read` only when the score is below 0.5:
  `Content::Risk(context.input.document).severityScore.lessThan(decimal("0.5"))`.

So `"safe"` (0.10) → permit, `"spam"` (0.80) → deny, `"other"` (0.50) →
deny (0.5 is not *less than* 0.5).
