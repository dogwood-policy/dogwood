# provider_risk_decimal_method

The decimal-extension-method comparison form. The `Content::Risk` provider
returns a record whose `severityScore` field is a Cedar `decimal`, so the policy
compares it with the decimal extension method `.lessThan(decimal("0.5"))` rather
than the bare `<` operator (Cedar decimals are not comparable with `<`).

`providers.json` declares `Content::Risk(string) -> { severityScore: decimal }`.
The Rhai script is **inlined** into `providers.json` (as `script`) rather than
referenced via `scriptFile`, because the `dogwood` CLI reads the providers file
as raw text and does not resolve `scriptFile` paths. The equivalent standalone
`risk.rhai` is included for readability. It returns a fixed score per keyword:
`"safe"` -> 0.10, `"spam"` -> 0.80, anything else -> 0.50.

The trace shows all three cases:

- `@0` — `document: "safe"` (score 0.10, below 0.5) -> **ALLOW**.
- `@10` — `document: "spam"` (score 0.80) -> **DENY**.
- `@20` — `document: "other"` (score 0.50, not *less than* 0.5) -> **DENY**.

Referenced by `guide/05-information-providers.md`.
