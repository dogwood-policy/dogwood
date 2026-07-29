# provider_digitcount_operator_ge

The operator-form comparison example (`>=` on an integer provider output),
promoted from a guardrail fragment to a standalone `permit`. Permit `Read` only
when the document contains **two or more digits**, as counted by the
`Strings::DigitCount` provider:

```
Strings::DigitCount(context.input.document).count >= 2
```

`Strings::DigitCount(text) -> { count: Long }` counts `[0-9]` matches via the
`regex_count` host function (see `digits.rhai`). The provider script is inlined
into `providers.json` because the CLI reads that file as text and does not
resolve `scriptFile` references; `digits.rhai` is kept as the readable source.

The trace over four documents:

- `@0`  — `"abc"`   (0 digits) → **DENY**
- `@10` — `"a1b"`   (1 digit)  → **DENY**
- `@20` — `"a1b2"`  (2 digits) → **ALLOW**
- `@30` — `"12345"` (5 digits) → **ALLOW**

Referenced by `guide/05-information-providers.md`.
