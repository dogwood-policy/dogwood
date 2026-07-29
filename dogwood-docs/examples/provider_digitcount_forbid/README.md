# provider_digitcount_forbid

A provider gating a **`forbid`** rule, alongside a catch-all `permit` -- showing
that a provider call is orthogonal to the rule effect. The same
`Strings::DigitCount(context.input.document).count >= 2` atom that *permits*
Read in `provider_digitcount_operator_ge` here *forbids* it, so the verdicts are
the exact inverse:

```
@id("forbid_digits")
forbid (...) when { Strings::DigitCount(context.input.document).count >= 2 };
@id("permit_read")
permit (...);   // catch-all: allow Read by default; the forbid overrides it
```

`Strings::DigitCount(text) -> { count: Long }` counts `[0-9]` matches via the
`regex_count` host function (see `digits.rhai`). The provider script is inlined
into `providers.json` because the CLI reads that file as text and does not
resolve `scriptFile` references; `digits.rhai` is kept as the readable source.

The trace over four documents (Cedar's forbid overrides the catch-all permit):

- `@0`  — `"abc"`   (0 digits) → **ALLOW**
- `@10` — `"a1b"`   (1 digit)  → **ALLOW**
- `@20` — `"a1b2"`  (2 digits) → **DENY**
- `@30` — `"12345"` (5 digits) → **DENY**

Referenced by `guide/05-information-providers.md`.
