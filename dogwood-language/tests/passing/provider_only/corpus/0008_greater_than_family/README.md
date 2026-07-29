# 0008 — `>=` operator form, provider in a `forbid` rule

Complements 0002 (`<`) with the greater-than side of the operator family,
and shows a guardrail clause inside a **`forbid`** rule (the effect is
orthogonal to the dialect — a provider atom is just a Boolean leaf):

```
forbid (...) when guardrails {
    Strings::DigitCount(context.input.document).count >= 2
};
permit (...);   // allow Read by default; the forbid above overrides it
```

- **`digits.rhai`** — `Strings::DigitCount(text) -> { count: Long }`, using
  the `regex_count` host function to count `[0-9]` occurrences.

The bare `permit` allows every Read; the `forbid` clause then denies any
document with two or more digits (Cedar's forbid overrides permit):
`"abc"` (0 digits) → **permit**, `"a1b"` (1) → **permit**,
`"a1b2"` (2) → **deny**, `"12345"` (5) → **deny**.
