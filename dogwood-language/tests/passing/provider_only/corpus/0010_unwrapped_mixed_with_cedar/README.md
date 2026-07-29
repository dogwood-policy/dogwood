# 0010 — Unwrapped provider composed with arbitrary Cedar

Shows what the unwrapped form unlocks that the closed `guardrails { … }`
grammar cannot express — the provider output is just an ordinary Cedar
sub-expression, so it composes freely:

```
permit (...) when {
    context.input.trusted == true
    && Strings::DigitCount(context.input.document).count + 1 <= 3
};
```

- A provider atom (`Strings::DigitCount(...).count`) mixed with a plain
  Cedar condition (`context.input.trusted == true`) under `&&`.
- The provider's **integer output used inside arithmetic**
  (`count + 1 <= 3`), not merely a bare comparison — impossible in the
  wrapped form, whose grammar requires `invocation ~ projection ~
  comparison`.

`Strings::DigitCount` counts `[0-9]` via a regex host function, so the
guard is "trusted AND at most two digits" (`count + 1 <= 3` ⇔
`count <= 2`):

| trusted | document | digits | verdict |
|---------|----------|--------|---------|
| true    | `ab`     | 0      | permit  |
| true    | `a1b2`   | 2      | permit  |
| true    | `a1b2c3` | 3      | deny    |
| false   | `ab`     | 0      | deny    |
