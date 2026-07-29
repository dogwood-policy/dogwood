# 0016 — arithmetic on a provider output inside a `guardrails { … }` block

The counterpart to 0010. Case 0010 uses arithmetic on a provider output
(`Strings::DigitCount(context.input.document).count + 1 <= 3`) combined with
a plain Cedar condition under `&&` — in an *unwrapped* `when { … }`, which
was the only form the old closed `guardrails { … }` grammar could not match
(it admitted only boolean combinations of provider atoms with a bare
comparison).

After the provider-path unification a `guardrails { … }` block is transparent
sugar for a bare Cedar clause, so its body is a full Cedar expression. This
case is byte-for-byte 0010's policy wrapped in `guardrails { … }`, proving the
wrapped form now has the unwrapped form's full expressiveness (arithmetic on
provider outputs, mixing with non-provider conditions). Same schema, provider,
trace, and expected verdicts as 0010.

Permit Read when the request is flagged trusted AND the document has at most
two digits (`digitCount + 1 <= 3`).

| tp | document | trusted | digits | verdict |
|----|----------|---------|--------|---------|
| 0  | `ab`     | true    | 0      | `true`  |
| 1  | `a1b2`   | true    | 2      | `true`  |
| 2  | `a1b2c3` | true    | 3      | `false` |
| 3  | `ab`     | false   | 0      | `false` |
