# 0018 — multiple `when guardrails` clauses

The runnable, regex-backed analog of the reference
`documentation_0406_multiple_guardrail_clauses`: one rule carries two
`when guardrails { … }` clauses, each over a different provider, conjoined
(the rule fires iff both hold).

- **Clause 1** — `Strings::Matches(document, "^[a-z0-9]+$").matched == true`:
  the document must be lowercase letters and digits only.
- **Clause 2** — `Strings::DigitCount(document).count == 0`: the document
  must contain no digits.

The checks are genuinely independent — the charset check rejects uppercase /
punctuation, the digit check rejects digits the charset check alone allows —
so the trace exercises each clause flipping the verdict on its own:

| tp | document | matches charset | digit count | verdict |
|----|----------|-----------------|-------------|---------|
| 0  | `abc`    | yes             | 0           | `true`  |
| 1  | `abc1`   | yes             | 1           | `false` (clause 2) |
| 2  | `ABC`    | no              | 0           | `false` (clause 1) |
