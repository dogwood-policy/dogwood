# 0017 — regex PII scan with a reduce method

The runnable, regex-backed analog of the reference sensitive-information guardrail
(`documentation_0402` / `0404`), which gates on a `confidenceScore`. Here the
`Pii::Scan` provider scans the document with the `regex_count` host function
for two PII shapes and returns a per-category count record
`{ ssn: Long, email: Long }`. The zero-argument output method `maxCount()`
reduces that to the worst category count — the same shape as the reference
`maxConfidenceScore()` (a method with no arguments of its own, only the
pipeline value). The policy permits only when the worst count is `< 1`, i.e.
no PII of any tracked kind.

| tp | document | ssn | email | maxCount | verdict |
|----|----------|-----|-------|----------|---------|
| 0  | `hello world`                | 0 | 0 | 0 | `true`  |
| 1  | `my ssn is 123-45-6789`      | 1 | 0 | 1 | `false` |
| 2  | `reach me at bob@example.com`| 0 | 1 | 1 | `false` |

A method genuinely earns its place here: reducing several regex counts to
their max is exactly the "worst score" pattern the reference classifier methods
express, done honestly with the host functions DL ships.
