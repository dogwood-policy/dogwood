# 0019 — `when guardrails` plus a Cedar `unless` exception

The runnable, regex-backed analog of the reference
`documentation_0407_guardrails_with_unless_cedar`: a positive guardrail
precondition combined with a plain Cedar `unless` carve-out on one
non-temporal rule. The clauses are conjoined — the rule fires iff the
guardrail holds AND the `unless` condition does not.

- **Guardrail (`when`)** — `Strings::Matches(document, "^[A-Za-z]+$").matched
  == true`: the document must be an all-letters name.
- **Exception (`unless`)** — `context.input.document == "BLOCKED"`: the
  literal sentinel `BLOCKED` is denied even though it satisfies the regex.

| tp | document  | matches regex | is "BLOCKED" | verdict |
|----|-----------|---------------|--------------|---------|
| 0  | `hello`   | yes           | no           | `true`  |
| 1  | `BLOCKED` | yes           | yes          | `false` (unless) |
| 2  | `bad1`    | no            | no           | `false` (guardrail) |

tp1 is the interesting one: it passes the regex guardrail but is vetoed by
the Cedar `unless`, proving the two clause kinds compose on one rule.
