# provider_regex_analyze_fields

Several calls to the **same** `Regex::Analyze` provider, each projecting a
different output field and comparing it, combined with `&&` as plain Cedar
(the *unwrapped* provider form — no `guardrails { … }` block). Permit `Read`
only when the document:

1. starts with an uppercase letter — `^[A-Z]` → `.is_match == true`
2. has at least three digit characters — `[0-9]` → `.count >= 3`
3. whose first run of digits is exactly `42` — `[0-9]+` → `.first_match == "42"`

`Regex::Analyze(string, string) -> { is_match: bool, first_match: string,
count: integer }` is declared in `providers.json`. Its Rhai script is
**inlined** into `providers.json` (as the `"script"` field) rather than
referenced via `scriptFile`, because the `dogwood` CLI parses the
declarations text directly and does not resolve external `scriptFile`
references.

## Trace

Each denial isolates one failing condition:

| doc | starts A–Z | ≥3 digits | first run == "42" | verdict |
|-----|-----------|-----------|-------------------|---------|
| `Abc42x999` | yes | yes (5) | yes | **ALLOW** |
| `abc42x999` | no  | yes | yes | DENY |
| `A42`       | yes | no (2) | yes | DENY |
| `A99942`    | yes | yes | no (`99942`) | DENY |

Run from this directory so the schema/providers paths resolve:

```
dogwood validate policy.dw --policy-schema schema.cedarschema --providers providers.json
dogwood replay   policy.dw --policy-schema schema.cedarschema --providers providers.json --trace trace.log
```

Lifted from corpus case `0005_regex_operations`.

Referenced by `guide/05-information-providers.md`.
