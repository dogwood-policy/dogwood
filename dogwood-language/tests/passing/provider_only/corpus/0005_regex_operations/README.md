# 0005 — All regex operations in one provider (unwrapped)

Exercises every regex host function a provider script can call, surfaced
as fields of a single `Regex::Analyze(text, pattern)` provider:

| host function | output field | type |
|---|---|---|
| `regex_is_match(pattern, text)` | `is_match` | Bool |
| `regex_find(pattern, text)` | `first_match` | String |
| `regex_count(pattern, text)` | `count` | Long |

The policy is written in the **unwrapped** form (no `guardrails { … }`
block): three `Regex::Analyze` calls sit directly in an ordinary Cedar
`when { … }`, each projecting a different output field and combined with
`&&`. Permit `Read` only when the document:

1. starts with an uppercase letter — `^[A-Z]` → `.is_match == true`
2. has at least three digits — `[0-9]` → `.count >= 3`
3. whose first digit run is exactly `42` — `[0-9]+` → `.first_match == "42"`

Verdicts (each denial isolates one failing condition):

| doc | starts A–Z | ≥3 digits | first run == "42" | verdict |
|-----|-----------|-----------|-------------------|---------|
| `Abc42x999` | ✓ | ✓ (5) | ✓ | **Allow** |
| `abc42x999` | ✗ | ✓ | ✓ | deny |
| `A42`       | ✓ | ✗ (2) | ✓ | deny |
| `A99942`    | ✓ | ✓ | ✗ (`99942`) | deny |
