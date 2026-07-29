# provider_regex_matches_uppercase

The canonical worked information-provider example: permit `Read` only when the
requested `document` is all-uppercase letters (matches `^[A-Z]+$`), as decided
by the `Strings::Matches` information provider (a regex matcher implemented in
`matches.rhai`). The provider call sits in an ordinary `when { ... }`; the
projection (`.matched`) and comparison (`== true`) are plain Cedar.

Files:

- `policy.dw` — the policy.
- `schema.cedarschema` — the base Cedar schema (minimal Drupe `Read` action).
- `providers.json` — declares `Strings::Matches(string, string) -> { matched: Bool }`.
- `matches.rhai` — the provider implementation (`fn evaluate(text, pattern)`).
- `trace.log` — three `Read` requests: `ABC`, `abc`, `AB12`.
- `expected.out` — the replay verdict stream.

The trace shows:

- `@0` — `Read` of `"ABC"` (all uppercase) → **ALLOW**.
- `@10` — `Read` of `"abc"` (lowercase) → **DENY**.
- `@20` — `Read` of `"AB12"` (digits) → **DENY**.

## Running it

```
dogwood validate policy.dw --policy-schema schema.cedarschema --providers providers.json
dogwood replay   policy.dw --policy-schema schema.cedarschema --providers providers.json --trace trace.log
```

Note on `providers.json`: the CLI's `--providers` flag parses the declarations
with `from_json`, which does **not** resolve a `scriptFile` reference. So for
the CLI path the Rhai body is inlined under `implementation.script`; the
equivalent `matches.rhai` file is kept alongside for reference (and validation
works either way).

Referenced by `guide/05-information-providers.md`.
