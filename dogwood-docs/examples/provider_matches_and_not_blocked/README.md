# provider_matches_and_not_blocked

Two information providers combined with the boolean spine (`&&` and `!`) inside
one ordinary `when { ... }` clause: permit `Read` only when the document
**matches** an allowed-name pattern (`Strings::Matches` against `^[a-z]+$`)
**and is not** on the blocklist (`!(Lists::Blocked(...).blocked == true)`).

A `when { ... }` body is a boolean expression over multiple provider atoms, not
just one; each provider is a plain namespaced call recognized and hoisted at
lowering.

## Files

- `policy.dw` — the permit rule combining both providers with `&&` and `!`.
- `schema.cedarschema` — the minimal Drupe action schema (has `Read` with
  `ReadInput = { document: String }`), lifted from
  `provider_only/corpus/0004_two_providers_and_not`.
- `providers.json` — declares `Strings::Matches` and `Lists::Blocked`. Each
  Rhai body is **inlined** in the `script` field (rather than referenced via
  `scriptFile`) because the `dogwood` CLI reads `--providers` as text with
  `ProviderDeclarations::from_json`, which does not resolve external
  `scriptFile` references at replay time.
- `matches.rhai` — the `Strings::Matches` body kept as a readable standalone
  source (lifted from the corpus).
- `blocked.rhai` — the `Lists::Blocked` body kept as a readable standalone
  source (a tiny hard-coded denylist: `"evil"`, `"badword"`).
- `trace.log` — three `Read` events; see verdicts below.
- `expected.out` — captured from the real `dogwood replay` run.

## Verdicts (from `dogwood replay`)

- `@0` — `document: "hello"` → **ALLOW**: matches `^[a-z]+$` and is not on the
  blocklist.
- `@10` — `document: "evil"` → **DENY**: matches the pattern but is blocked; the
  `!` rejects it.
- `@20` — `document: "Hello"` → **DENY**: the uppercase `H` fails the
  lowercase-only pattern.

## Reproduce

Run from this directory (so relative provider paths resolve):

```
dogwood validate policy.dw --policy-schema schema.cedarschema --providers providers.json
dogwood replay   policy.dw --policy-schema schema.cedarschema --providers providers.json --trace trace.log
```

Referenced by `guide/05-information-providers.md`.
