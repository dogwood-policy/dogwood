# sell_after_approval_valid_ticker

Two Dogwood clause forms combined on a single rule:

- a `when temporal { … }` **marker** — a matching `ApproveSale` for the *same
  stock* must precede this `SellShares` within the last hour (`formerly within
  1h`, with the stock pinned via `input.stock: context.input.stock`); and
- a `when guardrails { … }` **provider** check — the ticker must match an
  uppercase regex, decided by the `Strings::Matches` information provider. The
  `guardrails` tag is transparent sugar for a bare `when`; `Strings::Matches`
  is a plain provider call recognized and hoisted at lowering.

Both clauses must hold for the rule to permit.

## Files

- `policy.dw` — the combined-clause permit rule.
- `schema.cedarschema` — the reusable Drupe action schema (has `SellShares`
  and `ApproveSale`), lifted from the `write_after_read` example.
- `providers.json` — declares `Strings::Matches`. The Rhai body is **inlined**
  in the `script` field (rather than referenced via `scriptFile`) because the
  `dogwood` CLI reads `--providers` as text with `ProviderDeclarations::from_json`,
  which does not resolve external `scriptFile` references at replay time.
- `matches.rhai` — the same provider body kept as a readable standalone source
  (lifted from `provider_only/corpus/0001_regex_matches_uppercase`).
- `trace.log` — five events; see verdicts below.
- `expected.out` — captured from the real `dogwood replay` run.

## Verdicts (from `dogwood replay`)

- `@0` — alice `ApproveSale` AMZN → **DENY** (history-only; no `SellShares`
  permit applies).
- `@100` — alice `SellShares` AMZN → **ALLOW**: temporal passes (AMZN approval
  at `@0` is within 1h) *and* guardrails passes (`AMZN` matches `^[A-Z]+$`).
- `@200` — bob `ApproveSale` goog → **DENY** (history-only).
- `@300` — bob `SellShares` goog → **DENY**: temporal passes (goog approval at
  `@200`) but guardrails **fails** — `goog` is lowercase. Isolates the
  guardrails clause.
- `@5000` — carol `SellShares` MSFT → **DENY**: guardrails passes (`MSFT` is
  uppercase) but temporal **fails** — no prior approval. Isolates the temporal
  clause.

## Reproduce

Run from this directory (so relative provider paths resolve):

```
dogwood validate policy.dw --policy-schema schema.cedarschema --providers providers.json
dogwood replay   policy.dw --policy-schema schema.cedarschema --providers providers.json --trace trace.log
```

Referenced by `guide/02-policy-language.md` — The Policy Language.
