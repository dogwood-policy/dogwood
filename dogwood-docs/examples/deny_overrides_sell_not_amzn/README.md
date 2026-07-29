# deny_overrides_sell_not_amzn

A `permit` + `forbid` pair showing **deny-overrides** semantics: `SellShares` is
permitted in general, but a `forbid` carves out AMZN. Because `forbid` always
wins, source order does not matter — the forbid "carves a hole" out of whatever
the permit allows.

The trace shows both outcomes:

- `@0` — alice sells MSFT → **allow** (the permit matches; no forbid applies).
- `@100` — alice sells AMZN → **deny** (the forbid matches and overrides the
  permit).
- `@200` — bob calls `GetStockInfo` → **deny** (no permit matches, so the
  default-deny applies).

Referenced by `guide/02-policy-language.md` — The Policy Language.
