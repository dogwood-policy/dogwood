# macro_library_once_is_small

Demonstrates the shareable **macro library**: the policy calls `once` (a
`def temporal` macro) and `is_small` (a `def cedar` macro) that are defined in
an external `macros.dw` and supplied via `--macros`. The `policy.dw` does **not**
redeclare either macro — they are merged in from the library at lowering time.

`permit SellShares` only when the sale amount `is_small(context.input.shares)`
(the Cedar macro, `< 100`) **and** the same stock had an `ApproveSale`
`once` within the last hour (the temporal macro, `formerly within 1h`, pinned to
`context.input.stock`).

Run it (from this directory):

```
dogwood validate policy.dw --policy-schema schema.cedarschema --macros macros.dw
dogwood replay   policy.dw --policy-schema schema.cedarschema --macros macros.dw --trace trace.log
```

The trace shows every case:

- `@0` — `ApproveSale` for AMZN by alice (history-only; no `SellShares` permit
  applies, so the decision is a deny).
- `@100` — alice sells 5 AMZN, 100s after the approval → **allow** (`is_small(5)`
  holds and a matching approval is within the window).
- `@200` — alice sells 500 AMZN → **deny** (`is_small(500)` is false: the Cedar
  macro's `< 100` threshold fails).
- `@5000` — bob sells MSFT with no prior approval → **deny** (`once` finds no
  matching `ApproveSale` in the window).

This is the only chapter example that needs `--macros`.

Referenced by `guide/06-macros.md`.
