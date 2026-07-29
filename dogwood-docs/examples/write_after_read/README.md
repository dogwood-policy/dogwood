# write_after_read

The canonical history-dependent policy: permit `SellShares` only if the **same
user** had an `ApproveSale` for the **same stock** within the last hour
(`formerly within 1h`, with the stock pinned via `input.stock:
context.input.stock`).

The trace shows all three cases:

- `@0` — `ApproveSale` for AMZN by alice (a history-only event here; no
  `SellShares` permit applies, so the decision is a deny).
- `@100` — alice sells AMZN, 100s after the approval → **allow** (a matching
  approval is within the window).
- `@5000` — bob sells MSFT with no prior approval → **deny**.

Referenced by `guide/04-temporal-expressions.md`.
