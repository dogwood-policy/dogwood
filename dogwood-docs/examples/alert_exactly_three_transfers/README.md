# alert_exactly_three_transfers

Counting over a `*`-wildcard field: permit an `Alert` only if **exactly three**
`Transfer`s — regardless of amount — occurred within the last hour. The
`input.amount: *` wildcard matches any transfer and binds nothing; `tp(t)`
keeps the rows one-per-timepoint so `count` tallies distinct past timepoints.

The trace demonstrates both verdicts, including the window boundary:

- `@200` — only two Transfers so far (w1@0, w2@100) → **deny** (count = 2).
- `@400` — three Transfers in window (w1, w2, w3@300) → **allow** (count = 3).
- `@600` — a fourth Transfer (w4@500) pushes the count to 4 → **deny**.
- `@3700` — one hour later, w1@0 has aged out of the 1h window but w2@100,
  w3@300, and w4@500 remain → count back to 3 → **allow** (the
  window-boundary demo).

Referenced by `guide/04-temporal-expressions.md`.
