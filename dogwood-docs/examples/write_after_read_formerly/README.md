# write_after_read_formerly

The flagship history-dependent policy in the guide's literal wording: permit a
`Write` only if the **same user** successfully read the **same document** within
the last hour. `formerly within 1h` is the existential past operator; the field
pins `input.user: context.input.user` and `input.document: context.input.document`
correlate the past `Read` response to the *current* request.

This bundle preserves the guide's literal `Read`/`Write` text. (The sibling
bundle `examples/write_after_read` adapts the same concept to the designated
`SellShares`/`ApproveSale` schema.) The schema here is lifted from temporal
corpus case `0004_write_after_read`, which carries the `Read`/`Write` actions.

The trace shows both outcomes:

- `@0` — alice reads doc1 (a decision event; a `Read` is not a `Write`
  permit, so the decision is a deny).
- `@5` — the read completes successfully (a history-only `response` event;
  no verdict is produced, but it records the success for later lookups).
- `@10` — alice writes doc1, 10s after her read -> **allow** (matching read
  response in the window).
- `@20` — alice writes doc2, which she never read -> **deny** (the
  `input.document` pin fails).
- `@30` — bob writes doc1, which he never read -> **deny** (the `input.user`
  pin fails).
- `@3700` — alice writes doc1 again, but 3700s > 1h after her read -> **deny**
  (the window has expired).

Referenced by `guide/04-temporal-expressions.md`.
