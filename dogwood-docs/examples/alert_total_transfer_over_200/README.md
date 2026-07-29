# alert_total_transfer_over_200

Aggregation example: permit an `Alert` only when the total transferred amount
exceeds a threshold. `sum a for (a: Long). where …Transfer::request{ input.amount: a }`
sums the `amount` column over the deduplicated matching rows, binds it to
`total` via `== total`, and the permit fires only if `total > 200`.

The `sum` body is a **bare predicate** — it has no `formerly`/temporal wrapper,
so it scans only the *current* timepoint. Because the permit's scope requires
the current action to be `Alert` (never a `Transfer`), the summed relation at
every Alert decision point is empty, so `total` is 0 and `total > 200` is never
satisfied. Every verdict in the trace is therefore a **deny** — matching the
all-`false` oracle for corpus `0063_sum_threshold`. (To make this fire you would
wrap the body in a temporal operator so the sum ranges over past transfers, as
in the `0299_sum_resolved_filter` / `0301_sum_resolved_range_filter` variants.)

Files:

- `policy.dw` — the permit with the `sum … > 200` temporal body.
- `schema.cedarschema` — Drupe action schema (lifted from corpus
  `temporal_only/0063_sum_threshold`; has `Transfer` with a `Long amount` input
  and `Alert`).
- `trace.log` — lifted from `0063_sum_threshold/trace_1.log`: transfers of 100,
  200, and 50 by three users interleaved with three Alerts.
- `expected.out` — the real per-timepoint verdict stream from `dogwood replay`.

Reproduce (run from this directory):

```
dogwood validate policy.dw --policy-schema schema.cedarschema
dogwood replay   policy.dw --policy-schema schema.cedarschema --trace trace.log
```

Referenced by `guide/04-temporal-expressions.md`.
