# temporal_sum_formerly_transfer

A `temporal sum` aggregation macro defined inline. `sum_formerly` combines a
**binder-position parameter** `?a` (the sum's bound variable, passed by the
caller as the bare identifier `a`) with a macro-introduced **hygienic** binder
`$t`. It desugars to:

```text
sum ?a for (?a: Long), ($t: Timepoint). where (formerly within ?w (?body && tp($t)))
```

The policy sums every `Transfer`'s `input.amount` seen within the last hour and
permits `Alert` only when that running total exceeds 100, comparing the
aggregate inside an `exists (total: Long)` binder.

The trace shows both outcomes:

- `@0` — `Transfer` of 40 by alice (history-only; running sum = 40).
- `@2` — `Alert`: cumulative Transfer sum within 1h is 40, not `> 100` → **DENY**.
- `@4` — `Transfer` of 80 by bob (running sum = 40 + 80 = 120).
- `@6` — `Alert`: cumulative Transfer sum is 120, which is `> 100` → **ALLOW**.

Note: the guide uses `total > 100`; the corpus source policy
(`tests/passing/macros/corpus/0010_sum_formerly_exact`) uses `total == 100`.
This example follows the guide (`> 100`), so `expected.out` was captured from a
fresh `dogwood replay` of this policy.

Referenced by `guide/06-macros.md`.
