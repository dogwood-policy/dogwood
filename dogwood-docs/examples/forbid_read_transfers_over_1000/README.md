# forbid_read_transfers_over_1000

A `forbid` rule with a `sum` over a `(value, timepoint)` domain and a filtered
temporal body. Forbid a `Read` if the **same user's** resolved **positive**
`Transfer`s in the last hour total **more than 1000**.

The two-binder domain `for (a: Long), (t: Timepoint).` is what keeps equal
amounts made at different timepoints from being deduplicated — `a` is the summed
value and `t` distinguishes the timepoints, so the sum is per-occurrence.

Because the policy set contains only this `forbid` rule, no request can ever be
allowed — the interesting contrast is the threshold, i.e. whether the `forbid`
fires (an explicit deny, shown as `[rules: 0]`) or not (a default deny).

The trace shows both sides of the threshold:

- `@0`/`@1` — alice's first `Transfer` resolves to 600 (a history-only event; no
  matching rule applies, so the decision is a default deny).
- `@10` — alice reads with only 600 transferred in the last hour → **default
  deny** (the `forbid` does not fire; 600 is not over 1000).
- `@20`/`@21` — a second `Transfer` for alice resolves to 600 (running total
  1200).
- `@30` — alice reads again, now with 600 + 600 = 1200 transferred in the last
  hour → **explicit deny** (`[rules: 0]`, the `forbid` fires because the sum is
  over 1000).
- `@40` — bob reads with no `Transfer`s of his own → **default deny** (the
  per-user pin `input.user: context.input.user` means alice's transfers do not
  count for bob).

Referenced by `guide/04-temporal-expressions.md`.
