# mc_0025 sum of unresolved (in-flight) transfer amounts

The `sum` companion to `mc_0022_count_unresolved_transfer`. A macro,
`sum_unresolved_transfer_amount_within(?w)`, sums the `input.amount` of
every Transfer request in the last `?w` that has **no matching
response** — the total value of still-pending, in-flight transfers.

## The "requested but not yet resolved" idiom

A request and its response share a `requestId`. "In-flight" means a
`Transfer::request` whose uid has *not* (yet) appeared on a
`Transfer::response`:

```
formerly within ?w Transfer::request{ requestId: $q, input.amount: a }
  && !exists ($r: Timepoint).
        formerly within ?w (Transfer::response{ requestId: $q } && tp($r))
```

The left conjunct enumerates each request, binding the per-occurrence
uid `$q` and the summed value `a` (from `input.amount`). The negated
inner `exists` drops any request whose uid already has an in-window
response. `tp($r)` range-restricts the inner existential (the §7-safe
negated-exists shape). The `sum a for (a: Long), ($q: String). where …`
then adds up `a` across the surviving (pending) requests.

The policy permits the `Alert` when the pending total reaches `50`.

## Trace and verdicts

Three transfers are requested — `u1: 10`, `u2: 20`, `u3: 30` — and
`u1` resolves at `@1`, `u2` resolves at `@6`, `u3` never resolves.

- **`@5` Alert (tp 4):** pending = `u2 (20)` + `u3 (30)` = **50** ≥ 50
  → **true**. (`u1` already resolved; `u2` has not resolved yet.)
- **`@8` Alert (tp 6):** `u2` resolved at `@6`, so pending = `u3 (30)`
  only = **30** < 50 → **false**.

The `Transfer::request` timepoints (`@0`/`@2`/`@3`) are decision events
but the `Alert`-scoped policy never applies to them, so each is `false`;
the `response` events (`@1`/`@6`) are history-only and produce no
verdict. This is the exact same verdict stream as `mc_0022`'s count
version (count ≥ 2 ⇔ pending total 50 here), by construction.
