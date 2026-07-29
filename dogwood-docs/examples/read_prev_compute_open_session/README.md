# read_prev_compute_open_session

A top-level `previous && (open-session since)` chain: permit a `Read` only if the
**same user** computed at the **immediately preceding** timepoint (`previous
within 1h ... Compute`, user pinned via `input.user: context.input.user`) **AND**
that user has an **open session** — no `Logout` since their `Login` within 24h
(`!Logout since within 24h Login`).

The since-clause is parenthesized so that `&&` (the loosest-binding operator)
groups the two conjuncts, rather than the `since` swallowing the `previous`
conjunct. This demonstrates combining `previous` with a negated-left `since` in
one top-level temporal chain.

Referenced by `guide/04-temporal-expressions.md`.
