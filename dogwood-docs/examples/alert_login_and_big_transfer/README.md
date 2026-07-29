# alert_login_and_big_transfer

Nested `exists` with a value-threshold filter: permit an `Alert` when the
**same user** both logged in AND made a transfer over 100 within the last hour.

The outer `exists (u: String)` binds the user; the inner `exists (a: Long)`
is scoped by that same `u` and combines a predicate-field restrictor
(`input.amount: a`) with a comparison filter (`a > 100`). Pinning the inner
transfer to the outer user's `u` prevents another user's large transfer from
satisfying the threshold.

Referenced by `guide/04-temporal-expressions.md`.
