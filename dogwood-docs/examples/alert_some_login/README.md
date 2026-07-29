# alert_some_login

`exists` is the sole quantifier: it asserts **at least one** satisfying
assignment, with candidate values coming only from the atom that binds the
variable. This policy permits an `Alert` if **some** user logged in to *this
Alert's server* within the last hour. The bound `u` is range-restricted by the
`Login` predicate's `input.user` field, and `input.server: context.input.server`
pins the login's server to the server named in the current `Alert` request.

The trace shows all the interesting cases (`within 1h` = 3600s, inclusive):

- `@0` — alice logs in to `s1` (a `Login`, not an `Alert`; no permit applies) → **deny**.
- `@100` — bob alerts on `s1`; some user (alice) logged in to `s1` 100s ago → **allow**.
  Note `exists` is "at least one," and the *witness* need not be the alerting
  principal — alice's login satisfies bob's alert.
- `@200` — bob alerts on `s2`; no login to `s2` (the server pin fails) → **deny**.
- `@5000` — alice alerts on `s1`, but the only `s1` login was 5000s ago,
  outside the 1h window → **deny**.

Referenced by `guide/04-temporal-expressions`.
