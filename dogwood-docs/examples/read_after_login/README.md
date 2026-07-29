# read_after_login

The history-dependent version of the getting-started tour (Step 4 — the feature
that makes Dogwood more than Cedar): permit `Read` only if the **same user**
logged in within the last hour. The `when temporal { … }` clause reads the
accumulated event history, and the `{ input.user: context.input.user }` pin
correlates the past `Login`'s user with the current `Read` request's user.

The trace shows both an allow and a deny:

- `@0` — `Login` by alice. The policy gates `Read`, not `Login`, so no `permit`
  matches → **deny** (the login still lands in the history).
- `@10` — alice reads, 10s after the login → **allow** (a matching login is
  inside the 1h window).
- `@7200` — alice reads again, two hours later; the only login has expired
  (7200s > 3600s) → **deny**.

Referenced by `guide/01-getting-started.md`.
