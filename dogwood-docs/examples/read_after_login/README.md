# read_after_login

The history-dependent version of the getting-started tour (Step 4 — a decision that
depends on history, which a single Cedar request cannot see): permit `Read` only if the **same user**
successfully logged in within the last hour. The `when temporal { … }` clause
reads the accumulated event history, and the `{ input.user: context.input.user }`
pin correlates the past `Login` response's user with the current `Read` request's
user.

The trace shows both an allow and a deny:

- `@0` — `Login` request by alice. The policy gates `Read`, not `Login`, so no
  `permit` matches → **deny** (the login request still lands in the history).
- `@5` — `Login` response (history-only; records that the login succeeded).
- `@10` — alice reads, 10s after the login → **allow** (a matching login
  response is inside the 1h window).
- `@7200` — alice reads again, two hours later; the only login has expired
  (7200s > 3600s) → **deny**.

Referenced by `guide/01-getting-started.md`.
