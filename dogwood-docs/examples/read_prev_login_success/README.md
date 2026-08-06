# read_prev_login_success

`previous` with a **response predicate** and an **output-field filter**.
Permit a `Read` only if the *immediately preceding* event (within 1h) was the
same user's **successful** `Login` — i.e. a `Login::response` whose
`output.result` is `true`. Because `previous` looks only at timepoint `i - 1`,
at timepoint 0 there is no predecessor, so the rule can never fire there.

The trace shows all three behaviors:

- `@0` — a `Read` at **timepoint 0**: no predecessor exists, so **deny** (the
  no-verdict-at-tp0 behavior).
- `@7` — a `Read` whose immediately preceding event (`@5`) is alice's
  successful `Login::response` (`output.result: true`) → **allow**.
- `@31` — a `Read` whose predecessor (`@30`) is bob's `Login::response` with
  `output.result: false`; the output-field filter rejects the failed login →
  **deny**.

Referenced by `guide/04-temporal-expressions.md`.
