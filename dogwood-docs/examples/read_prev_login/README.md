# read_prev_login

`previous within 1h`: permit a `Read` only if the **immediately preceding**
timepoint (`i - 1`) was a matching `Login` by the same user, and that event was
within the last hour. Unlike `formerly`, `previous` looks only at the single
event directly before the decision point, not the whole window. At the first
timepoint `previous` is always false.

The trace shows both outcomes:

- `@0` — `Login` by alice (a history-only event here; no `Read` permit applies,
  so the decision is a deny).
- `@100` — alice reads doc1, immediately after the login → **allow** (the
  directly preceding event was a matching `Login` within the window).
- `@200` — alice reads doc2, but the immediately preceding event was a `Read`,
  not a `Login` → **deny** (`previous` fails even though a login exists earlier
  in history).

Referenced by `guide/04-temporal-expressions.md`.
