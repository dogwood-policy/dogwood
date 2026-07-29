# alert_login_in_last_hour

Counting over **history**: a `formerly within 1h` body *inside* the aggregation
makes the `count` range over the whole window, not just the current timepoint.
Permit an `Alert` if at least one `Login` to **this server**
(`input.server: context.input.server`) occurred in the last hour. The
`exists (n: Long). ((count …) == n && n > 0)` idiom just asserts the historical
count is positive.

The trace shows both a fire and a non-fire:

- `@0` — `Login` to `s1` by alice (a history-only event here; no `Alert` permit
  applies, so the decision is a deny).
- `@100` — alice raises an `Alert` for server `s1`, with a matching `Login` to
  `s1` within the window → **allow**.
- `@200` — alice raises an `Alert` for server `s2`, with no `Login` to `s2` →
  **deny**.

Referenced by `guide/04-temporal-expressions.md`.
