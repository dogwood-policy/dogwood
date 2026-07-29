# alert_login_current_tp

The canonical `tp(t)` count-over-timepoints idiom with **no temporal wrapper**
on the aggregation body. The `count for (t: Timepoint)` ranges over distinct
timepoints, and because there is no `formerly`/`since`/`previous` wrapper on the
`Login::request` predicate, the count sees **only same-timepoint events**. The
policy permits an `Alert` iff at least one `Login` to this same server
(`input.server: context.input.server`) occurred at the current timepoint.

No trace is authored for this example (`validate`-only).

Referenced by `guide/04-temporal-expressions.md`.
