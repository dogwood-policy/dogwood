# alert_heartbeat_and_login_rate

A top-level `&&` chain combining a `formerly` with an `exists`-guarded `count`
(the login-rate threshold). Permit an `Alert` only if a `Heartbeat` for this
server fired within the last hour **and** more than two `Login`s to this server
occurred.

```text
when temporal {
    formerly within 1h Drupe::Action::"Heartbeat"::request{ input.server: context.input.server }
    && exists (n: Long). (
        (count for (t: Timepoint). where (
            Drupe::Action::"Login"::request{ input.user: _, input.server: context.input.server } && tp(t)
        )) == n && n > 2
    )
};
```

Schema is lifted from the `temporal_only` corpus case `0059_count_threshold`
(it declares `Heartbeat`/`Login`/`Alert` with a `server` input); the trace is
lifted from that case's `trace_1.log`. The default event schema
(request/response) is used.

## What the trace shows

The trace fires a `Heartbeat` for `s1`, three `Login`s (alice, bob, carol) to
`s1`, and two `Alert`s. Every timepoint replays to **DENY**:

- The `formerly ... Heartbeat` conjunct **is** satisfied at the two `Alert`
  timepoints (a heartbeat fired within the window), so on its own it would
  allow.
- But the `count` conjunct is **never** satisfied. Its body `Login && tp(t)`
  is not wrapped in a past-temporal operator, so `tp(t)` pins the count to the
  *current* timepoint (the `Alert`), where no `Login` fires. The count is
  therefore `0` at every `Alert`, so `n > 2` is false.
- Because the two conjuncts are joined by `&&`, the rule denies everywhere.

This is the intended semantics of the guide fragment as written: a bare
`count ... where (P && tp(t))` counts occurrences *at the verdict timepoint*,
not across history. To count historical logins you would wrap the body in a
`formerly within 1h (...)` (compare corpus `0179_agg_with_once_counts_history`).

Referenced by `guide/04-temporal-expressions.md`.
