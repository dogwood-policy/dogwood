# temporal_count_formerly_login

An aggregation-flavoured temporal **macro**. `count_formerly(?w, ?s)` counts the
timepoints within a window `?w` at which predicate `?s` held. It desugars to

```
count for ($t: Timepoint). where (formerly within ?w (?s && tp($t)))
```

where `$t` is a fresh binder the macro introduces itself — hygienically renamed
per call site, so the macro is safe to reuse across policies. The macro is
spliced into a comparison inside `exists`, never called on its own: the
`login_count_positive` rule permits an `Alert` only when the same user has had
at least one `Login` on the same server within the last hour (`count == n` and
`n > 0`).

The trace shows both outcomes:

- `@0` — alice logs in on `s1` (a history-only event; no `Alert` permit
  applies, so the decision is a **deny**).
- `@100` — alice raises an `Alert` on `s1`, 100s after her login → **allow**
  (a matching login is within the 1h window and the count is positive).
- `@200` — bob raises an `Alert` on `s2` with no prior login → **deny**.

Referenced by `guide/06-macros.md`.
