# max_window_raised

Raising the temporal look-back cap. The event schema's default cap on any
`within` window is **24h**; a `max_window = <interval>` directive at the top of
the event schema changes it. Here the cap is raised to `30d`, which is what
lets the policy's `formerly within 7d` validate — under the default 24h cap a
7-day window is a `max_window` validation error.

The event schema is passed with `--event-schema event.dwschema`; the
`max_window = 30d` line must precede the event declarations.

```
dogwood validate policy.dw \
  --policy-schema schema.cedarschema \
  --event-schema event.dwschema
```

See [The event schema § Capping the look-back
window](../../guide/03-event-schema.md#capping-the-look-back-window-max_window)
and [Temporal expressions § Intervals and time
units](../../guide/04-temporal-expressions.md#intervals-and-time-units).
