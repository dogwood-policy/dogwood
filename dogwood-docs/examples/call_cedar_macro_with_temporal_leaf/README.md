# call_cedar_macro_with_temporal_leaf

A Cedar macro conjoined mid-expression with a `temporal { … }` leaf. Because a
`def cedar` macro (`level_ok(?n) { ?n >= 2 }`, in `macros.dw`) expands *before*
the surrounding expression is lowered, `level_ok(context.input.level)` can be
`&&`-joined with a `temporal { … }` block in one `when`. The guide leaves the
temporal body as `/* … */`; here it is promoted to a recent-`Login` check
(`formerly within 1h`, pinned to the same `input.server`).

The trace shows both outcomes:

- `@0` — `Login` by alice on `s1` (history only; no `Alert` permit applies) → **DENY**.
- `@2` — `Alert` by alice, `level: 1` → `level_ok(1)` is false → **DENY**.
- `@10` — `Alert` by alice, `level: 2` → `level_ok(2)` true *and* a `Login` on `s1`
  is within the last hour → **ALLOW**.
- `@20` — `Login` by bob (history only) → **DENY**.
- `@22` — `Alert` by alice, `level: 3` → `level_ok` true *and* a matching recent
  `Login` on `s1` → **ALLOW**.

Run from this directory:

```text
dogwood validate policy.dw --policy-schema schema.cedarschema --macros macros.dw
dogwood replay  policy.dw --policy-schema schema.cedarschema --macros macros.dw --trace trace.log
```

Referenced by `guide/09-calling-macros.md`.
