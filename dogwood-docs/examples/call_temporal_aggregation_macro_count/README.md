# call_temporal_aggregation_macro_count

Calling a `def temporal` **aggregation** macro. `count_formerly` produces a
`count`, so it is spliced into a comparison and wrapped in an `exists` binder
that introduces the variable it is compared against — never called on its own:

```text
exists (n: Long). (count_formerly(1h, Login) == n && n > 0)
```

The macro is defined in the attached library `macros.dw` (supplied via
`--macros`) and desugars to
`count for ($t: Timepoint). where (formerly within ?w (?s && tp($t)))`. The
policy permits `Alert` once at least one matching `Login` is in the last hour.

The trace shows both verdicts:

- `@0` — alice `Login` on `s1` (a history-only event here; no `Alert` permit
  applies, so the decision is a deny).
- `@2`, `@10` — alice `Alert` on `s1`, within 1h of her login → **allow**
  (`count == 1`, so `n > 0`).
- `@20` — bob `Login` on `s1` (history-only again → deny).
- `@22` — alice `Alert` on `s1`, still within the window → **allow**.

Run from this directory:

```text
dogwood validate policy.dw --policy-schema schema.cedarschema --macros macros.dw
dogwood replay   policy.dw --policy-schema schema.cedarschema --macros macros.dw --trace trace.log
```

Referenced by `guide/09-calling-macros.md`.
