# call_temporal_condition_macros_composed

Two `def temporal` **condition** macros composed with `&&` inside a single
`when temporal { … }` block. `recently_logged_in(?u)` and
`recently_read(?u, ?d)` each name a "happened within the last hour" check
(`formerly within 1h`); the policy permits a `Write` only when **both** hold —
the same user logged in *and* read the same document being written. Condition
macros compose with `&&` exactly like the built-in temporal operators.

The macros live in `macros.dw` and are supplied with `--macros`.

The trace walks alice through login (`@0`) then read of `doc1` (`@10`), so:

- `@20` — alice writes `doc1`: both macros hold → **allow**.
- `@30` — alice writes `doc2`: she logged in but never read `doc2`
  (`recently_read` fails) → **deny**.
- `@40` — bob writes `doc1`: he never logged in or read → **deny**.

Referenced by `guide/09-calling-macros.md`.
