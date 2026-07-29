# call_temporal_condition_macro_once

Calling a `def temporal` **condition** macro inside a `when temporal { … }`
block. `macros.dw` defines `once(?w, ?s)` as a thin wrapper over
`formerly within ?w ?s`; the policy calls it with a **bare interval literal**
window arg (`1h`, no `within` keyword) and a `Read` request pattern as the
predicate arg — pinning `input.user` and `input.document` to the current
request's context.

Net effect: permit a `Write` only if the same user recently `Read` the same
document (within 1h). The trace shows both outcomes:

- `@0` — `Read` of `doc1` by alice (history-only here; no `Write` permit
  applies, so the decision is a **deny**).
- `@10` — alice writes `doc1`, 10s after the read → **allow** (matching read is
  within the window and pins both `user` and `document`).
- `@20` — alice writes `doc2`, which she never read → **deny**.

Referenced by `guide/09-calling-macros.md`.
