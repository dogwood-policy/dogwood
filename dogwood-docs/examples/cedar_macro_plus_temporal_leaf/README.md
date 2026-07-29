# cedar_macro_plus_temporal_leaf

A `def cedar` boolean macro (`level_ok`) conjoined **mid-expression** with an
inline `temporal { … }` leaf. The Cedar macro is expanded *before* the
surrounding expression is lowered (which hoists the temporal leaf). The guide
shows a `temporal { /* ... */ }` placeholder; here it is promoted to a concrete
recent-login leaf: `formerly within 1h ...Login...`, pinned to the same server
via `input.server: context.input.server`.

The policy permits `Alert` only when **both** conjuncts hold:

- `level_ok(context.input.level)` — the Cedar macro requires `level >= 2`.
- the temporal leaf — a `Login` for the same server occurred within the last hour.

The trace exercises every combination:

- `@0` — a `Login` (not an `Alert`; no permit rule applies) → **DENY**.
- `@10` — `Alert` level 3 on `s1`, with a recent login on `s1` → **ALLOW**
  (both conjuncts true).
- `@20` — `Alert` level 1 on `s1` → **DENY** (macro conjunct false: `1 < 2`).
- `@30` — `Alert` level 5 on `s2`, no login on `s2` → **DENY** (temporal
  conjunct false: server mismatch).

Referenced by `guide/06-macros.md`.
