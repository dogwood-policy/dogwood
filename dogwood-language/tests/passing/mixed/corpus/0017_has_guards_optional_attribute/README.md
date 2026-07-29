# 0017 — `has` guards an optional entity attribute

The idiomatic safe-read pattern for an **optional** entity attribute
(`clearance?: String`): guard the read with `has` so an absent attribute is a
plain `false`, not an evaluation error.

```
principal has clearance && principal.clearance == "high"
```

`principal has clearance` short-circuits the `&&`: when `clearance` is absent
the read is never reached, so the clause is false with no error. (A bare
`principal.clearance == "high"` would instead error on the absent attribute.)
`clearance` is supplied per event via the `.log` `entities(...)` envelope.

Three timepoints covering the interesting states of an optional attribute:

- `@0` alice, `clearance: "high"` -> present and matches -> **Allow**.
- `@10` bob, `clearance: "low"` -> present but not "high" -> **Deny**.
- `@20` carol, `clearance` omitted -> `has` is false, `&&` short-circuits ->
  **Deny** (no error; omitting an optional attribute also conforms).

The verdict stream cannot distinguish "false" from "errored-and-skipped" — the
no-error property is pinned precisely by the unit tests in
`tests/entity_store.rs` (`has_*`); this case is the portable end-to-end
companion.
