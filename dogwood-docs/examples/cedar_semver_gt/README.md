# cedar_semver_gt

The RFC 0061 `semver` worked example for Cedar macros: a record-building macro
(`semver`, which constructs a `{ major, minor, patch }` record) passed as an
argument to a comparator macro (`semverGT`). Nesting one macro *call* as an
argument to another is allowed — the compiler expands call arguments first,
then splices the result into the outer macro's body.

Both macros are declared inline in `policy.dw`. The rule uses constant
arguments and a bare `action` scope, so it validates against the Drupe
schema (copied from `write_after_read`) with no event history.

Referenced by `guide/06-macros.md`.
