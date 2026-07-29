# temporal_once_read_recent

A condition-flavoured temporal macro. `def temporal once(?w, ?s) { formerly
within ?w ?s }` wraps a window `?w` and a **whole condition** `?s` in `formerly
within`, so it is callable wherever a temporal condition is expected. The
policy permits when the same user recently (within `1h`) issued a `Read` for the
same document, pinning both fields via `input.user: context.input.user` and
`input.document: context.input.document`.

The macro is defined **inline** in `policy.dw` (no separate `macros.dw`), and
the schema (`schema.cedarschema`, which carries a `Read` action) is copied from
`tests/passing/macros/corpus/0020_condition_macro_bare`.

The trace shows both outcomes:

- `@0` — alice `Read`s `doc1`; the `once(...)` condition matches at the current
  timepoint → **allow**.
- `@100` — alice `Write`s `doc1`, 100s after her read → **allow** (a matching
  read for the same user + document is within the window).
- `@200` — bob `Write`s `doc2` with no prior read → **deny**.

Referenced by `guide/06-macros.md`.
