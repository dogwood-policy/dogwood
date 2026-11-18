# dogwood-ops

Host-neutral Dogwood operations with owned, serializable results: the shared
core of the `dogwood` CLI and the language bindings (`@aws/dogwood-wasm`, the
Python `dogwood` package).

Every function takes `&str` sources and returns an owned report that
implements `serde::Serialize`, or an [`OpError`] that is both a
`miette::Diagnostic` (for rendering) and `Serialize` (for a stable JSON
shape). A host only converts these to its own values: the CLI renders them or
prints them as JSON, a binding turns them into native objects and raised
errors. The frontend's handle types never cross that boundary.

| Item | What it is |
|---|---|
| [`ops`] | One function per CLI command — `check_parse`, `validate_policies`, `lower_to_cedar`, `replay_trace`, `explain_policies`, the schema checks — and their report types |
| [`error`] | [`OpError`] and [`Diagnostic`], the projection of the frontend's diagnostics |
| [`live`] | [`LiveAuthorizer`]: lower once, then authorize events one at a time, rejecting events the schema cannot decide |
| [`bounds`] | Limits a binding enforces on untrusted host values before any recursive code sees them |
| [`fail_closed`], [`providers`] | Safety rules the bindings apply on top of the CLI's behaviour |

The crate-root [`replay`], [`check_providers`] and `mcp_to_cedar_schema`
(feature `mcp-schema`) are those operations with the bindings' safety rules
applied. The CLI calls the [`ops`] functions directly.

The JSON shapes of the report types are a contract shared by every host:
changing a field is a breaking change for the CLI's `--format json` and for
each binding.
