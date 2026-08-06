# Test Suite — dogwood-language

Tests are separated by **outcome** (passing / expected failure) and grouped by **dialect**.
Each category has its own harness in `Cargo.toml`. No snapshots — tests verify parse success,
verdict correctness, or expected rejection.

## Structure

```
tests/
├── passing/
│   ├── cedar_only/           7,499 cases (32 handwritten + 7,467 fuzz)
│   ├── temporal_only/        475 cases + shared_schema.cedarschema
│   ├── provider_only/        42 cases + corpus/shared_schema.cedarschema
│   ├── macros/               144 cases
│   └── mixed/                15+ cases
├── expected_failures/        164 cases (pinned error messages)
├── pending_fix/              0 cases (all resolved)
├── docs_as_tests/            7 API usage examples
└── fixtures/                 Shared event schema
```

## Schema Consolidation

Each corpus has a **shared schema** as the default fallback. Cases only keep a
per-case `schema.cedarschema` when they need non-standard types or actions.
Guardrail types use `confidenceScore`, aligned with the canonical
`drupe.cedarschema` stub.

## Embedded Corpus (`--features corpus`)

Embeds all cases (~13MB) into the library so an alternative engine can be
checked against them.
Off by default.

## Running

```bash
cargo test                              # all
cargo test --test passing_temporal_only # one harness
cargo test --features corpus corpus::tests  # embedded corpus
DUMP_AST=1 cargo test --test passing_cedar_only  # with AST dump
```

## Adding a Temporal Case

Create a directory in `tests/passing/temporal_only/corpus/` with:
- `policy_1.dw` — the policy
- `trace_1.log` — the event trace
- `expected_1.out` — expected verdicts

No `schema.cedarschema` needed if the shared schema covers the actions used.
To recategorize, move the directory between `passing/`, `pending_fix/`, or
`expected_failures/`.
