# Handwritten Cedar Cases

Pure-Cedar policies hand-authored to exercise the cedar-only spine of the
Dogwood parser. Each case is a self-contained directory:

- `policy_<n>.dw` — Dogwood policy source. No `temporal { … }` or
  `guardrails { … }` extension markers — only Cedar scope, `when` /
  `unless` clauses, and core boolean/comparison expressions.
- `schema.cedarschema` — the Cedar schema the policy validates against.
- `README.md` — prose describing the case's intent.

## What is tested

These cases go through **parse + validate** only (no authorization).
The harness (`tests/passing/cedar_only/harness.rs`) asserts each case:
1. Parses successfully via `dogwood_language::api::parse()`
2. Validates against its paired schema via `dogwood_language::api::validate()`

Authorization decision testing is covered by the fuzz corpus
(`corpus_fuzz/`), which has entities and request manifests with
ground-truth decisions.

## Case ranges

| Range | Coverage |
|-------|----------|
| `documentation_0001..0003` | Basic permit, when clause, forbid overrides |
| `documentation_01xx` | Scope constraints, context access, annotations, if-then-else |
| `documentation_02xx` | Comparisons, string like, boolean combinators, datetime, multiple clauses |
