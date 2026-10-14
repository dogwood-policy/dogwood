# Passing Tests

All cases here are expected to pass in CI. Organized by dialect:

| Directory | Cases | What's tested |
|-----------|------:|---------------|
| `cedar_only/corpus_handwritten/` | 32 | Pure-Cedar policies parse + validate against paired schemas |
| `cedar_only/corpus_fuzz/` | 7,467 | Cedar fuzz corpus from cedar-policy/cedar-integration-tests (parse + validate) |
| `temporal_only/temporal_corpus/` | 399 | Temporal verdict-stream tests (authorize_trace vs expected output) |
| `provider_only/corpus/` | 94 | Information-provider dialect verdict tests; policies must also validate (opt out with `skip_validation.txt` stating why). `NNNN_enum_*` cover enum-typed provider values, including a multi-vendor guardrail declarations file |
| `macros/macro_corpus/` | 21 | `def cedar` / `def temporal` macro expansion verdict tests |

## Adding a new case

1. Pick the appropriate dialect folder
2. Create a subdirectory with the case files (policy_*.dw + schema.cedarschema + trace_*.log + expected_*.out)
3. Run the corresponding harness to verify it passes
