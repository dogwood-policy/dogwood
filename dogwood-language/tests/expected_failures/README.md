# Expected Failures

Policies that are intentionally rejected by the frontend. The harness asserts
each FAILS — either at `parse` (syntax / lowering) or at `validate`
(event-schema / temporal / provider findings). It does not care which layer
catches a case, only that the frontend rejects it.

## Error-message pinning

When a case directory contains an `expected_error.txt` file, the harness also
asserts the error message matches exactly. This pins diagnostic quality and
prevents regressions. To regenerate the files after intentionally changing
error messages:

```
cargo test --test expected_failures -- --ignored generate_expected_error_files --nocapture
```

To overwrite existing files (when updating all messages):

```
OVERWRITE=1 cargo test --test expected_failures -- --ignored generate_expected_error_files --nocapture
```

## Categories

- **Removed implicit aggregation** (`0426`–`0974`): `sum a where ...` /
  `count where ...` without `for` binders — syntax removed in Phase B
  (rejected at `parse`).
- **Event-schema defects** (`1030`–`1034`): unknown action / kind / field, an
  output field on a `request` event, an injected unknown field — rejected at
  `validate` (the event-schema names check is a validation finding, not a
  fatal parse error).
- **Temporal field-pattern type mismatches** (`1035`–`1037`): a temporal
  predicate field pattern (`Tool2::request{ input.mode: <value> }`) whose
  declared type is an entity type, bound to a value of the wrong type — an
  entity of a different type (`1035`), an int (`1036`), or a bare string
  (`1037`). These should be rejected at `validate` by the temporal
  type-checker, the same way it already rejects mismatched `==`/`!=` operands.
  Regression guard for a bug where field-pattern arguments (`input.<field>`)
  were not type-checked at all, so a mis-typed literal validated cleanly and
  then silently never matched a real event at runtime.
- **Cedar-parallel scalar-vs-entity mismatches** (`1039`–`1040`): the
  base-Cedar analogues of `1036`/`1037` — a plain `when { context.input.mode ==
  <value> }` where `input.mode` is entity-typed and the value is an int
  (`1039`) or a bare string (`1040`). Cedar's own strict-mode validator rejects
  these as hard type errors ("the types Long/String and … are not
  compatible"), so they belong here. They establish that the scalar-vs-entity
  gap in the temporal cases is NOT a limitation of Cedar itself. (The
  entity-vs-entity analogue of `1035` is deliberately absent: Cedar treats any
  `entity == entity` as well-typed and only emits an "impossible policy"
  *warning*, not an error — so it is not an expected failure. Only the temporal
  dialect, whose type-checker is stricter and requires equal entity tags, hard-
  rejects that swap.)
- **Non-`Long` aggregation summands** (`1041`–`1043`): a `sum <v> for (<v>: T),
  … . where …` whose *summand* (the value added together) is not a `Long` — a
  `Timepoint` (`1041`), a `decimal` (`1042`), or a `String` (`1043`). Only
  `Long` is summable: Dogwood arithmetic operates only on `Long` (matching
  Cedar, whose `+`/`-`/`*` are Long-only), decimals aren't summable, and
  timepoints are ordinal positions, not quantities. Regression guard for a bug
  where the summand's type was never checked (`term_type(Agg)` reports the whole
  aggregate as `int`, and the summand is a *use*, not a declaration site) — so a
  non-`Long` summand validated cleanly. Summing decimals has no defined meaning
  in Dogwood, so it must be rejected rather than left to each implementation to
  interpret. A `Timepoint` in the `for (…)` binders remains valid — it
  controls per-timepoint row distinctness; only the summand is constrained.
- **Summand not in the `for` list** (`1044`): a `sum <v> for (<binders>). where
  …` whose summand `<v>` is bound in scope (e.g. by an enclosing `exists`) but
  is *not* one of this aggregation's own `for` binders. This is a parse-time
  binding defect (in `check.rs`), distinct from the summand *type* checks above:
  `eval_agg_expr` projects the match relation onto the `for` columns and then
  sums the summand's column, so a summand outside `for_vars` has no column and
  silently sums to 0. The summand must appear in the `for` list. (This
  parse-time check also subsumes the enclosing-bound case for the type checks
  above — an enclosing-bound summand is rejected here before typing runs.)
- **Pure-Cedar parse errors** (`2001`–`2056`): broken pure-Cedar policies
  testing every grammar position where a syntax error can occur. These pin
  error-message parity with Cedar's parser (the "unexpected token" style
  and helpful hints like "expected expression"). Categories:
  - `2001`–`2008`: top-level structure (effect keyword, parens, semicolons)
  - `2009`–`2016`: scope (variables, operators, entity UIDs)
  - `2017`–`2022`: conditions (`when`/`unless`, braces, body)
  - `2023`–`2047`: expressions (operators, delimiters, if/then/else,
    has/like/is, member access, records, sets)
  - `2048`–`2053`: entity references and annotations
  - `2054`–`2056`: literals (overflow, standalone operators)

If a case both parses AND validates cleanly (e.g. a defect is reintroduced as
valid), the harness panics.
