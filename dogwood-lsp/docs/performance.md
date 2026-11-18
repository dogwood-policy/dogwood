# Performance Baselines

Performance reports are observational and never pass or fail on elapsed time.
Generate one from the current workspace:

```console
./scripts/performance --output target/m8-performance-report.json
```

`./scripts/check` also invokes the suite explicitly and writes its ignored
report to `target/check-performance-report.json`. The complete check fails on
workload output or metadata inconsistency, while elapsed values remain
report-only.

The report records that Dogwood comes from the same workspace, workload and fixture names,
bytes, lines, token/diagnostic/publication counts, dependency count, Cargo
profile, warm-up and sample counts, minimum/median/mean/maximum/total elapsed
nanoseconds, UTC generation time, OS, architecture, CPU, Rust, Cargo, and the
rerun command.

The eight workloads cover tolerant lexical fallback, valid parser-backed policy
analysis, valid event-schema analysis, complete bundle validation, invalid
diagnostic projection, UTF-16 semantic-token encoding over real stdio,
dependency revalidation, and incremental UTF-16 edits. The generated long-line
workload has many Unicode-aware tokens on one line and is also covered by
non-timing correctness regressions in the ordinary test suite.

Byte and line counts describe the complete source set consumed by each timed
operation. Multi-input policy analysis, validation, diagnostic projection, and
dependency revalidation include every relevant bundle input. The incremental
workload uses fixed-width astral replacements so its reported source size is
constant across all samples.

`performance-reference.json` is a reference observation, not a target. Update
it only by running the command above on identified hardware, reviewing every
metadata and workload field, and replacing the file without introducing a
machine-dependent assertion.
