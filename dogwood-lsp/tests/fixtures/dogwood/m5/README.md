# Policy Semantic Fixtures

This directory contains locally authored policy fixtures plus three historical
Dogwood corpus snapshots under `upstream/`. The semantic tests assert exact
UTF-8 spans, UTF-16 positions, declarations, comments, tolerant fallback, and
deterministic truncation behavior.

Structural classification comes from `dogwood_language::syntax`, which reads
the canonical policy and temporal grammars. These snapshots remain useful as
regressions but no longer define a detached frontend version.
