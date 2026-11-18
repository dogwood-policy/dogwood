# Event-Schema Semantic Fixtures

This directory contains locally authored event-schema fixtures plus two
historical Dogwood corpus snapshots under `upstream/`. Tests cover exact
semantic spans, UTF-16 encoding, comments, nested fields, pins, invalid input,
and deterministic truncation fallback.

Structural classification comes from `dogwood_language::syntax`, backed by the
canonical event-schema grammar in the sibling language crate.
