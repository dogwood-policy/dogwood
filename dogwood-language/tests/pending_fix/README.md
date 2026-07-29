# Pending Fix

Cases that currently produce incorrect results but will be fixed before GA.

## temporal_divergences/ (21 cases)

Known verdict divergences from the reference monitor. These policies parse and evaluate but produce different verdicts than the proven reference monitor.

Categories:
- **Explicit false-verdict emission** (15 cases): a verdict mode where certain decision points emit `false` (not just silent deny); not yet modeled.
- **UID-based event idempotence** (3 cases): duplicate events with the same `requestId` should not be re-counted as fresh anchors.
- **Temporal edge semantics** (3 cases): corner cases in quote handling and entity correlation.

When a case is fixed, move it to `passing/temporal_only/temporal_corpus/`.
