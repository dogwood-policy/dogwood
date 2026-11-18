# Expanded Corpus Fixtures

The M8 manifest indexes three complete Dogwood bundles and a deterministic set
of component mutations. Tests compare the in-memory LSP frontend with the
sibling workspace `dogwood` CLI, verify parser-backed semantic spans, and check
that repeated runs are deterministic.

The manifest's revision and hashes document the historical source of these
snapshots. They are fixture provenance, not a production dependency pin.
