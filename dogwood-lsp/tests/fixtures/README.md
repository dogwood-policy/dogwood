# Dogwood LSP Test Fixtures

The fixture tree combines locally authored LSP edge cases with historical
Dogwood policies and schemas retained as regression snapshots.

- `lexical-*.dw` exercises tolerant tokenization and UTF-16 projection.
- `dogwood/m3/` covers complete bundle validation and CLI differential tests.
- `dogwood/m5/` covers parser-backed policy semantic spans.
- `dogwood/m6/` covers parser-backed event-schema semantic spans.
- `dogwood/m8/` covers expanded bundles, mutations, and performance workloads.

The LSP and `dogwood-language` now live in one workspace. Compatibility tests
build the sibling `dogwood-cli` package and compare
`dogwood validate --format json` with the in-memory LSP adapter. They do not
clone or pin a second Dogwood checkout.

The M3 and M8 manifests still record the historical source revision and
artifact provenance for copied snapshots. That metadata documents fixture
origins; it is not a production compatibility pin.
