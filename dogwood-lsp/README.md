# Dogwood LSP

Dogwood LSP is the pure editor-agnostic server in this Cargo workspace. The
`dogwood-lsp` package contains the server, protocol implementation, tests,
and documentation; it contains no editor extension source, packaging, or UI.
It depends on sibling `dogwood-language` for parsing, validation, and
canonical parser-backed syntax spans, so it contains no Dogwood grammar
copies. The `dogwood-lsp` binary publishes diagnostics and semantic tokens for
`.dw` policies and `.dwschema` event schemas over standard input and output.

## Workspace and ownership boundary

The LSP and language packages are reviewed and built from the same source
revision. `dogwood-language` owns the canonical policy, temporal, and
event-schema Pest grammars and exposes an editor-neutral syntax-span API. The
LSP maps those spans to its frozen protocol legend.

See [`docs/dogwood-frontend.md`](docs/dogwood-frontend.md) for the public API
boundary and same-workspace differential-test design.

## Transport limits

The server reads protocol messages from standard input, writes protocol
messages to standard output, and writes logs only to standard error. Each
inbound frame may contain at most 8 KiB of headers, including the header
terminator, and a JSON body of at most 16 MiB (16,777,216 bytes). The server
rejects malformed or unsupported framing and exits with a nonzero status.

## Features

The server advertises two language capabilities: published diagnostics and
full-document semantic tokens. Editors may render semantic tokens as syntax
highlighting. The server also implements incremental synchronization,
cancellation, and dependency revalidation.

### What It Provides

- Authoritative, project-aware diagnostics for open `.dw` policies. Validation
  includes the resolved action schema and optional event schema, providers, and
  macros, and matches the workspace `dogwood validate` pipeline.
- Standalone authoritative diagnostics for every open `.dwschema` event
  schema.
- Parser-backed semantic tokens for valid, complete `.dw` and
  `.dwschema` files, with tolerant lexical highlighting preserved while a file
  is incomplete or invalid.
- Incremental document synchronization, cancellation, and automatic
  revalidation of dependent open policies when a resolved project input
  changes.
- Editor-independent LSP communication over standard input and output using
  UTF-16 positions.

### What It Does Not Provide

- Completion, snippets, or automatic imports.
- Hover documentation, signature help, or type information.
- Go to definition, find references, rename, document symbols, breadcrumbs, or
  other navigation and indexing features.
- Formatting or format-on-save support.
- Code actions or quick fixes, even when a diagnostic identifies a problem.
- A schema editor, bundle picker, project-setup wizard, commands, status bar,
  or other editor UI.
- Workspace-wide diagnostics for closed policies or event schemas.
- Direct diagnostics or semantic tokens for dependency-only files such
  as `.cedarschema`, `providers.json`, and configured macro libraries. Problems
  in those inputs are reported on dependent open policies with related
  locations where available.
- A TextMate grammar or fixed colors. Editors must enable semantic tokens, and
  the active theme determines the rendered syntax highlighting.
- Diagnostic pull, semantic-token ranges, semantic-token deltas or refresh,
  or an editor-specific API.

## Build and Run

From the repository root:

```console
cargo build --bin dogwood-lsp
cargo run --bin dogwood-lsp
```

From this crate directory, run the server-specific checks with:

```console
./scripts/check
```

The check covers:

- Rust formatting, Clippy, and tests with default and all features;
- compiled-server black-box protocol tests;
- differential checks against the sibling workspace `dogwood` CLI; and
- the report-only performance suite.

## Performance

The following report-only medians were observed on 2026-08-23 on Linux ARM64
with 64 logical CPUs, Rust 1.96.0, three warm-ups, and ten samples. These are
unoptimized `cargo test` measurements, not release-build targets or pass/fail
thresholds.

| Workload | Fixture/output | Median |
|---|---|---:|
| Lexical fallback | 57 KiB, 16,385 tokens | 13.1 ms |
| Valid policy analysis | 2.5 KiB, 71 tokens, 3 dependencies | 3.3 ms |
| Valid event-schema analysis | 600 bytes, 61 tokens | 0.82 ms |
| Full bundle validation | 4.8 KiB, 4 dependencies | 69.6 ms |
| Invalid diagnostic projection | 4.4 KiB, 1 diagnostic | 0.56 ms |
| UTF-16 token encoding over stdio | 57 KiB, 16,385 tokens | 92.5 ms |
| Dependency revalidation | 4.8 KiB, 4 dependencies | 69.4 ms |
| Incremental edit and publication | 32 KiB event schema | 21.8 ms |

The generated JSON includes minimum, median, mean, maximum, and total elapsed
nanoseconds plus complete workload and host metadata. See
[`docs/performance.md`](docs/performance.md) for interpretation and
[`docs/performance-reference.json`](docs/performance-reference.json) for the
checked-in non-normative reference report.

Regenerate the report with:

```console
./scripts/performance --output target/m8-performance-report.json
```

The complete check writes its report to
`target/check-performance-report.json`.

## Document classification and synchronization

At `didOpen`, the server assigns one immutable document kind. A `.dw`
extension selects Policy and `.dwschema` selects EventSchema regardless of
language ID. Otherwise `dogwood-event-schema` selects EventSchema for an
unambiguous absolute file URI, except that `.cedarschema`, `.json`, and
arbitrary explicitly configured dependency paths remain Dependency-only.
Generic `dogwood` and unknown IDs rely on a known extension; generic `dogwood`
does not infer an event schema. Dependency documents are retained only to
validate open policies and never receive semantic tokens.

The server uses incremental document synchronization and reports UTF-16
positions. Ordered range edits and full-document replacements are both
accepted; an invalid change list is rejected atomically. It supports
full-document semantic-token requests for Policy and EventSchema documents.
Lexical analysis is tolerant of incomplete input. Structural classifications
are added only for exact ranges from a complete strict parse. Project policies
use the same resolved in-memory-or-disk service inputs as diagnostics,
including configured macro libraries; unresolved or unreadable bundles remain
lexical.

## Concurrency and cancellation

Each semantic-token request is capped at 262,144 lexical tokens, indexed source
lines, and emitted line-local token segments. Analysis runs on a bounded worker
outside the protocol state owner. `$/cancelRequest` cancels queued or running
semantic-token work. Diagnostics take queue priority; a displaced or rejected
semantic request receives `ServerCancelled`. An accepted edit or close returns
`ContentModified` for pending semantic work on that source. Standard-input
framing also uses a bounded 64-message channel, which backpressures the reader
during input bursts. See
[`docs/concurrency.md`](docs/concurrency.md) for the snapshot, staleness,
ordering, cancellation, and shutdown contract.

## Diagnostic projection

The internal frontend validates complete in-memory Dogwood bundles against the
sibling `dogwood-language` crate. Production never invokes the Dogwood CLI.
Server-published diagnostics carry the current document version. Every open
EventSchema receives standalone diagnostics from the workspace frontend;
valid source publishes an empty list and close clears the last version. Error,
warning, and advice findings map to LSP error, warning, and information
severities. Dogwood messages, string codes, and emission order are preserved.
Policy byte spans are converted to UTF-16 ranges; findings attributed to
another bundle input remain on the policy at zero range with related
information pointing to that input. Configuration and load failures remain
policy diagnostics, so an empty policy diagnostic set means the entire
resolved bundle passed without errors or warnings.

## LSP Project Configuration

The server selects the deepest configured workspace folder containing each
policy. It uses `workspaceFolders` when the list is present and nonempty, then
falls back to one `rootUri` when the list is absent or empty. Policies outside
those folders receive a configuration diagnostic.

Without explicit options, the server walks from the policy directory through
its workspace root and selects the nearest directory containing a
`.cedarschema` action schema. Within that directory, `actions.cedarschema` is
preferred; otherwise exactly one `.cedarschema` file must exist. Multiple
non-preferred candidates produce a configuration diagnostic instead of an
arbitrary choice. The server also uses `events.dwschema`, `providers.json`, and
`macros.dw` from the selected directory when present. Missing optional files
use Dogwood defaults; a missing required action schema is diagnostic.

Explicit configuration uses this strict `initializationOptions` contract:

```json
{
  "bundles": [
    {
      "workspaceFolder": "file:///workspace",
      "actionSchema": "config/actions.cedarschema",
      "eventSchema": "config/events.dwschema",
      "providers": "config/providers.json",
      "macros": "config/macros.dw"
    }
  ]
}
```

`workspaceFolder` must exactly identify one configured folder.
`actionSchema` is required; the other paths are optional. Relative paths are
resolved within that workspace folder and may not traverse outside it.
Existing explicit dependency paths and ancestors must already be canonical:
symlink aliases are rejected for both relative and absolute paths. Normal
absolute paths are accepted, including external paths. A nonexistent explicit
path remains a load diagnostic and can recover after watched creation. Unknown
fields, duplicate bundle entries, invalid URIs, and ambiguous workspace entries
produce stable policy diagnostics rather than falling back to syntax-only
validation.

Open dependency text takes precedence over disk. Opening, changing, or closing
a resolved event schema publishes its standalone state and revalidates only
dependent open policies; close clears the schema URI and falls back to disk for
policy validation. Other resolved dependencies retain the same M4 invalidation
behavior. `workspace/didChangeWatchedFiles` creation, change, and deletion
events also trigger dependency revalidation and conventional bundle
rediscovery. When
the client advertises
`workspace.didChangeWatchedFiles.dynamicRegistration: true`, the server sends
one `client/registerCapability` request after `initialized`. It registers the
four conventional input names under configured workspace roots and every
explicit dependency path. External explicit dependencies are registered as
exact relative patterns rooted at their absolute parent URI and require
`workspace.didChangeWatchedFiles.relativePatternSupport: true`. An external
bundle remains non-clean with a stable project diagnostic while registration is
unsupported or pending, and after the client rejects registration or returns a
non-null result. Only a matching null-success response enables validation of
external bundles and triggers current-version revalidation. Clients without
dynamic registration receive no registration request; explicitly sent
watched-file notifications and internal bundles remain supported. Closing a
policy publishes an empty diagnostic set at its current version and removes its
dependency tracking.

[`src/legend.rs`](src/legend.rs) defines the fixed semantic-token legend.
[`src/protocol/mod.rs`](src/protocol/mod.rs) defines protocol error codes and
messages. [`tests/stdio_black_box.rs`](tests/stdio_black_box.rs) freezes both
contracts.

The server returns these errors without an `error.data` field:

| Condition | Code | Message |
|---|---:|---|
| Request before `initialize` | `-32002` | `Server not initialized` |
| Request after `shutdown` | `-32600` | `Server has shut down` |
| Duplicate `initialize` | `-32600` | `Initialize request may only be sent once` |
| Unknown, unopened, or closed document | `-32803` | `Document is not open` |
| Semantic token resource limit exceeded | `-32803` | `Semantic token limit exceeded` |
| Client-cancelled semantic request | `-32800` | `Request cancelled` |
| Source changed during semantic request | `-32801` | `Content modified` |
| Analysis queue rejects or evicts a semantic request | `-32802` | `Server cancelled` |
| Malformed method parameters | `-32602` | `Invalid params` |
| Unknown method while running | `-32601` | `Method not found` |

[`docs/protocol-conformance.md`](docs/protocol-conformance.md) maps every
advertised capability and documented error path to a compiled-process
assertion. [`docs/performance-reference.json`](docs/performance-reference.json)
records one non-normative reference run with complete workload and host
metadata.
