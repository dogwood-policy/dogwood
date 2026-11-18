# Concurrency and Snapshot Contract

The protocol thread is the only owner of mutable lifecycle, document, project
resolution, reverse-dependency, and publication state. Standard-input framing
runs on a reader thread and feeds a bounded channel of 64 decoded messages.
Once full, the reader blocks before decoding more input, bounding framed-message
memory while leaving enough room for normal editor bursts.

Dogwood validation and semantic analysis run on one bounded analysis worker
with at most 1,024 queued tasks. Diagnostics are coalesced by policy path or
schema URI and ordered ahead of queued semantic requests. A diagnostic may
evict the oldest queued semantic request, which receives `ServerCancelled`
exactly once. If the queue contains only diagnostics, the owner records one
dirty key per current policy/schema and retries from current authoritative
state whenever a worker slot opens.

A complete validation bundle that has not started exists only in that bounded
queue. Production therefore retains at most 1,024 not-started full validation
snapshots, independent of policy fanout; deterministic test mode lowers the
same limit to four. One additional bundle may be active on the worker. Policies
beyond the admitted limit retain only their path, resolved input paths,
generation, document version, and bundle path/revision identity. The protocol
owner materializes the latest bundle only after the scheduler confirms
diagnostic capacity, so a rejected queue admission never leaves a full bundle
on a dirty policy.

## Document and Bundle Identity

Every accepted open or change receives a monotonic server revision. Document
text is stored as `Arc<str>`; work receives an immutable revision and text
snapshot. A policy validation task receives one complete immutable bundle:

- policy;
- required action schema;
- optional event schema;
- optional providers; and
- optional macros.

Each source identity contains its resolved path and either its open-document
version and revision or its accepted watched-file revision. Disk source content
is read once per stable path/revision identity and stored as one shared
`Arc<str>`; every admitted policy snapshot clones that allocation rather than
rereading or copying the input. A watched-file event or open/close transition
invalidates the path's cached revision, and the cache entry is removed when no
tracked policy depends on it. Resolution and reverse-dependency edges are
replaced on the protocol owner before work is scheduled.

Each policy revalidation increments a generation and supersedes queued or
running work for that policy. A completion publishes only when its generation
and complete bundle identity still match the current tracked bundle. Source
edits, dependency edits, resolution changes, close, and watched-file events
therefore suppress old completions. Closing a policy removes its dependency
edges and publishes the existing versioned clear.

## Incremental Changes

The server advertises `TextDocumentSyncKind::INCREMENTAL`. Changes in one
`didChange` are applied in array order. Ranges use UTF-16 code units and must
land on Unicode scalar boundaries. CRLF, lone CR, and lone LF are line
terminators; CRLF counts as one line boundary. Line content excludes the
terminator, and a cross-line range includes the terminator bytes between its
positions. Insert, delete, replace, multiple range changes, and a range-less full
replacement are accepted.

All changes are first applied to a temporary string. An invalid version, empty
change list, out-of-bounds position, reversed range, surrogate split, or
incorrect `rangeLength` rejects the notification without changing text,
version, or revision.

## Semantic Requests

Semantic-token responses remain full responses; delta and refresh are not
implemented. A request captures one source revision and the current immutable
semantic input. Its terminal behavior is deterministic:

- unchanged source: return tokens or the existing analysis error;
- accepted source edit or close before completion: return `ContentModified`
  (`-32801`);
- matching `$/cancelRequest`: return `RequestCancelled` (`-32800`);
- bounded queue rejection or diagnostic-priority eviction: return
  `ServerCancelled` (`-32802`).

The owner removes a request from pending state when it emits a terminal
response. A later cancellation or worker completion cannot emit another.

## Shutdown

`shutdown` drops dirty metadata, completed semantic snapshots, and shared disk
source cache entries, cancels queued and running work, and returns cancellation
errors for pending semantic requests without waiting for Dogwood analysis.
`exit` drops the scheduler, releases queued snapshots, wakes a test-paused
worker, and joins the worker before process termination. Dogwood analysis
already in progress is bounded by the existing frontend source and token limits
and is allowed to finish before the join completes.

## Deterministic Test Control

Compiled-process concurrency tests build with the non-default `test-control`
Cargo feature and set `DOGWOOD_LSP_TEST_CONTROL=1`. Only
then, the private `dogwood-lsp/testControl` request can pause the next
`validation` or `semantic` worker checkpoint and the server emits
`dogwood-lsp/testReached` with its task ID. The same switch enables
`dogwood/testBarrier`: it waits for running, queued, and dirty diagnostic work
to finish, then returns the ordinary `MethodNotFound` response used by the
pre-M7 test harness. Test mode also reduces the analysis queue to four entries
so saturation is deterministic. Its `snapshotStats` command reports the
retention limit, queued and active validation snapshots, dirty policies,
completed policy snapshots, and shared disk cache entries, bytes, and read
count. This read-only command remains available after `shutdown` so tests can
verify release before `exit`. Tests release an exact paused task or exercise
normal cancellation.

Without the explicit environment switch, both private request methods return
`MethodNotFound` immediately and are never retained. The server does not
advertise any test-only surface.
