# Configuration Examples

This directory contains example action schemas and event schemas for use with
the `dogwood` CLI and the Dogwood library. They serve two purposes:

1. **Defaults** — the pinned event schema and multi-action action schema are the
   compiled-in defaults when no explicit schema is provided.
2. **Examples** — other schemas demonstrate common patterns (unpinned traces,
   session pinning, custom event kinds, single-action minimal schemas).

## Action Schemas

| File | Description |
|------|-------------|
| `action-schemas/minimal.cedarschema` | Single action, one principal, one resource. The "hello world" schema. |
| `action-schemas/multi-action.cedarschema` | Login/Read/Write/Transfer/Alert/Heartbeat with input/output records. The default for tests and examples. |
| `action-schemas/multi-principal.cedarschema` | Multiple principal and resource types (User vs ServiceAccount, Document vs Folder). |

## Event Schemas

| File | Description |
|------|-------------|
| `event-schemas/pinned.dwschema` | **Default.** request/response/error with `pin callerPrincipal = principal` on all kinds → per-principal key-local semantics. |
| `event-schemas/unpinned.dwschema` | Same shape, no pins → global-trace semantics. Pass via `--event-schema` to see the behavioral difference. |
| `event-schemas/session-pinned.dwschema` | Pins on `sessionId` → per-session isolation instead of per-principal. |
| `event-schemas/custom-kinds.dwschema` | Author-defined kinds (`attempt`/`outcome`) showing that kind names are not fixed. |

## Usage

```bash
# Use the default (pinned) event schema — no flag needed:
dogwood validate policy.dw --policy-schema schema.cedarschema

# Use the unpinned schema to see global-trace behavior:
dogwood validate policy.dw --policy-schema schema.cedarschema \
    --event-schema configuration/event-schemas/unpinned.dwschema

# Replay with session-pinned semantics:
dogwood replay --trace trace.log --policy-schema schema.cedarschema \
    --event-schema configuration/event-schemas/session-pinned.dwschema
```
