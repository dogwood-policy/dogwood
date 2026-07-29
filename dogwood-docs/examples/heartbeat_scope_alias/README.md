# heartbeat_scope_alias

`formerly` with **scope-alias correlation**. Permit an `Alert` only if a
`Heartbeat` for the **same server** *and* the **same request scope** fired
within the last hour (`formerly within 1h`).

The scope aliases `context.principal` / `context.resource` resolve to the
current request's scope entities and are pinned against the reserved event
fields `callerPrincipal` / `callerResource`, so a heartbeat only counts if
it came from the same principal on the same resource — not just any heartbeat
for that server.

The trace shows both outcomes:

- `@0` — `machine-a` sends a `Heartbeat` for `s1` (history-only event; no
  `Alert` permit applies, so the decision is a deny).
- `@100` — `machine-a` raises an `Alert` for `s1` → **allow** (its own
  heartbeat, same server, same principal/resource, is within the window).
- `@200` — `machine-b` raises an `Alert` for `s1` → **deny**: the server
  matches, but the scope-alias pins on `callerPrincipal` fail (the only
  heartbeat came from `machine-a`).

Referenced by `guide/04-temporal-expressions.md`.
