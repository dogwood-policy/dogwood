# login_attempt_custom_kind

A custom, author-defined event kind. The per-case event schema
(`event.dwschema`) names `attempt` as the decision kind and `outcome` as
history (instead of the conventional `request`/`response`), and renames the
injected principal field to `actor` (instead of `callerPrincipal`). The
policy permits a `Read` only if the **same actor** formerly attempted a `Login`
within the last hour (`formerly within 1h`, correlating `actor:
context.principal` and `input.user: context.input.user`).

The event schema is passed with `--event-schema event.dwschema`; without it the
CLI would default to `request`/`response` and reject the `::attempt` kind.

The trace shows all three cases:

- `@0` — alice attempts a `Login` (a history-only event here; no `Read` permit
  applies to a login, so the decision is a **deny**).
- `@10` — alice reads, 10s after her login → **allow** (a matching login by the
  same actor is within the window).
- `@20` — bob reads with no prior login of his own → **deny**.

Referenced by `guide/04-temporal-expressions.md`.
