# 0030 — provider reads a non-`input` context group (`context.system`)

A provider argument reads `context.system.hour` — a request-context group other
than `input`. This pins the decision that provider `context.<path>` arguments
resolve against the request **context record** (`request_context`), the same bag
the Cedar request context and temporal `context.<path>` read — NOT the logged
temporal record.

The distinction is observable here precisely because the trace supplies `system`
**only** in `request_context(...)`, never in the trailing (logged) group. Before
provider args were switched onto `request_context`, `context.system.hour` would
have read the logged record, found nothing, and resolved to `Null` (denying
every request); reading `request_context` it resolves correctly.

`Time::WithinHours(hour)` permits only when `9 <= hour < 17` (business hours):

- `@0`  hour 10 → within hours → permit.
- `@10` hour 3  → too early    → deny.
- `@20` hour 20 → too late     → deny.
- `@30` hour 16 → within hours → permit.
