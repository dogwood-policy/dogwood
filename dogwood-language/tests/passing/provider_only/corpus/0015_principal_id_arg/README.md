# 0015 — provider argument rooted at `principal`

Exercises a provider **argument** that is an attribute path rooted at
`principal` rather than `context` — the capability opened by the
provider-path unification (before it, provider arguments were restricted to
`context.<field>` paths + literals + sets, in both the wrapped and unwrapped
forms).

`Access::Allowed(principal.id).allowed == true` passes the request
principal's id to the provider. Provider arguments are resolved *pre-Cedar*
against the request event: a `principal` / `resource` root resolves to the
request scope entity (carried on the event as the reserved
`callerPrincipal` / `callerResource` fields), and a trailing `.id` reads that
entity's `id` attribute, as in Cedar: the trace supplies it in each event's
`entities(...)` data. This mirrors the temporal-logic argument restriction
rule (`context` / `principal` / `resource` paths + literals + sets).

The trace has four decision points:

| tp | principal | supplied `id` | `allowed` | verdict |
|----|-----------|---------------|-----------|---------|
| 0  | `alice`   | `"alice"`     | `true`    | `true`  |
| 1  | `mallory` | `"mallory"`   | `false`   | `false` |
| 2  | `carol`   | `"alice"`     | `true`    | `true`  |
| 3  | `alice`   | `"mallory"`   | `false`   | `false` |

The last two show that the provider receives the supplied attribute, not the
uid's id: under the uid reading, they would be `false` and `true`.

`allowed.rhai` stands in for a membership lookup with a one-name allowlist
(`alice`).
