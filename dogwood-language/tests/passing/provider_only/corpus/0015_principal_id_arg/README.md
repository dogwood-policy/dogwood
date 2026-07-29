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
`callerPrincipal` / `callerResource` fields), and a trailing `.id` /
`.type` projects that entity's id or type. This mirrors the temporal-logic argument restriction
rule (`context` / `principal` / `resource` paths + literals + sets).

The trace has two decision points:

| tp | principal | `allowed` | verdict |
|----|-----------|-----------|---------|
| 0  | `alice`   | `true`    | `true`  |
| 1  | `mallory` | `false`   | `false` |

`allowed.rhai` stands in for a membership lookup with a one-name allowlist
(`alice`).
