# provider_principal_id_allowlist

Permit `Read` only when the requesting principal is on the provider's
allowlist. The distinctive shape is the provider **argument**: `Access::Allowed`
is passed `principal.id` — an attribute path rooted at `principal`, not
`context`. Provider arguments are resolved *pre-Cedar* against the request
event; `principal` / `resource` roots resolve to the request scope entity, and
a trailing `.id` projects that entity's id.

`allowed.rhai` stands in for a membership lookup with a one-name allowlist
(`alice`). Because the CLI loads `providers.json` via `from_json` (text only,
`scriptFile` is not resolved), the script is inlined into `providers.json` as
`implementation.script`; `allowed.rhai` is kept alongside for reference.

The trace has two decision points:

| tp | principal | `allowed` | verdict |
|----|-----------|-----------|---------|
| 0  | `alice`   | `true`    | ALLOW   |
| 1  | `mallory` | `false`   | DENY    |

Referenced by `guide/05-information-providers.md`.
