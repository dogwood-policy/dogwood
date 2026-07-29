# provider_allowed_or_short

Disjunction and parentheses over two information providers: permit `Read` when
the document is EITHER explicitly allowlisted (`Lists::Allowed`) OR shorter than
4 characters (`Strings::Length`) — `(A || B)` — showing the `||` operator and
parentheses in a `when` body across two different providers.

The trace exercises both branches and both verdicts:

- `@0` — `readme` is on the allowlist → **ALLOW** (left branch).
- `@10` — `hi` is 2 chars, so `length < 4` → **ALLOW** (right branch).
- `@20` — `longfilename` is neither allowlisted nor short → **DENY**.
- `@30` — `manifest` is on the allowlist → **ALLOW** (left branch).

The two Rhai providers are declared in `providers.json`. Because the `dogwood`
CLI parses declarations with `ProviderDeclarations::from_json` (which does not
resolve `scriptFile`), the script bodies are inlined into `providers.json` via
the `script` field. `allowed.rhai` and `length.rhai` are kept alongside as the
readable source of those inlined bodies.

Referenced by `guide/05-information-providers.md`.
