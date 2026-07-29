# provider_filter_set_index_decimal

The guardrail flagship shape in one atom: a **set argument**
(`["VIOLENCE", "HATE"]`), an **index-then-field projection**
(`["VIOLENCE"].severityScore`), and a **decimal extension-method comparison**
(`.lessThan(decimal("0.5"))`), all via the `Content::Filter` information
provider. Permit `Read` only when the document's VIOLENCE severity is below 0.5.

The `Content::Filter(string, set<string>)` provider returns a per-category
record `{ VIOLENCE: { severityScore: decimal }, HATE: { severityScore: decimal } }`,
so the policy can index into `["VIOLENCE"]` and compare `.severityScore`.
The Rhai implementation is inlined into `providers.json` (the CLI does not
resolve a `scriptFile` path); `filter.rhai` is kept alongside for reference.

The trace shows all three cases:

- `@0` — `"violent"` scores VIOLENCE 0.90 (>= 0.5) -> **DENY**.
- `@10` — `"safe"` scores VIOLENCE 0.10 (< 0.5) -> **ALLOW**.
- `@20` — `"hateful"` scores VIOLENCE 0.10 (only HATE is high) -> **ALLOW**.

Referenced by `guide/05-information-providers.md`.
