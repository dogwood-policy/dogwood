# AGENTS.md

Guidance for AI coding agents working in the Dogwood policy-language package.
This file is intentionally short; it points to detailed procedures rather than
inlining them, so it costs little when it is not relevant.

## Working with Dogwood authorization

Setting up Dogwood authorization has a lifecycle, and there is a procedure
(a skill under `.claude/skills/`) for each stage. Follow the one matching what
the user is actually doing — each is the single source of truth for its task,
references the guide rather than duplicating it, and enforces a mandatory
`dogwood` CLI validation gate. Ignore this section for unrelated requests.

The lifecycle and its skills (dependency order):

1. **Action schema** — declare the Cedar `.cedarschema`: the entity types
   (principals/resources), one action per tool/operation, and each action's
   `context.input`/`output`/`system` layout — hand-written or generated from an
   MCP `tools/list` manifest. This is the prerequisite for everything else.
   → [`.claude/skills/authoring-action-schema/SKILL.md`](.claude/skills/authoring-action-schema/SKILL.md)
   (gate: `dogwood schema action schema.cedarschema`)
2. **Service schema (only if needed)** — the event schema (`.dwschema`: event
   kinds, decision vs history points, pins, the `max_window` look-back cap)
   and/or information providers (`providers.json` + Rhai). Optional; defaults
   sensibly (request/response/error kinds with only `request` deciding, a
   universal principal pin, a 24h window cap, no providers, standard macros).
   → [`.claude/skills/authoring-service-schema/SKILL.md`](.claude/skills/authoring-service-schema/SKILL.md)
   (gate: `dogwood schema event`/`providers`, then composite `dogwood validate`)
3. **Policies** — turn a natural-language authorization requirement ("permit X
   only if Y", "deny after Z", "no more than N per hour") into a validated
   `.dw` policy.
   → [`.claude/skills/autoformalize-policies/SKILL.md`](.claude/skills/autoformalize-policies/SKILL.md)
   (gate: `dogwood validate policy.dw --policy-schema schema.cedarschema`)
4. **Check / replay** — validate or replay existing files with the `dogwood`
   CLI. → [`dogwood-docs/guide/12-cli.md`](dogwood-docs/guide/12-cli.md)

Pick by what the user names: entities/actions/MCP tools → (1); event kinds or
providers → (2); a prose access rule → (3); running the CLI on existing files →
(4). Read the matching skill file and follow it exactly.

## Building this package

This is a Cargo workspace of Rust crates (`dogwood-language`, `dogwood-cli`,
`dogwood-docs`). Build and test with `cargo build` / `cargo test` from the
workspace root. See the crate READMEs and
[`dogwood-docs/guide/`](dogwood-docs/guide/README.md) for the language, and
[`dogwood-docs/guide/12-cli.md`](dogwood-docs/guide/12-cli.md) for the `dogwood`
CLI.
