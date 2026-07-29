# Dogwood

<!-- TODO: write the full README. Placeholder to satisfy the OSS hygiene check. -->

Dogwood is a policy language: a Cedar-derived surface syntax with temporal
(history-dependent) conditions and information providers, lowered to Cedar. See
the [language guide](dogwood-docs/guide/README.md) and the
[`dogwood` CLI](dogwood-docs/guide/12-cli.md).

## The Dogwood skills

This repo ships a suite of Claude Code [Agent Skills](https://code.claude.com/docs/en/skills)
that cover the Dogwood authorization lifecycle. Each references the guide as its
source of truth and validates its output with the `dogwood` CLI. They live under
[`.claude/skills/`](.claude/skills/):

- **[`authoring-action-schema`](.claude/skills/authoring-action-schema/SKILL.md)** —
  stand up the Cedar action schema (entities, actions, `context` layout),
  hand-written or generated from an MCP tool manifest. The prerequisite for the
  rest.
- **[`authoring-service-schema`](.claude/skills/authoring-service-schema/SKILL.md)** —
  set up the event schema and information providers (the optional service-schema
  half), when a policy needs history events or computed facts.
- **[`autoformalize-policies`](.claude/skills/autoformalize-policies/SKILL.md)** —
  turn a natural-language authorization requirement ("permit X only if Y", "deny
  after Z", "no more than N per hour") into a validated `.dw` policy.
- **`/dogwood`** — a user-only orientation command (type `/dogwood`) that maps
  the lifecycle and routes you to the right skill when you are starting out.

For the common cases you don't invoke these explicitly: Claude Code loads the
right one **automatically** from what you describe (declaring an action → the
action-schema skill; a prose access rule → autoformalize; and so on). You can
also run one directly by name, e.g. `/authoring-action-schema` (or
`/dogwood:authoring-action-schema` when installed as a plugin).

### Using them while working in this repo

Claude Code auto-discovers skills under a project's `.claude/skills/` directory.
So if you run Claude Code from within this package, all of them are available
with no setup — just describe what you want.

### Using them in another project

Copy (or symlink) the skill directories into the target project's — or your
personal — skills directory:

```bash
# Project-scoped (commit them to share with your team):
cp -r .claude/skills/{authoring-action-schema,authoring-service-schema,autoformalize-policies} <your-project>/.claude/skills/

# Or personal, available in every project:
cp -r .claude/skills/{authoring-action-schema,authoring-service-schema,autoformalize-policies} ~/.claude/skills/
```

Then invoke one by name (e.g. `/autoformalize-policies`) or let Claude load it
automatically. Note: the skills' guide references are relative to this repo, so
for the richest behavior run them where the `dogwood-docs/guide/` files and the
`dogwood` CLI are reachable.

### Installing them as a plugin

This repo is also a Claude Code plugin marketplace. To install the `dogwood`
plugin (which bundles all the skills) into your Claude Code:

```text
/plugin marketplace add <this-repo-url>
/plugin install dogwood@dogwood
```

The skill is then available as `/dogwood:autoformalize-policies`. For local
development you can instead load it for a single session without installing:

```bash
claude --plugin-dir /path/to/this/repo
```

The plugin reuses the same single skill directory (`.claude/skills/`) via the
`skills` path in [`.claude-plugin/plugin.json`](.claude-plugin/plugin.json) —
there is no second copy to keep in sync.

## Other coding agents

The same policy-authoring guidance is exposed to non-Claude agents through a
repo-root [`AGENTS.md`](AGENTS.md) — the emerging cross-agent instructions
standard. `AGENTS.md` is a *thin pointer*: it tells the agent to read
`.claude/skills/autoformalize-policies/SKILL.md` (the single source of truth)
**only when** the user asks to formalize a policy, so it adds almost nothing to
an agent's always-on context otherwise.

**Read out of the box** (they auto-discover a repo-root `AGENTS.md`): OpenAI
Codex CLI, Cursor, GitHub Copilot, Windsurf, Cline. Just work in the repo and
ask for a policy — the agent picks up the pointer.

**Claude Code** does not read `AGENTS.md`; it uses the native skill above
(auto-loaded on demand). The repo-root [`CLAUDE.md`](CLAUDE.md) imports
`AGENTS.md` as well, so the guidance has a single source across all agents.

**Manual opt-in** (these don't read `AGENTS.md` automatically today):
- **Gemini CLI** — add `"AGENTS.md"` to `context.fileName` in your Gemini
  settings, or point it at the skill file directly.
- **Aider** — run with `--read AGENTS.md` (or `--read
  .claude/skills/autoformalize-policies/SKILL.md`).

In every case the guidance lives in exactly one file
(`.claude/skills/autoformalize-policies/SKILL.md`); the per-agent files only
point at it.
