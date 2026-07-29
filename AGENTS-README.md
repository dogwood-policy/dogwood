# AI Agent Integration

This repo ships a suite of agent skills that cover the Dogwood authorization
lifecycle — from declaring schemas to formalizing policies from natural language.
Each skill references the [language guide](dogwood-docs/guide/README.md) as its
source of truth and validates output with the `dogwood` CLI.

## Claude Code skills

The skills live under [`.claude/skills/`](.claude/skills/):

- **[`authoring-action-schema`](.claude/skills/authoring-action-schema/SKILL.md)** —
  stand up the Cedar action schema (entities, actions, `context` layout),
  hand-written or generated from an MCP tool manifest.
- **[`authoring-service-schema`](.claude/skills/authoring-service-schema/SKILL.md)** —
  set up the event schema and information providers (the optional service-schema
  half), when a policy needs history events or computed facts.
- **[`autoformalize-policies`](.claude/skills/autoformalize-policies/SKILL.md)** —
  turn a natural-language authorization requirement ("permit X only if Y", "deny
  after Z", "no more than N per hour") into a validated `.dw` policy.
- **`/dogwood`** — a user-only orientation command (type `/dogwood`) that maps
  the lifecycle and routes you to the right skill.

For common cases you don't invoke these explicitly: Claude Code loads the right
one **automatically** from what you describe. You can also run one directly by
name, e.g. `/authoring-action-schema`.

### Using them while working in this repo

Claude Code auto-discovers skills under `.claude/skills/`. Run Claude Code from
within this package and all skills are available with no setup.

### Using them in another project

```bash
# Project-scoped (commit them to share with your team):
cp -r .claude/skills/{authoring-action-schema,authoring-service-schema,autoformalize-policies} \
  <your-project>/.claude/skills/

# Or personal, available in every project:
cp -r .claude/skills/{authoring-action-schema,authoring-service-schema,autoformalize-policies} \
  ~/.claude/skills/
```

### Installing as a plugin

```text
/plugin marketplace add <this-repo-url>
/plugin install dogwood@dogwood
```

The skill is then available as `/dogwood:autoformalize-policies`. For local
development:

```bash
claude --plugin-dir /path/to/this/repo
```

## Other coding agents

The same guidance is exposed through a repo-root [`AGENTS.md`](AGENTS.md) — the
cross-agent instructions standard. `AGENTS.md` is a thin pointer: it tells the
agent to read the skill file only when the user asks to formalize a policy.

**Auto-discovered** (read `AGENTS.md` out of the box): OpenAI Codex CLI, Cursor,
GitHub Copilot, Windsurf, Cline.

**Claude Code** uses the native skills above (auto-loaded on demand). The
repo-root [`CLAUDE.md`](CLAUDE.md) imports `AGENTS.md` as well.

**Manual opt-in:**
- **Gemini CLI** — add `"AGENTS.md"` to `context.fileName` in settings.
- **Aider** — run with `--read AGENTS.md`.
