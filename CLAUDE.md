# CLAUDE.md

Claude Code reads this file; it does not read `AGENTS.md` automatically, so the
shared cross-agent guidance is imported here to keep a single source:

@AGENTS.md

Note for Claude Code specifically: the policy-authoring procedure above is also
packaged as the **`autoformalize-policies` skill** at
`.claude/skills/autoformalize-policies/`, which Claude Code loads automatically
when a user describes an authorization requirement. That skill is the native,
on-demand path — prefer it; the `AGENTS.md` pointer is the cross-agent fallback.
