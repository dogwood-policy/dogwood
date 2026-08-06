---
name: dogwood
description: "Orientation and router for authoring Dogwood authorization policies end to end. Run /dogwood when you are starting from scratch and are not sure which step you are on — it maps the lifecycle (action schema -> service schema, if needed -> policies -> validate/replay) and points you at the right task skill. This command only routes; it does not do the work itself. Not for a specific step — the three task skills (authoring-action-schema, authoring-service-schema, autoformalize-policies) each own their step."
disable-model-invocation: true
---

# Dogwood: where do I start?

This is the **entry point** for building a Dogwood authorization setup from
nothing. It is a *map and a router*, not a worker: it tells you the lifecycle
and hands you off to the one task skill that owns your current step. Each of the
three task skills named below does the actual authoring, points at the guide as
its ground truth, and ends in a **mandatory `dogwood` CLI gate**.

New to Dogwood entirely? Read the mental model first — it is short and pays for
itself. Paths are relative to this skill directory
(`.claude/skills/dogwood/`); the guide lives in the `dogwood-docs` crate:

- `../../../dogwood-docs/guide/00-introduction.md` — what Dogwood is, the
  problem it solves, and the five concepts (policies, events, schemas, temporal
  / providers, the authorizer). **Read this if you are new.**
- `../../../dogwood-docs/guide/README.md` — the full guide index and reading
  order, if you want the complete picture before starting.

## The lifecycle

An authorization setup is built in this order. Each step depends on the one
before it — **you cannot skip forward**.

1. **Action schema** — declare your world: entity types, actions, and each
   action's `context` shape (a Cedar `.cedarschema`). This is the one schema
   every policy needs, and it is **required before anything else**.
   → skill: **authoring-action-schema**
2. **Service schema** — *only if needed*. Customize the **event schema** (event
   *kinds* beyond the default `request`/`response`/`error`, pins, the
   `max_window` look-back cap) and/or declare **information providers**
   (computed facts / `guardrails`). Both default sensibly, so most setups skip
   this step entirely.
   → skill: **authoring-service-schema**
3. **Policies** — turn a natural-language rule ("permit X only if Y", "deny
   after Z", "no more than N per hour") into a validated `.dw` policy.
   → skill: **autoformalize-policies**
4. **Validate / replay** — check a policy set and watch a temporal policy decide
   across an event trace, with the `dogwood` CLI (`validate`, `replay`, `lower`,
   `check-parse`, and the `schema` checks).
   → guide: `../../../dogwood-docs/guide/12-cli.md`

## Which skill do I want?

Route on what you are trying to do:

- **"I need to define what actions / entities / request fields exist"** — or you
  have an MCP tool manifest to turn into a schema, or you have no schema yet at
  all → **authoring-action-schema** (step 1; do this first).
- **"My policies need event kinds beyond a plain request"** (history-only
  responses, custom decision kinds), **a look-back longer than 24h or
  any-principal (global-trace) semantics**, **or a computed fact / guardrail /
  risk score / regex / denylist** that isn't just a field of the request →
  **authoring-service-schema** (step 2; only after you have an action schema).
- **"I have a schema and want to write a policy from a plain-English rule"** →
  **autoformalize-policies** (step 3; requires an action schema, and a service
  schema if the rule needs custom events or providers).
- **"I already have a `.dw` policy and want to check it or replay a trace"** →
  the `dogwood` CLI; see `../../../dogwood-docs/guide/12-cli.md`.

If two of these seem to fit, pick the **earliest** one — an action schema is a
prerequisite for the service schema and for policies, so a missing prerequisite
is almost always the real blocker.

## Notes

- **Action schema vs service schema are different things.** The *action* schema
  is entities + actions + context (Cedar `.cedarschema`,
  **authoring-action-schema**). The *service* schema is event kinds + providers
  (the event-schema DSL and `providers.json`, **authoring-service-schema**).
  Don't conflate them — they have separate skills and separate `dogwood schema`
  checks (`schema action` vs `schema event` / `schema providers`).
- **Every task skill validates with the `dogwood` CLI before it is done.** A
  schema or policy that has not passed its CLI gate is not a finished answer.
  Exit codes are uniform across the tool: `0` ok/valid, `1` usage or I/O error,
  `2` rejected input. See `../../../dogwood-docs/guide/12-cli.md`.
- This command does not edit files or run the pipeline. Once you know your step,
  **invoke the named task skill** and follow it.
