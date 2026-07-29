---
name: authoring-action-schema
description: "Stand up the Cedar ACTION schema (.cedarschema) a Dogwood deployment governs — its entity types (principals/resources), one action per tool/operation, and each action's context.input/output/system layout — either hand-written or generated from an MCP tools/list manifest. Use when a user needs to declare the entities and actions that policies will scope over, map MCP tools to Cedar actions, or run `dogwood schema mcp`. This is the ACTION schema (entities + actions + context) — the prerequisite for both later skills. Not for writing policies — that is autoformalize-policies. Not for declaring event kinds or information providers (the SERVICE schema) — that is authoring-service-schema. Not for general \"set up Dogwood from scratch\" / \"I don't know where to start\" orientation when no specific entity, action, or MCP manifest is named — route those to the /dogwood orientation command."
---

# Authoring the Cedar action schema for a Dogwood deployment

Your job: produce the **action schema** — a Cedar `.cedarschema` — that declares
the world a Dogwood deployment governs: its **entity types** (the principals and
resources), **one action per tool/operation**, and each action's **`context`**
laid out as `input` / `output` / `system`. This schema is the foundation every
policy scopes over, so it comes *first* in the lifecycle: an action schema is
**required** before you declare a service schema and before you write any policy.

This is a *modeling* task. The syntax is plain Cedar and fully documented (see
[Ground truth](#the-ground-truth-read-before-authoring)) — the hard part is
**deciding what your world looks like**: which entities are principals vs
resources, what counts as one action, and which fields belong under `input` vs
`output` vs `system`. You also choose *how* to produce the file: hand-write it,
or **generate it from an MCP `tools/list` manifest**.

Do **not** invent Cedar schema syntax from memory, and do **not** return a
schema you have not checked with the `dogwood` CLI. Follow the loop below in
order:

1. **Decide the shape** — resolve the modeling questions, and pick hand-write vs
   MCP-generate ([Step 1](#step-1--decide-the-shape-do-this-first)).
2. **Author or generate** the `.cedarschema` ([Step 2](#step-2--author-or-generate-the-cedarschema)).
3. **Check it** — run `dogwood schema action` and fix until it exits `0`; this
   is **mandatory** ([Step 3](#step-3--check-the-schema-mandatory--never-skip)).
4. **Hand off** — present the schema and point at the next lifecycle skill
   ([Step 4](#step-4--output-and-hand-off)).

## The ground truth (read before authoring)

The action schema is standard Cedar `.cedarschema` — Dogwood adds **no** schema
syntax, only a *convention* for the `context` record. Treat these docs as
authoritative; do not guess. Paths are relative to this skill directory
(`.claude/skills/authoring-action-schema/`); the guide lives in the
`dogwood-docs` crate:

- `../../../dogwood-docs/guide/02-policy-language.md` — read the **"The action
  schema"** section: the `namespace`, `entity`/`type`/`action` declarations, the
  implicit `Action` segment (so `action "Read"` is named `Ns::Action::"Read"`),
  action group hierarchies (`in [...]`), and the **`context.input` /
  `context.output` convention** — what `input` vs `output` vs `system` mean and
  why the grouping matters. This is the 100% reference for a hand-written schema.
- `../../../dogwood-docs/guide/11-mcp-schema-generation.md` — the **MCP
  generation** path: the manifest format (a `tools/list` payload or array of
  tools with `inputSchema` / `outputSchema`), the JSON→Cedar type mapping
  (`integer`→`Long`, `string`→`String`, `boolean`→`Bool`, `number` +
  `format: decimal`→`decimal`), and the **Drupe template** the generator
  layers tools onto (principals, `Gateway` resource, `SystemContext`, and the
  `Mcp`/`CallTool` action hierarchy). Read this before generating.
- `../../../dogwood-docs/guide/12-cli.md` — the **CLI**: the `dogwood schema`
  group (`action`, `mcp`) and `validate`, their flags, `--format human|json`,
  and the exit-code contract (`0` ok, `1` usage/IO, `2` rejected). If a schema
  construct is not in these docs, it does not exist — do not use it.

## Step 1 — Decide the shape (do this first)

Before writing anything, resolve the modeling questions below. These are the
equivalent of policy disambiguation: a wrong answer here silently mis-shapes
every policy that scopes over the schema. If you can infer an answer from a
supplied MCP manifest or an obvious convention, state your assumption and
proceed; otherwise ask the user, tying each question to how it changes the
schema.

1. **Which entities are principals vs resources?** Principals are the *actors*
   (a user, an agent, an IAM entity); resources are what they act *on* (a
   gateway, a document, a tool endpoint). Declare each as an `entity`, with
   attributes it carries (`entity OAuthUser = { id: String }`) and optional
   `tags`. If the same noun could be either, ask — the choice fixes which scope
   slot (`principal` vs `resource`) a policy uses.
2. **What is one action?** Model **one action per tool or operation** the
   deployment exposes (`Login`, `Read`, `SellShares`). If two operations differ
   only in arguments, they are still two actions. Resist collapsing distinct
   tools into one.
3. **Each action's scope.** For every action, which principal type(s) may
   perform it (`principal: [OAuthUser]`) and which resource type(s) does it act
   on (`resource: [Gateway]`)? Does it belong in a **group hierarchy**
   (`action "Login" in [Action::"CallTool"]`) — the shape the MCP generator
   produces and the corpus uses? Getting `appliesTo` wrong makes a valid policy
   fail to type-check.
4. **`context`: what goes in `input` vs `output` vs `system`?** This is the
   highest-value decision. Follow the convention exactly:
   - **`input: <Record>`** — the tool's **arguments** (read in a policy as
     `context.input.<field>`). Name and type every field.
   - **`output?: <Record>`** — the tool's **result** (`context.output.<field>`);
     usually optional (`output?`) because it exists only after the action
     resolves.
   - **`system: SystemContext`** — the base context every action carries
     (`{ now: datetime }`; read as `context.system.now`).

   Put arguments under `input`, results under `output`. The grouping is not
   decorative: it lets an action whose input and output both have a field `x`
   keep them as two distinct leaves (`input.x`, `output.x`). Use Cedar **common
   types** (`type ReadInput = { … };`) so each action references a named record.
5. **Hand-write or generate from MCP?** If the deployment already has an MCP
   server (or you have its `tools/list` JSON), **generate** — it is faster,
   applies the JSON→Cedar mapping for you, and layers tools onto the proven
   Drupe template (principals, `Gateway`, `SystemContext`, `CallTool`
   hierarchy). Hand-write when there is no manifest, when you need custom entity
   types/attributes/tags the template does not have, or for a small bespoke set
   of actions. Either way the output is a `.cedarschema` that goes through the
   same Step 3 gate.

## Step 2 — Author or generate the `.cedarschema`

### 2a. Generate from an MCP manifest (preferred when you have one)

Save the manifest (an MCP `tools/list` payload, or a JSON array of tools with
`inputSchema` / `outputSchema`) to `tools.json`, then run:

```bash
dogwood schema mcp --manifest tools.json -o schema.cedarschema
```

This layers **one Cedar action per tool** onto the Drupe template, deriving
each action's `context.input` from the tool's `inputSchema.properties` and
`context.output` from its `outputSchema`, and placing tool actions
`in [Action::"CallTool"]`. `-o` writes the file (omit it to write stdout). See
the MCP doc for the exact manifest format and type mapping. After generating,
**read the result** — confirm the actions, their `appliesTo` principals/
resource, and the `input`/`output` records match your intent — then go straight
to the Step 3 gate.

### 2b. Hand-write the schema

Follow the "action schema" section of the policy-language doc. Declare the
`namespace`, the principal/resource `entity` types, the common `type` records
for each action's input/output, and one `action … appliesTo { principal,
resource, context }` per operation. A minimal, correct shape (two tools sharing
a base context):

```text
namespace Drupe {
  type LoginInput  = { user: String };
  type ReadInput   = { document: String, user: String };
  type ReadOutput  = { };
  type SystemContext = { now: datetime };

  entity Gateway;
  entity OAuthUser = { id: String };

  action "Login" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: LoginInput, system: SystemContext }
  };

  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput, output?: ReadOutput, system: SystemContext }
  };
}
```

Match the corpus style in the guide. Keep `input` argument-only, `output?`
result-only and optional, and `system` for the base `{ now: datetime }`.

## Step 3 — Check the schema (MANDATORY — never skip)

**Every action schema MUST be checked before you present it. Do not return a
schema you have not run through the CLI** — an unchecked schema is a guess, and a
schema that does not resolve its own entity/action/type references will make
every downstream policy fail in confusing ways. This is a hard gate.

### The gate: `dogwood schema action`

The `dogwood` CLI checks the schema in isolation — that it parses and every
type/entity/action reference resolves — with no policy or service schema needed:

```bash
dogwood schema action schema.cedarschema
```

- **Exit code `0`** with `OK: action schema is valid.` → the schema is
  well-formed. Proceed.
- **Exit code `2`** → the schema was rejected. The command prints each finding
  as an underlined source snippet (e.g. `failed to resolve types: Nope` when an
  `appliesTo` names an undeclared entity). Read it, fix, and re-run. Add
  `--format json` for structured findings instead of rendered snippets.
- **Exit code `1`** → a usage/IO problem (missing file, bad flag), not a schema
  defect — fix the invocation.

Iterate until `dogwood schema action` exits `0`. Only then proceed.

### Fuller check (recommended): validate a probe policy

`schema action` proves the schema is *well-formed*; it does not prove your
`context.input` paths are what a policy will actually read. To confirm that,
write a one-line probe policy that names a generated/authored action and touches
an `input` field, and run `validate`:

```bash
dogwood validate probe.dw --policy-schema schema.cedarschema
```

with, for example:

```text
permit ( principal, action == Drupe::Action::"GetStockInfo", resource )
when { context.input.stock == "AMZN" };
```

A `0` exit proves the action name resolves and `context.input.stock` type-checks
against the scoped action; a `2` with `attribute input.<x> … not found` means the
field differs from what you assumed — fix the schema (or probe) and re-run. This
catches the mismatches `schema action` alone cannot.

### If you genuinely cannot run the CLI

If `dogwood` is not available (no built binary, no workspace), you MUST NOT
silently present the schema as correct. Instead:
1. State clearly that the schema was **not** checked in this environment.
2. Manually verify against the docs: every `appliesTo` entity type and action
   group parent is declared; every common `type` a `context` references exists;
   `input`/`output`/`system` follow the convention; the implicit `Action` naming
   is respected.
3. Give the user the exact `dogwood schema action schema.cedarschema` (and the
   probe-policy `dogwood validate`) command so they can run the gate themselves.

Treat "cannot check here" as a degraded path to flag loudly — not the norm.

## Step 4 — Output and hand-off

Only after the gate passes (or the degraded path is explicitly flagged), present
the result. Return, in this order:

1. A one-line restatement of the world you modeled — which entities are
   principals vs resources, and the list of actions.
2. Any assumptions you made (principal/resource split, group hierarchy, optional
   `output`, whether you generated from MCP or hand-wrote) — called out
   explicitly.
3. **Check status** — state plainly that `dogwood schema action` exited `0`, and
   whether you also ran the probe-policy `validate`.
4. The `.cedarschema` file itself.
5. A short gloss of each action's scope and `context` layout.

Then point the user at the rest of the lifecycle:

> Once the `.cedarschema` validates, declare any custom **event kinds or
> information providers** with **authoring-service-schema** (only if you need a
> non-default service schema), then write policies against this schema with
> **autoformalize-policies**.

Keep the schema minimal and idiomatic — match the corpus examples in the guide.
Do not add entities or actions the deployment does not have.
