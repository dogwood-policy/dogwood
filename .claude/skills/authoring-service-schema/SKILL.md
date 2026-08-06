---
name: authoring-service-schema
description: "Author or edit a Dogwood SERVICE schema — the event schema (.dwschema: event kinds, decision vs history points, renamed/reserved fields, nested records, correlation pins) and/or information providers (providers.json + the Rhai `evaluate` implementation behind a computed guardrail fact). Use when a policy needs a non-default event model (a history-only event kind, a renamed principal field, a pin/correlation invariant) or a computed fact from a provider/guardrail. The service schema is OPTIONAL and defaults sensibly (default = request/response/error kinds with only `request` deciding, a universal principal pin giving key-local semantics, a 24h `max_window` cap, no providers, and a small standard macro library), so this also covers deciding whether one is even needed. Requires a Cedar action schema first — that is authoring-action-schema. NOT for the Cedar action schema itself (entities/actions/context) — that is authoring-action-schema. NOT for writing `.dw` policies — that is autoformalize-policies."
---

# Authoring a Dogwood service schema (events + providers)

Your job: produce the **service-schema half** of a Dogwood schema — an **event
schema** (`.dwschema`) and/or an **information-provider declarations** file
(`providers.json` plus its Rhai implementation) — that parses, is well-formed,
and lets the policies you care about validate against a concrete action schema.

The service schema is **entirely optional and defaults sensibly**. The default
event schema declares three kinds — `request` (the only decision kind),
`response`, and `error` (both history-only) — each carrying the action's inputs
(`response` also its outputs) plus the reserved leaves `callerPrincipal` /
`callerResource` / `requestId` / `sessionId`. Crucially, `callerPrincipal` is a
**universal symmetric pin** (`pin callerPrincipal: principalType(A) =
principal` on every kind), so the default runs under **key-local semantics**:
every temporal predicate is silently correlated to the current request's
principal, and other principals' events are invisible to it. The default
look-back cap is `max_window = 24h`, the default provider set is **empty**, and
the default macro library is the small standard one (`count_within`,
`sum_within`, `count_distinct_within`, `bind`). So the most important decision
is Step 0: *do you even need one?* If not, the best service schema is no
service schema — omit it and Dogwood uses the default.

This skill has two cores — **events** and **providers** — plus **macros** as a
related seam (Step 3, briefly; the guide owns it). Do **not** invent DSL or JSON
from memory: the guide is exhaustive and every construct is corpus-verified.
Follow the steps in order.

## Step 0 — Decide whether you need a service schema at all (do this first)

Write a custom **event schema** only if the application's event model diverges
from the default request/response/error model in one of these ways:

- **A history-only event kind the default lacks** — an `audit`/`outcome` kind, or
  renaming the set (`attempt`/`outcome` instead of `request`/`response`). The
  default already gives `request` (decision) + `response` + `error` (history);
  customize only to go *beyond* that.
- **A different decision point** — some kind other than `request` must run
  authorization (mark it `decision`).
- **A renamed or extra reserved/principal field** — the injected principal is
  `actor` not `callerPrincipal`, or an extra `__session_id`.
- **Nested record fields** — hierarchical fields like `__platform.session.id`.
- **A different pin / correlation invariant** — the default already pins
  `callerPrincipal` on every kind (key-local, per-principal semantics). Write a
  custom schema to pin a *different* key (a session id), to add an extra pin,
  or — going the other way — to get **global-trace semantics** (a policy about
  *any* principal's events, e.g. "N logins by any user"), which requires a
  schema *without* the universal principal pin (the shipped
  `configuration/event-schemas/unpinned.dwschema` is exactly that).
- **A longer look-back than 24h** — every temporal window is capped by the
  event schema's `max_window` directive, **24h when absent**, so a policy with
  `within 7d` is a validation error under the default. Raising the cap is an
  event-schema change: copy the default schema and add `max_window = <interval>`
  (e.g. `max_window = 30d`) at the top of the file. **A `.dwschema` containing
  only the directive declares zero events** — it passes the isolated
  `schema event` check but every policy predicate then fails the composite
  `validate` (`does not name a declared event`) — so always carry the event
  declarations along with the directive.

Write **providers** (`providers.json`) only if a policy needs a **computed fact**
not in the request — a regex match, denylist check, risk/content score, allowlist
lookup — i.e. the `Provider::Name(args)` / `guardrails { }` path. Write a **macro
library** only for a genuinely reusable policy fragment (Step 3).

If **none** of these apply, **skip the service schema entirely** — do not write
an empty `.dwschema` (an explicitly-supplied blank event schema declares zero
events and is *rejected* at build time; only *omitting* it falls back to the
default). Say so and stop.

## The ground truth (read before authoring)

The event-schema DSL and the provider declaration format are precisely
documented, including their legality rules. Treat these as authoritative. Paths
are relative to this skill directory
(`.claude/skills/authoring-service-schema/`); the guide lives in the
`dogwood-docs` crate:

- `../../../dogwood-docs/guide/03-event-schema.md` — the **event-schema DSL**:
  the `[decision] event <A>::kind { … }` shape, the four selectors (`inputs`,
  `outputs`, `principalType`, `resourceType`), spreads vs field-types, nested
  records, **pins** (`pin name: type = <request-reference>`), decision vs
  history kinds, the **`max_window` directive** (the look-back cap), the
  default schema, and worked corpus examples (1110–1122). Read in full
  before writing any `.dwschema`.
- `../../../dogwood-docs/guide/10-provider-schema.md` — **declaring** a provider:
  the `providers.json` format (`availableProviders`, `argumentTypes`,
  `outputType`, `implementation`), the `ParamType` → Cedar-type table, the
  **Rhai `evaluate` contract**, the sandbox (deterministic, no I/O, registered
  host functions, decimal support, off-by-default `net`), and the
  **`from_json` / `scriptFile` gotcha** (see Step 2). Read in full before writing
  `providers.json`.
- `../../../dogwood-docs/guide/05-information-providers.md` — the **calling**
  contract from a policy's side (`Ns::Fn(args).field <cmp> …`, argument kinds,
  projection; any action scope works): what a policy author writes against your
  declaration.
- `../../../dogwood-docs/guide/12-cli.md` — the `dogwood` CLI, the two schema
  halves, and the exact commands + exit codes used in Step 4.
- `../../../dogwood-docs/guide/06-macros.md` — **defining** macros (Step 3).

If a construct is not in these docs, it does not exist — do not use it.

## Prerequisite: a Cedar action schema must already exist

**REQUIRED.** A service schema is meaningless on its own: the event schema
*derives* per-action event signatures from the action schema, and each provider
call hoists a typed field into every action's context. The action schema
(`.cedarschema`) declares the entities, actions, and each action's
`context.input` / `context.output` — and that `context.input`/`output` is exactly
what an event schema's `...inputs(A)` / `...outputs(A)` spreads read. If you do
not have one yet, produce it first — that is **authoring-action-schema**. This
skill takes the action schema as given.

## Step 1 — Write the event schema (`.dwschema`) — only if Step 0 said so

The DSL is generic and schema-independent: `<A>` is a binder meaning "any
action", and every selector inside the body must reference that exact binder. A
declaration is `[decision] event <A>::kind { field, … }`. Build it from the
selectors and field forms documented in guide 03 — the full rules for spreads,
selector-as-type, nested records, and pins live there; do not restate them from
memory. A verified shape (author-defined kinds + a renamed principal field, from
corpus case 1110):

```text
decision event <A>::attempt {
    ...inputs(A),
    actor: principalType(A),
}
event <A>::outcome {
    ...inputs(A),
    ...outputs(A),
    actor: principalType(A),
}
```

Watch the load-bearing rules from guide 03: the `decision` prefix is what makes
authorization run (default is only `request`); `inputs`/`outputs` are **spread**
(`...inputs(A)`) while `principalType`/`resourceType` are used as a **field
type**; a spread mints its own group even nested; field names are unique **at
every level**; and a **pin** needs both `pin` and a `= <request-ref>` value
(a scope reference `= principal` / `= resource`, or a context field
`= context.<path>`), may sit only on a leaf, and is injected onto *every*
predicate for that event (a hand-written field can only *narrow* a pin, never
relax it). Correlate against the current request with `principal` / `resource`
(the scope entities) / `context.<path>` (a context field) — note `principal`
is the bare scope reference, **not** `context.principal` (which would be a
context field literally named `principal`). A pin declared identically on
**every** kind with a symmetric path (`pin f = context.f`, or the reserved
`callerPrincipal = principal` / `callerResource = resource`) additionally
switches temporal evaluation to
**key-local semantics** (`previous` / `since` range over the key's own
events) and guarantees verdicts depend only on that key's events — safe to
partition storage per key, but cross-key policies ("N logins by *any*
user") become inexpressible; see the event-schema doc's "Universal
symmetric pins" section before adopting one.

## Step 2 — Write the information providers (`providers.json` + Rhai) — only if Step 0 said so

Declare each provider under `availableProviders` keyed by its fully-qualified
name (`Ns::Fn` — the same name a policy invokes). Each declaration has
`argumentTypes` (ordered positional `ParamType`s), a required `outputType`, and
an optional `implementation`. The `ParamType` → Cedar-type mapping and the record
`fields`/`required`/set `items` shapes are tabulated in guide 10. A verified
declaration (`Strings::Matches`, corpus case 0001):

```json
{
  "availableProviders": {
    "Strings::Matches": {
      "argumentTypes": [ { "paramType": "string" }, { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "matched": { "paramType": "bool" } },
        "required": ["matched"]
      },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(text, pattern) { if type_of(text) == \"()\" || type_of(pattern) == \"()\" { return #{ matched: false }; } #{ matched: regex_is_match(pattern, text) } }"
      }
    }
  }
}
```

The Rhai implementation must define `fn evaluate(arg0, …)` whose parameters match
the declared `argumentTypes` **positionally** (not any host function's order) and
return a value matching `outputType` — typically an object map `#{ … }`. Scripts
MUST be defensive: providers execute unconditionally (for every decision event),
so any argument may arrive absent as Rhai unit `()` — guard with
`type_of(x) == "()"` and return a type-conforming sentinel, as the template
above does (an erroring provider is undefined behavior). It runs
in a **locked-down sandbox**: deterministic, no file/network/process access, only
the host functions Dogwood registers (the three `regex_*` always; `http_get` only
under the off-by-default `net` feature), `parse_decimal("…")` for decimals, plus
pure Rhai. See guide 10 for the full contract and the decimal/nested shapes.

**The `scriptFile` / inline-`script` gotcha (this bites the CLI path).** An
`implementation` carries its Rhai two ways: inline **`script`** (source as a JSON
string) or **`scriptFile`** (a path to an external `.rhai`, resolved relative to
`providers.json`). A `scriptFile` reference is only folded in when the file is
loaded via `from_json_file`; loaded as text via `from_json` it stays unresolved.
**The `dogwood` CLI reads `providers.json` as text** — so when you gate with the
`--providers` flag (Step 4) or `dogwood replay`, a `scriptFile`-only provider is
**never resolved** and evaluation fails. When you validate/replay through the
CLI, put the Rhai **inline under `implementation.script`** (the corpus keeps the
inline copy in sync with any external `.rhai` for exactly this reason). A
declaration may also **omit `implementation`** entirely — an interface-only
provider whose value your own code supplies; it validates and lowers, but cannot
be *evaluated* by the CLI (`replay` errors "has no implementation"). This is
also documented in the CLI chapter (guide 12, under `validate`).

## Step 3 — Macros (the related seam)

A macro library (`def cedar` / `def temporal`, passed with `--macros`) is the
*third* optional service-side input, for a genuinely reusable policy fragment. It
is out of scope here — if you need one, see
`../../../dogwood-docs/guide/06-macros.md` (defining) and
`../../../dogwood-docs/guide/09-calling-macros.md` (calling).

## Step 4 — Validate (MANDATORY — never skip)

**Every service-schema artifact you write MUST be validated before you present
it.** An unvalidated `.dwschema` or `providers.json` is a guess. Validate with
the **`dogwood` CLI** (build it with `cargo build -p amzn-dogwood-cli`; if it is
not on your `PATH`, invoke the binary from the Cargo target directory). Exit codes are
uniform across all commands: **`0`** = valid, **`1`** = usage/IO error (missing
file, bad flag — fix the invocation), **`2`** = the artifact was rejected (read
the rendered snippet, fix, re-run). Add `--format json` for structured findings.

**First, check each part in isolation** — this separates "my schema is broken"
from "my policy is broken":

```bash
dogwood schema event     events.dwschema     # exit 0 = well-formed event schema
dogwood schema providers providers.json      # exit 0 = well-formed provider decls
```

**Then run the composite `validate`** — this is the gate that actually matters,
because it **derives** the event signatures against the action schema and
**type-checks provider calls**, which the isolated checks cannot:

```bash
dogwood validate policy.dw \
    --policy-schema schema.cedarschema \
    --event-schema events.dwschema \
    --providers providers.json
```

Pass only the service-side flags you actually authored (each is optional and
defaults). Exit `0` with `OK: validation passed` means the whole bundle — action
schema, derived events, provider calls, and the policy — checks out together.
Iterate until it exits `0`.

Note: `dogwood check-parse policy.dw` (no schema) is a fast syntax pass that
**flags any provider a policy calls that your declarations do not declare**
(`warning: undeclared provider Ns::Fn`) — a quick way to confirm `providers.json`
covers every call. For a temporal event schema, also consider `dogwood replay …
--trace trace.log` to confirm decision-vs-history kinds and pins behave as
intended (guide 12).

### If you genuinely cannot run the CLI

If `dogwood` is unavailable, you MUST NOT present the schema as correct. Instead:
(1) state plainly it was **not** validated here; (2) do a rigorous manual check
against guides 03 and 10 — every selector references the `<A>` binder, a reachable
`decision` kind exists, pins are leaf-only with both `pin` and a `= <request-reference>`
value, field names unique at every level, provider `argumentTypes`/`outputType`
well-formed, and Rhai is **inline under `script`** (not `scriptFile`); and (3)
give the user the exact `dogwood validate` command above to gate it themselves.
Treat "cannot validate here" as a degraded path to flag loudly — not the norm.

## Step 5 — Output

Only after the composite `dogwood validate` exits `0` (or the degraded path is
explicitly flagged), present the result. Return, in this order:

1. **Whether a service schema was even needed** — if Step 0 ruled it out, say so
   and stop; otherwise which halves you wrote and why (which Step 0 trigger).
2. **Validation status** — state plainly that `dogwood validate` exited `0`
   (action schema + derived events + provider calls all check out), or why it
   could not be validated here.
3. The artifact(s) — the `.dwschema` and/or `providers.json` (with inline Rhai),
   each with a leading comment explaining intent.
4. A short gloss: which kind is the decision point, what each pin correlates, and
   what each provider computes and returns.

Keep artifacts minimal and idiomatic — match the corpus examples the guide cites.
Do not add event kinds, fields, pins, or providers no policy needs.
