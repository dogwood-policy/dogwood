---
name: autoformalize-policies
description: "Autoformalize a natural-language authorization requirement into a validated Dogwood (.dw) policy. Use when a user describes access rules in prose (\"only allow X if Y\", \"deny after Z\", \"no more than N per hour\") and wants a compilable Dogwood policy. Disambiguates intent before formalizing, and always validates the generated policy with the `dogwood` CLI before returning it. This skill CREATES a policy from prose; it is not for running the `dogwood` CLI / validator on an existing `.dw` file (validation here is an internal step, not a standalone command — for CLI usage see the guide's command-line chapter)."
---

# Autoformalizing natural language into Dogwood policies

Your job: turn a natural-language authorization requirement into a **Dogwood
`.dw` policy** that parses, validates against a schema, and means what the user
actually intended. This is a *formalization* task — the hard part is not the
syntax (that is fully documented; see [Ground truth](#the-ground-truth-read-before-authoring))
but **pinning down ambiguous intent** and mapping it onto the right Dogwood
construct.

Do **not** guess at intent when a requirement is underspecified, and do **not**
return a policy you have not validated. Follow the loop below in order:

1. **Disambiguate** the requirement (resolve every gap that changes the output).
2. **Formalize** it into a `.dw` policy.
3. **Validate** it — run it through the `dogwood` CLI and fix until it is clean.
   This step is **mandatory** (see
   [Step 3](#step-3--validate-the-policy-mandatory--never-skip)); a policy that
   has not been validated is not a finished answer.
4. **Round-trip** the intent and present the result.

## The ground truth (read before authoring)

Dogwood's syntax and, crucially, its *legality rules* are precisely documented.
Treat these as authoritative; do not invent syntax from memory. These paths are
relative to this skill directory (`.claude/skills/autoformalize-policies/`); the
guide lives in the `dogwood-docs` crate:

- `../../../dogwood-docs/guide/02-policy-language.md` — core
  policy syntax: `permit`/`forbid`, the `(principal, action, resource)` scope,
  `when`/`unless`, and the complete Cedar expression language (operators,
  literals, methods, `has`/`like`/`is`, sets/records, entity refs). **100% of
  the core syntax.**
- `../../../dogwood-docs/guide/04-temporal-expressions.md` — the
  `temporal { … }` sublanguage: `formerly`/`previous`/`since`, windows,
  `exists`/`tp`, `count`/`sum`, predicates, and the **acceptance rules** (range
  restriction, conjunct ordering, tp-dependence). Read this in full before
  writing any history-dependent policy.
- `../../../dogwood-docs/guide/02-policy-language.md` (the
  "action schema" section) — the action schema and the
  `context.input`/`context.output` convention.
- `../../../dogwood-docs/guide/03-event-schema.md` — the
  event-schema DSL and decision vs history event kinds (needed only when
  customizing the default).
- `../../../dogwood-docs/guide/05-information-providers.md` —
  computed facts via `Provider::Name(args)` calls in an ordinary `when { … }`;
  see `../../../dogwood-docs/guide/10-provider-schema.md` for
  declaring providers (`providers.json`, the Rhai contract).
- `../../../dogwood-docs/guide/09-calling-macros.md` — calling
  macros; and `../../../dogwood-docs/guide/06-macros.md` —
  defining `def cedar` / `def temporal` (rarely needed; reach for it only for a
  genuinely reusable pattern).

If a construct is not in these docs, it does not exist — do not use it.

## Step 1 — Disambiguate intent (do this first)

A prose requirement almost always leaves gaps that change the formal policy.
Before writing anything, **resolve every gap that affects the output**. If you
can infer the answer from a supplied schema or an obvious convention, state your
assumption and proceed; otherwise ask the user. Prefer asking a few sharp,
batched questions over silently guessing.

Work through this checklist:

1. **Effect and default.** Is this granting access (`permit`) or restricting it
   (`forbid`)? Remember Dogwood is **default-deny with deny-overrides**: a
   `forbid` always wins. "Users may X" → a `permit`. "Never allow X" / "block X
   when Y" → a `forbid` that carves a hole out of the permits. If the user
   describes an exception to an existing allow, that is a `forbid`, not a
   narrower `permit`.
2. **Scope: which principal / action / resource?** Which action(s) does this
   govern (`action == Ns::Action::"X"`, or `action in [ … ]`, or any action)?
   Is the principal any user, a specific entity, a type (`principal is
   OAuthUser`), or a group member (`… in Group`)? Same for resource. Map the
   user's nouns to concrete schema entities/actions — **ask for the schema if
   you do not have it** (you cannot validate entity/action/field names without
   it).
3. **Condition data: where does each fact live?** For every fact the rule
   depends on, decide its source:
   - An attribute of the **principal / resource entity** → `principal.<attr>` /
     `resource.<attr>` (e.g. `principal.dept`), or the bare `principal` /
     `resource` for an identity comparison. These are the request scope
     entities — the *same* names, and the same meaning, in a core `when { … }`
     clause and inside `temporal { … }`. Do **not** write `context.principal`:
     as in Cedar, `context` is a separate record, so `context.principal` is a
     field literally named `principal` in the context record, **not** the scope
     entity.
   - A field of *this* request's **context** → `context.input.<field>` (or
     `context.output.<field>`, `context.system.now`). Confirm the field name and
     type against the schema.
   - A *computed* fact (regex match, denylist, risk score, content safety) →
     an **information provider** (`when guardrails { … }` /
     `Provider::Name(args)`). Any action scope works; providers are
     evaluated unconditionally, so their scripts must be pure and defensive
     (see the provider contract in the providers doc).
   - A fact about the **past** (something happened / did not happen / how many
     times) → the **temporal** sublanguage (Step 2b).
4. **Temporal specifics** (if history is involved) — these are the highest-value
   disambiguations, because the wrong choice silently changes meaning:
   - **"happened at least once recently"** → `formerly within W`.
   - **"the immediately preceding event"** → `previous within W` (strict: only
     `i-1`, false at the first event). Under an event schema with a
     **universal symmetric pin** — which includes the **default** schema,
     whose every kind pins `callerPrincipal` to the request principal —
     `previous` means the *key's own* previous event, and the positive left of
     `since` ranges over the key's own positions only — other keys' interleaved
     events neither satisfy nor break these operators (see the event-schema
     doc's "Universal symmetric pins" section).
   - **"has held continuously since an anchor"** → `left since within W right`.
   - **"has NOT happened since"** → `!left since within W right` (there is no
     dedicated operator).
   - **What is the window `W`?** Every temporal operator needs a mandatory
     `within <amount><unit>` (`s`/`m`/`h`/`d` only; no week/month/year). If the
     user says "recently" without a number, **ask** — the window is not optional
     and there is no default. Windows are also **capped** by the event schema's
     `max_window` (**24h when absent**): a `within 7d` under the default schema
     is a validation error. If the requirement genuinely needs a longer
     look-back, that is an event-schema change (`max_window = 30d` at the top
     of a `.dwschema` that also declares the events) — route it to
     **authoring-service-schema**, don't shrink the user's window silently.
   - **"the same X"** (same user, same document) → *pin* the past predicate's
     field to the current request: `input.user: context.input.user`. Decide
     which fields correlate. Note the **default** event schema already
     correlates every temporal predicate to the current request's
     **principal** (its universal `callerPrincipal` pin — key-local
     semantics), so "the same user" is enforced automatically when "user" =
     the principal; you still correlate explicitly for anything else (same
     document, same session, an `input` field distinct from the principal).
     Under an **unpinned** (global-trace) schema nothing is automatic, and a
     missing correlation silently turns "the same user" into "any user".
     Conversely, a "by *any* user" requirement cannot be met under the pinned
     default at all — it needs the unpinned schema (see
     **authoring-service-schema**).
   - **Counting/summing** → `count`/`sum` (no `min`/`max`/`avg`). For counts,
     decide **occurrences vs distinct values**: per-timepoint occurrences need a
     `tp` var in the `for` domain; distinct values omit it. Confirm the
     threshold and its operator (`> n`, `== n`, `<= n`).
5. **Combining conditions.** Multiple independent conditions that must *all*
   hold → separate `when` clauses (or `&&`). An exception → `unless`. **"A or
   B" across outcomes → two separate rules** (the temporal sublanguage has no
   `||` at all; even in core Cedar, splitting rules is often clearer).
6. **Edge cases the prose glosses over.** What if an optional field is absent
   (`has` guard + `if/then/else`)? Is the boundary inclusive (windows are
   closed/inclusive; `<=` vs `<`)? First-event behavior for `previous`? Surface
   these and pick a defensible default, stating it.

When you ask, ask concretely and tie each question to how it changes the
policy — e.g. *"'recent' — within what window (e.g. `1h`)? And must it be the
**same** document the user read, or any document?"* — not a vague "can you
clarify?".

## Step 2 — Formalize

### 2a. Core (single-request) policies

Map the disambiguated intent onto the five-part rule shape (annotation, effect,
scope, `when`/`unless` clauses, `;`). Lead each rule with a `//` doc comment in
the user's words and an `@id("…")`. Keep the scope as the coarse filter and put
fine logic in `when`/`unless`. Example — "only permit selling under 100 shares
of anything but AMZN":

```text
// Permit small share sales, but never for AMZN.
@id("sell_small_non_amzn")
permit ( principal, action == Drupe::Action::"SellShares", resource )
when   { context.input.shares < 100 }
unless { context.input.stock == "AMZN" };
```

Use the exact operator/method vocabulary from the core-language doc. Watch the
type rules it calls out: **decimals are equality-only** (use `.lessThan(…)`
etc. for ordering), and `/` and `%` are unsupported (only `+`, `-`, `*`). There
is also no `let … in` binding form (in core Cedar or in Dogwood). `!=` is
available both in core Cedar and inside `temporal { … }`.

### 2b. History-dependent policies (`temporal { … }`)

When the requirement is about the past, attach a `when temporal { … }` (or
`unless temporal { … }` for absence) and build the body from predicates and the
three operators. The canonical write-after-read shape:

```text
// Permit a Write only if this user read the same document within the last hour.
@id("write_after_read")
permit ( principal, action == Drupe::Action::"Write", resource )
when temporal {
    formerly within 1h Drupe::Action::"Read"::request{
        input.user: context.input.user,
        input.document: context.input.document
    }
};
```

Absence ("no logout since login" = an open session) is `unless`-of-a-`formerly`
or a negated `since` left; counting a threshold uses the
`exists (n: Long). ((count …) == n && n > k)` shape. **Follow the acceptance
rules in the temporal doc's "Writing temporal expressions that are accepted"
section exactly** — close the condition (bind every variable with an `exists`
or a `for` list; use `*` for "any value"), range-restrict every `exists` var
and every aggregation `for` var with a positive atom (a negated occurrence or
a since-left occurrence restricts nothing), order conjuncts so producers
precede consumers (a filter, a correlated aggregate behind a binding equality,
and a since-left all consume — their variables must be restricted by a
preceding conjunct), keep aggregates as comparison operands, and ensure every
scope is tp-dependent. These are the most common reasons a plausible-looking
temporal policy is *rejected*.

### 2c. Computed facts (`guardrails` / providers)

If a fact must be computed, use a declared provider (any action scope). See
the providers doc for the call shape, the `providers.json` declaration, and
the provider contract (unconditional evaluation; pure, defensive scripts).

## Step 3 — Validate the policy (MANDATORY — never skip)

**Every generated policy MUST be validated before you present it. Do not return
a policy you have not validated** — an unvalidated policy is a guess, and this
language has enough legality rules (especially in the temporal sublanguage) that
plausible-looking policies are routinely *rejected*. Validation is a hard gate,
not a nice-to-have.

Validate with the **`dogwood` CLI**, which runs the full pipeline — parse, macro
expansion, lowering, and schema-aware type-checking — and reports every finding.
You do not need to write any Rust.

### How to validate (preferred: actually run it)

Save the policy to a `.dw` file and the action schema to a `.cedarschema` file,
then run:

```bash
dogwood validate policy.dw --policy-schema schema.cedarschema
```

- **Exit code `0`** with `OK: validation passed` → the policy parsed, lowered,
  and type-checked cleanly. Proceed.
- **Exit code `2`** → the policy was rejected. The command prints each finding
  as an underlined source snippet pointing at the offending `.dw` span. Read it,
  fix, and re-run. Add `--format json` if you want the findings as structured
  data (each with a `message` and a byte-offset `labels` span) instead of
  rendered snippets.
- **Exit code `1`** → a usage/IO problem (missing file, bad flag), not a policy
  defect — fix the invocation.

`dogwood validate` covers **both** error classes in one run, so a `0` exit means
the policy is fully accepted:

1. **Parse + lowering.** Syntax, macro-expansion, and lowering failures — e.g. a
   temporal leaf that violates range-restriction or conjunct-order rules is
   rejected here.
2. **Schema-aware validation.** Type errors and dialect-check failures against
   the schema — an unknown entity type / action, a `context.input.<field>` that
   does not resolve in the scoped action, an operand that does not typecheck.

Iterate — fix and re-run — until `dogwood validate` exits `0`. Only then proceed
to output.

Common rejection causes and where they surface:

- **Parse/lowering (temporal):** an `exists` variable with no positive
  restrictor; a filter conjunct placed before its restrictor; an aggregate used
  outside a comparison operand; a missing `within` window.
- **Schema-aware:** an unknown entity type or action; a `context.input.<field>`
  that does not resolve in the scoped action; a `within` window exceeding the
  event schema's `max_window` cap (**24h** under the default schema — raising
  it is an event-schema change, see **authoring-service-schema**); an ordering
  comparison on a non-numeric operand; a decimal ordered with `<` instead of
  `.lessThan(…)`.

### Custom event schema, providers, or macros

If the policy uses a non-default event schema, information providers, or a macro
library, pass them too — each is optional and defaults sensibly when omitted:

```bash
dogwood validate policy.dw \
    --policy-schema schema.cedarschema \
    --event-schema events.dwschema \
    --providers providers.json \
    --macros lib.dw
```

You can also check a schema part on its own before validating the policy —
`dogwood schema action schema.cedarschema`, `dogwood schema event
events.dwschema`, or `dogwood schema providers providers.json` — to separate
"my schema is broken" from "my policy is broken".

### Sanity-check behavior with a trace (recommended for temporal policies)

For a history-dependent policy, validation proves it is *legal*, not that it
*means what you intended*. Write a short `.log` event trace and replay it to see
the actual verdict stream:

```bash
dogwood replay policy.dw --policy-schema schema.cedarschema --trace events.log
```

Each decision point prints `@<ts> (time point <i>): ALLOW|DENY`. Confirm that a
case which *should* allow does, and one that *should* deny does — this catches a
mis-pinned correlation ("same document" that is really "any document") or a wrong
window that validation alone cannot. Use `--format json` for a structured verdict
stream.

### If you genuinely cannot run the CLI

If `dogwood` is not available in the environment (no built binary, no
workspace), you MUST NOT silently present the policy as correct. Instead:
1. State clearly that the policy was **not** validated in this environment.
2. Do a rigorous manual check against the docs anyway: every name resolves
   against the schema; every temporal legality rule holds (closedness, range
   restriction — for `exists` and `for` variables alike — conjunct order,
   aggregate-as-operand, tp-dependence, mandatory windows); the
   intent round-trips to English.
3. Give the user the exact `dogwood validate` command above (with their schema
   and policy filenames) so they can validate it themselves in one step.

Treat "cannot validate here" as a degraded path to flag loudly — not the norm.

## Step 4 — Intent round-trip and output

Only after validation passes (or the degraded path above is explicitly
flagged), do a final intent check and present the result.

**Intent round-trip:** re-read your policy back into English and confirm it
matches what the user asked — especially the effect (permit vs forbid), the
correlation pins ("same" vs "any"), the window, and inclusive boundaries.

Return, in this order:
1. A one-line restatement of the requirement as you understood it (so the user
   can catch a misread).
2. Any assumptions you made (windows, correlations, defaults) — called out
   explicitly.
3. **Validation status** — state plainly that `dogwood validate` exited `0`
   (the policy parsed, lowered, and type-checked), or that it could not be
   validated here and why (the degraded path).
4. The `.dw` policy, with a `//` doc comment and `@id`.
5. A short plain-English gloss of what each clause does, and any residual
   ambiguity you could not resolve.

Keep the policy minimal and idiomatic — match the style of the corpus examples
in the guide. Do not add clauses the user did not ask for.
