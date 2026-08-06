# Introduction to Dogwood

*This page explains what Dogwood is, the problem it solves, and the concepts the
rest of the guide assumes. It introduces no syntax, only the model.*

## What Dogwood is

Dogwood is a **policy language for authorization decisions** — deciding whether
a given actor may perform a given action on a given resource. If you have seen
[Cedar](https://www.cedarpolicy.com/), Dogwood will feel familiar: you write
`permit` and `forbid` rules over a *principal*, an *action*, and a *resource*,
and an authorizer answers **Allow** or **Deny**.

A Dogwood decision is not confined to what is known at a single point in
time. Two capabilities extend it:

- **Accumulated history.** *Temporal expressions* let a rule reason about the
  stream of past events — "permit this transfer only if the same user was
  approved within the last hour", "deny reads after a logout until the next
  login". The authorizer remembers what it has seen.
- **On-demand computed values.** *Information providers* let a rule consult a
  value produced on demand by a small sandboxed script — "permit only if this
  document id matches an allowed pattern", "deny if a risk score is elevated".

Everything else — the schema, the operators, the tooling — exists to support
writing, validating, and evaluating those rules safely.

## The problem it solves

Ordinary point-in-time authorization answers *"is this request allowed, in
isolation?"* That is not enough when the safe answer depends on **what happened
before** or on **a value computed during authorization**. Consider the
following guardrails around an AI agent's tool calls:

- *"Allow `SellShares` only if there was an `ApproveSale` for the same stock in
  the last hour."* — a decision about **history**.
- *"Allow `Read` only if the document id looks like a public identifier."* — a
  decision about a **computed** property of the request.
- *"Deny everything for a user after they log out, until they log in again."* —
  again, **history**.

You could enforce this logic manually in application code, but it would be
scattered, duplicated, and hard to reason about. Dogwood lets you express it
**declaratively, in one place**, as policy — and it handles the history-tracking
and value-computation for you.

## The five concepts

There are five core concepts that underpin everything in Dogwood (and this
documentation).

### 1. Policies

A **policy** is a `permit` or `forbid` rule. It has a *scope* (which principal,
action, and resource it applies to) and optional *conditions* (`when` / `unless`
clauses). The decision is **default-deny**: a request is allowed only if some
`permit` matches and no `forbid` overrides it. This is the
[Cedar](https://www.cedarpolicy.com/) model, and it is the subject of
[The Policy Language](02-policy-language.md).

### 2. Events

The authorizer evaluates **events**: a timestamped occurrence of an action,
carrying named input fields. Each event has a *kind*, conventionally `request`
for the invocation and `response` for the result, that determines its role in
authorization. For authorization decisions, the event also includes a principal
and a resource.

The *kind* matters: some kinds are **decision points** (they ask for a verdict —
conventionally `request`), and others are **history-only** (they record
something that happened — conventionally `response`). A history-only event
updates what the temporal expressions can see but produces no verdict. This is
why Dogwood's authorizer is **stateful**: you feed it events one at a time, and
each is remembered.

### 3. Schemas

A **schema** tells Dogwood about your world. Dogwood composes *three*
schemas plus a macro library into one:

- the **action schema** — your principals, resources, and actions (a Cedar
  `.cedarschema`);
- the **event schema** — which event *kinds* each action produces and what
  fields they carry (a small Dogwood DSL, with a sensible default);
- the **provider declarations** — the signatures and implementations of any
  information providers (JSON; empty by default);
- the **macro library** — reusable named fragments of Cedar or temporal
  conditions (Dogwood source; a built-in standard library by default).

You write the **action schema** to describe your application, and it
is the schema this introduction and the core language chapters assume — it is
covered as part of [The policy language](02-policy-language.md). The other three
have sensible defaults, so a plain policy needs only the action schema; the core
chapters take them as *given*. When you do need to customize them, the Advanced
topics cover each in depth: [The event schema](03-event-schema.md),
[The provider schema](10-provider-schema.md), and [Macros](06-macros.md).

### 4. Reaching beyond the current request

Inside a policy's conditions, two constructs unlock Dogwood's extra reach:

- **`when temporal { … }`** — a condition over event history. See
  [Temporal expressions](04-temporal-expressions.md).
- **an information-provider call in an ordinary `when { … }`** — a condition
  that consults a value computed on demand. A provider is invoked as a plain
  Cedar call (`Provider::Name(args)…`); no special clause is required. See
  [Information providers](05-information-providers.md).

Both are ordinary conditions from the policy's point of view; they evaluate
against history or a computed value instead of only the current request. (You
will also see **macros** — a way to name and reuse fragments of either; calling
them is covered in [Calling macros](09-calling-macros.md), and defining them in
[Macros](06-macros.md).)

### 5. The authorizer

The **authorizer** is what you build from your policies and then feed events to.
For each decision-kind event it returns a **Response**: the decision
(`Allow` / `Deny`) and diagnostics (which rules determined it, and any evaluation
errors). Evaluation is **fail-closed** at defined points — if evaluating the
event history or building the request context cannot complete, the decision is
`Deny` with the reason in diagnostics rather than risking a wrong `Allow`.
Information providers are the exception: the language leaves an erroring
provider *undefined*, and while this reference interpreter does deny, a policy
must not rely on that (see
[Information providers](05-information-providers.md)). Driving the authorizer
from Rust is the subject of
[The API and workflow](07-api-and-workflow.md).

## How it fits together

```text
        schema(s)                policy source (.dw)
            │                          │
            └───────────┬──────────────┘
                        ▼
                LoweredPolicySet      ← parsed + lowered (to Cedar, under the hood)
                        │
                        ▼
                   Authorizer         ← stateful; holds accumulated history
                        │
   events ────────────►│
   (one at a time)     ▼
                    Response          ← Allow / Deny + diagnostics
                  (per decision-kind event)
```

Under the hood, Dogwood **lowers policies to Cedar** and evaluates with the Cedar
engine — the temporal and provider clauses are compiled into extra context that
Cedar then sees. You do not need to know this to use Dogwood, but it is why the
API mirrors Cedar's.

## Where to go next

- **Want to run something immediately?** → [Getting started](01-getting-started.md)
  walks through your first authorization end to end.
- **Want the language reference?** → [The policy language](02-policy-language.md),
  then [Temporal expressions](04-temporal-expressions.md) and
  [Information providers](05-information-providers.md).
- **Customizing the fixed inputs?** → the Advanced topics:
  [The event schema](03-event-schema.md),
  [The provider schema](10-provider-schema.md), and
  [Macros](06-macros.md).
- **Integrating from Rust?** → [The API and workflow](07-api-and-workflow.md).

## See also

- [Getting started](01-getting-started.md) — your first policy and authorization.
- [The policy language](02-policy-language.md) — the core syntax.
