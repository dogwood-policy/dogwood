# Getting Started

*This page walks you through your first Dogwood authorization end to end — a
schema, a policy, and the Rust code that decides a request. It starts with the
simplest possible policy and then adds a decision that depends on history. The
two policies here are the `permit_read_anyone` and `read_after_login` example
bundles, checked on every build, so they do validate and replay as shown.*

If you have not read [the introduction](00-introduction.md), skim it first — it
explains the five concepts (policies, events, schemas, temporal expressions and
information providers, and the authorizer) this tutorial puts into practice.

## The shape of the workflow

Every use of Dogwood runs the same pipeline:

- **Build the two schema halves** — a `ServiceSchema` (macros, providers, and
  the event-schema DSL — the fixed, service-provided inputs) and a
  `PolicySchema` (your action schema).
- **Parse and lower a `LoweredPolicySet`** from your policy source, against
  those two schemas.
- **(Optionally) validate** the policy set with a `Validator`.
- **Build an `Authorizer`** and feed it **events**, getting a **`Response`** back.

The tutorial below writes the schema and policy first, then runs that whole
pipeline in Step 3.

## Step 1 — a schema

The schema declares the entity types and actions in your world. It is a standard
Cedar `.cedarschema`. Here is a minimal one for an agent that can `Login` and
`Read`, each taking a `user` input field:

```text
namespace Drupe {
  type LoginInput = { user: String };
  type ReadInput = { user: String };
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  action "Login" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: LoginInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
```

Two things to notice, both Dogwood conventions covered in
[The policy language](02-policy-language.md):

- Each action's parameters live under a **`context.input`** record
  (`context: { input: ReadInput }`). This is where a policy reads the request's
  fields from (`context.input.user`).
- We only wrote the **action schema**. Dogwood's other two schemas — the event
  schema and provider declarations — have sensible defaults, so a simple policy
  needs nothing more.

## Step 2 — a policy

A policy is a `permit` or `forbid` rule. The simplest useful one: *permit `Read`
for anyone, on any resource.*

```text
permit (
    principal,
    action == Drupe::Action::"Read",
    resource
);
```

> Runnable: [`examples/permit_read_anyone/`](../examples/permit_read_anyone/) —
> `dogwood validate` and `dogwood replay`.

- `permit` is the effect. (`forbid` is the other; a `forbid` always wins over a
  `permit`.)
- The parenthesized part is the **scope**: bare `principal` and `resource` mean
  "any", and `action == Drupe::Action::"Read"` restricts this rule to the
  `Read` action.
- No `when` clause means no extra condition — this rule applies whenever its
  scope matches.

The full policy syntax — scope constraints, `when`/`unless` conditions, the
whole expression language — is [The policy language](02-policy-language.md).

## Step 3 — decide, from Rust

Here is the whole pipeline in Rust. Build the schema, parse the policy, validate,
then authorize one event:

```rust
use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema, Validator, Value,
};

// (SCHEMA and POLICY are the strings from steps 1 and 2.)
// The service half takes its defaults (no macros/providers/event schema here);
// the policy half is your action schema.
let service = ServiceSchema::defaults();
let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA)?;
let policies = LoweredPolicySet::from_str(POLICY, &service, &policy_schema)?;

// Optional but recommended: type-check the policy against the schema.
// The validator takes no schema — the one the policy set was lowered
// against already travels on the `LoweredPolicySet`.
let report = Validator::new().validate(&policies);
assert!(report.validation_passed());

// Build the authorizer and ask it about one Read request.
let mut authorizer = Authorizer::new(policies);
let event = Event::builder("Drupe::Action::Read", "request")
    .principal("Drupe::OAuthUser::\"alice\"")
    .resource("Drupe::Gateway::\"gw1\"")
    .field("input", "user", Value::String("alice".to_string()))
    .build();

if let Some(response) = authorizer.is_authorized(&event) {
    assert_eq!(response.decision(), Decision::Allow);
}
```

Three details of Dogwood's model are worth noting here:

- You authorize an `Event`, not a bare request. An event is a timestamped
  occurrence of an action with a *kind* (here `"request"`) plus the
  principal/resource and input fields. `Event::builder` constructs one.
- `is_authorized` returns `Option<Response>`. You get `Some(response)` for a
  *decision-kind* event (like `request`) and `None` for a history-only event.
  With the default event schema, `request` is a decision kind — so this call
  returns `Some`.
- The `Authorizer` is `&mut`. It is stateful: it remembers every event you
  feed it. That does not matter for this pure-Cedar policy, but the next step
  depends on it.

The full API is [The API and workflow](07-api-and-workflow.md).

## Step 4 — a decision that depends on history

The next requirement depends on the past. Change it to:
*permit `Read` only if the same user logged in within the last hour.* That is a
statement about the **past**, so it uses a `when temporal { … }` clause:

```text
permit (
    principal,
    action == Drupe::Action::"Read",
    resource
)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
};
```

> Runnable: [`examples/read_after_login/`](../examples/read_after_login/) —
> `dogwood validate` and `dogwood replay`.

Read the temporal clause as: *"there was formerly, within the last 1 hour, a
successful `Login` whose `input.user` equals this request's `context.input.user`."*
The `formerly within 1h …` operator scans the event history; the
`{ input.user: context.input.user }` part correlates the past login's user with
the current request's user. This is the subject of
[Temporal expressions](04-temporal-expressions.md).

Because the decision now depends on history, we feed the authorizer a **stream**
of events and watch the verdicts change over time:

```rust
let mut authorizer = Authorizer::new(policies);

let events = vec![
    // A Login at t=0.
    Event::builder("Drupe::Action::Login", "request")
        .timestamp(0)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .build(),
    // A Read at t=10 — 10s after the login, well within the 1h window.
    Event::builder("Drupe::Action::Read", "request")
        .timestamp(10)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .build(),
    // A Read at t=7200 — two hours later; the login has expired.
    Event::builder("Drupe::Action::Read", "request")
        .timestamp(7200)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .build(),
];

for event in &events {
    if let Some(response) = authorizer.is_authorized(event) {
        println!("@{:<5} {:?}", event.timestamp(), response.decision());
    }
}
```

This prints:

```text
@0     Deny
@10    Allow
@7200  Deny
```

- `@0` Login → Deny. The policy gates `Read`, not `Login`, so no `permit`
  matches the login itself. (The login still matters — it is now in the history.)
- `@10` Read → Allow. A login for `alice` happened 10 seconds ago, inside the
  1-hour window, so the temporal condition holds.
- `@7200` Read → Deny. The only login was 7200 seconds (2 hours) ago, outside
  the window, so the condition no longer holds.

Same policy, same code — the verdict changes because the **history** changed.

## Run it yourself

You have two ways to run Dogwood, and this guide uses both.

**The command line.** The `dogwood` CLI drives the whole pipeline over plain
files — no Rust needed. Save the policy above to `policy.dw` and its schema to
`schema.cedarschema`, then validate and replay a trace:

```text
dogwood validate policy.dw --policy-schema schema.cedarschema
dogwood replay   policy.dw --policy-schema schema.cedarschema --trace trace.log
```

Every policy-level example in this guide is a complete, runnable bundle under
this crate's `examples/` directory — a `policy.dw`, its `schema.cedarschema`,
and (where the example is history-dependent) a `trace.log` and the expected
verdict stream. A test harness checks *every* bundle on each build, so the
examples cannot drift from the language. The two policies above are the
`permit_read_anyone` and `read_after_login` bundles. See
[The command line](12-cli.md) for the full CLI.

**The library.** To *embed* the engine instead of driving it over files —
building events programmatically, feeding them one at a time, and reading each
`Response` — use the Rust API, walked through end to end in
[The API and workflow](07-api-and-workflow.md). The CLI cannot drive the
builder API.

## Where to go next

- **The core syntax** — scopes, conditions, operators, types:
  [The policy language](02-policy-language.md).
- **History-based conditions** — the `temporal` sublanguage in full:
  [Temporal expressions](04-temporal-expressions.md).
- **Computed conditions** — information providers, called from an ordinary
  `when { … }`: [Information providers](05-information-providers.md).
- **Customizing the fixed inputs** — the event schema, providers, and MCP
  generation: [The event schema](03-event-schema.md),
  [The provider schema](10-provider-schema.md), and
  [Generating the action schema from an MCP manifest](11-mcp-schema-generation.md).
- **The full Rust API** — the end-to-end flow, and how to plug in your own
  policy or temporal engine: [The API and workflow](07-api-and-workflow.md).

## See also

- [Introduction](00-introduction.md) — the concepts behind this tutorial.
- [The policy language](02-policy-language.md) — the next step in learning the
  language.
