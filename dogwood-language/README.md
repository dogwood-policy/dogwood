# Dogwood Language

Dogwood is a policy language for authorization decisions that can depend on
more than a single point-in-time request. A policy is written in a familiar
`permit` / `forbid` style and may additionally reason about:

- **history** — *temporal* predicates (`formerly`, `since`, aggregations)
  over a stream of past events; and
- **computed values** — *information providers*, values produced on demand
  by a sandboxed script.

This crate parses Dogwood policies, type-checks them against a schema, and
evaluates them against a stream of events with a stateful authorizer.

## The lifecycle

Authorization is four steps: build the two schema halves — a [`ServiceSchema`]
(the fixed, service-provided inputs) and a [`PolicySchema`] (your action
schema) — lower policy source into a [`LoweredPolicySet`], type-check it with a
[`Validator`], then feed events to an [`Authorizer`].

```rust,ignore
use dogwood_language::{
    ServiceSchema, PolicySchema, LoweredPolicySet, Validator, Authorizer, Event, Decision, Value,
};

// 1. Describe your actions and entities in the action schema; the service
//    schema (macros, providers, event schema) takes its defaults here.
let service = ServiceSchema::defaults();
let policy_schema = PolicySchema::from_cedarschema_str(action_schema_src)?;

// 2. Parse + lower the policy against those schemas.
let policies = LoweredPolicySet::from_str(policy_src, &service, &policy_schema)?;

// 3. Type-check the policy. The validator takes no schema — the one the policy
//    set was lowered against already travels on the LoweredPolicySet.
let result = Validator::new().validate(&policies);
assert!(result.validation_passed());

// 4. Build an authorizer and feed it events. The authorizer is stateful:
//    each event is remembered, so temporal predicates can see the past.
let mut authorizer = Authorizer::new(policies);
let event = Event::builder("Drupe::Action::Read", "request")
    .principal("Drupe::OAuthUser::\"alice\"")
    .resource("Drupe::Gateway::\"gw1\"")
    .field("input", "document", Value::String("report".to_string()))
    .build();
if let Some(response) = authorizer.is_authorized(&event) {
    assert_eq!(response.decision(), Decision::Allow);
}
```

When the action schema arrives *later* than the policy source (or one policy
set is lowered against several action schemas), split step 2 into its two
phases: [`ParsedPolicySet::parse`](ParsedPolicySet::parse) (needs only the
`ServiceSchema`) then [`lower`](ParsedPolicySet::lower) (needs the
`PolicySchema`). To combine independently-lowered sets into one Cedar
`PolicySet` / policy store, give each `lower` call a distinct namespace with
[`lower_with_distincter`](ParsedPolicySet::lower_with_distincter).

For the full language guide, the `dogwood` command-line tool, and complete,
runnable example bundles (each checked by the CLI on every build), see the
sibling **`dogwood-docs`** crate.

## The schema

Everything the parser and evaluator need about your domain is split into two
halves, along the one axis that matters — the **action schema**:

- the **[`ServiceSchema`]** — the *fixed, service-provided* inputs, available
  up front (before any action schema exists): the macro library, the provider
  declarations, and the event-schema DSL. Assemble it with
  [`ServiceSchema::builder`], or take the all-defaults form with
  [`ServiceSchema::defaults`].
- the **[`PolicySchema`]** — the *per-customer* action schema (a Cedar
  `.cedarschema`, or one generated from an MCP tool manifest), which typically
  arrives later. Construct it with [`PolicySchema::from_cedarschema_str`] or
  [`PolicySchema::from_mcp_manifest`].

```rust,ignore
use dogwood_language::{ServiceSchema, PolicySchema, ProviderDeclarations};

// The service half — everything customer-independent.
let service = ServiceSchema::builder()
    .event_schema_str(event_dsl)  // optional — default: request/response
    .macros_str(macro_library)    // optional — default: DEFAULT_MACROS (stdlib)
    .providers(provider_decls)    // optional — default: none
    .build()?;

// The action half.
let policy_schema = PolicySchema::from_cedarschema_str(action_schema_src)?;
```

The four parts, and which half each lives on:

1. **Action schema** *(required, on `PolicySchema`)* — the entity types and
   actions of your domain, as a Cedar `.cedarschema`. Set it directly with
   [`PolicySchema::from_cedarschema_str`], or generate it from an **MCP tool
   manifest** (see below).
2. **Event schema** *(optional, on `ServiceSchema`)* — the
   [`event_schema_str`](ServiceSchemaBuilder::event_schema_str) DSL describing
   the kinds of event each action can produce and the fields each carries. Omit
   it to use [`DEFAULT_EVENT_SCHEMA`], the request/response convention: every
   action gets a `request` decision event (inputs and reserved leaves), a
   `response` history event (inputs, outputs, and reserved leaves), and an
   `error` history event (inputs and reserved leaves).
   (It is *derived* against the action schema at lower time, which is why it
   lives on the service half as unbound DSL, not as a finished artifact.)
3. **Macro library** *(optional, on `ServiceSchema`)* — reusable `def cedar` /
   `def temporal` definitions ([`macros_str`](ServiceSchemaBuilder::macros_str))
   that any policy can call without re-declaring. Omit it to use
   [`DEFAULT_MACROS`], which ships a small standard library of temporal
   aggregation macros (`count_within`, `sum_within`, `count_distinct_within`,
   `bind`). A policy's own `def` of the same name takes precedence, so a shared
   library can never override a policy's intent.
4. **Provider declarations** *(optional, on `ServiceSchema`)* — the
   argument/output signature and implementation of each information provider
   ([`providers`](ServiceSchemaBuilder::providers)), as JSON parsed by
   [`ProviderDeclarations`]. Omit it if no policy uses a `guardrail { … }`
   clause.

The built-in defaults — the default event schema, the default macro
standard library, and the Drupe schema-generator template — live in the
crate's `data/` directory.

### Generating the action schema from an MCP manifest

A Dogwood action schema can be produced directly from a Model Context
Protocol (MCP) tool manifest: each tool becomes an action, with its input
and output fields as the request context. Use the
[`PolicySchema::from_mcp_manifest`] shortcut (layered on the built-in
Drupe template):

```rust,ignore
let policy_schema = PolicySchema::from_mcp_manifest(mcp_tools_json)?;
```

To supply your own template stub instead of Drupe, use
[`PolicySchema::from_mcp_manifest_with_template`]. (The lower-level
[`mcp_to_cedar_schema`] function is also available if you want the generated
`.cedarschema` text directly.)

## Events and the authorizer

An [`Authorizer`] is **stateful**. You build it once from a
[`LoweredPolicySet`] and then feed it [`Event`]s one at a time with
[`is_authorized`](Authorizer::is_authorized);
each event is folded into an accumulated history so that temporal predicates
can look back over earlier events.

An [`Event`] is a timestamped occurrence of an action, of a given *kind*,
carrying named input fields and — when it wraps an authorization request — a
principal and resource. Build one with [`Event::builder`]:

```rust,ignore
let event = Event::builder("Drupe::Action::SellShares", "request")
    .timestamp(1_000)
    .principal("Drupe::OAuthUser::\"alice\"")
    .resource("Drupe::Gateway::\"gw1\"")
    .field("input", "stock", Value::String("AMZN".to_string()))
    .field("input", "shares", Value::Int(500))
    .build();
```

The event *kind* decides whether the event produces a verdict. The event
schema marks some kinds as **decision** kinds (in the default schema,
`request` is one and `response` is not).
[`is_authorized`](Authorizer::is_authorized) returns:

- `Some(`[`Response`]`)` for a decision-kind event — the authorization result; or
- `None` for a history-only event — it still updates the history that
  temporal predicates see, but produces no verdict.

A [`Response`] carries the [`decision`](Response::decision)
(`Allow` / `Deny`) and [`diagnostics`](Response::diagnostics): the Dogwood
rules that determined the decision ([`reason`](Diagnostics::reason)) and any
evaluation errors ([`errors`](Diagnostics::errors)). Evaluation is
**fail-closed** — if a provider or guard cannot be evaluated, the decision
degrades to `Deny` with the error recorded in the diagnostics, never a
spurious `Allow`.

For a single one-off decision, a fresh `Authorizer` fed one `request`-kind
event is all you need — there is simply no prior history.

## Swapping the backends

The authorizer is assembled from two swappable pieces, each with a built-in
default and a trait you can implement to replace it. Install your own with
[`Authorizer::builder`] instead of [`Authorizer::new`]:

```rust,ignore
let authorizer = Authorizer::builder(policies)
    .policy_engine(my_policy_engine)      // defaults to CedarPolicyEngine
    .temporal_engine(my_temporal_engine)  // defaults to InMemoryTemporalEngine
    .build()?;
```

### The decision backend — [`PolicyEngine`]

A [`PolicyEngine`] makes the actual authorization decision. Its shape mirrors
a Cedar-based authorization service's `IsAuthorized`: the policies and
schema are installed once at [`prepare`](PolicyEngine::prepare) (like
populating a policy store), and each [`is_authorized`](PolicyEngine::is_authorized)
takes an [`AuthorizationRequest`] (a Cedar request + entities) and returns an
[`AuthorizationDecision`] (decision + determining policy ids + errors).

The default [`CedarPolicyEngine`] evaluates locally with the `cedar-policy`
crate. To decide with an external service instead, implement [`PolicyEngine`] over
a remote client: forward the policies to a policy store in `prepare`, and call
the service's authorization API in `is_authorized`. Dogwood maps the returned policy ids back
to the `.dw` rules and applies the same fail-closed handling.

### The temporal backend — [`TemporalEngine`]

A [`TemporalEngine`] computes the boolean value of each hoisted
`temporal { … }` leaf. It has three lifecycle points, which is what lets a
backend *compile* the leaves and evaluate them against a **database**:

- [`prepare`](TemporalEngine::prepare) — once, when the authorizer is built.
  A compiling backend turns each [`TemporalField`] into a query and creates
  its tables here.
- [`observe`](TemporalEngine::observe) — for *every* event ingested, in
  order. A database backend inserts a row (reading the event's fields via
  [`Event::field`] / [`Event::principal`] / [`Event::fields`]).
- [`evaluate`](TemporalEngine::evaluate) — at each decision point, returning
  each leaf's boolean. A database backend runs its compiled queries here.

The default [`InMemoryTemporalEngine`] keeps the event history in memory and
re-runs the interpreter; because it holds the history, the `Authorizer`
itself is stateless between the engines. A failure from either backend
(a compile error at build time, an unreachable database at decision time)
fails the affected decision closed.

The two seams are independent — replace one, the other, or both.

## Writing policies over history and computed values

A policy adds guards to a `permit` / `forbid` with `when` clauses. Beyond
ordinary boolean conditions, two clause forms give Dogwood its reach:

```text
permit ( principal, action == Drupe::Action::"SellShares", resource )
when temporal {
    // history: an ApproveSale for the same stock within the last hour
    formerly within 1h Drupe::Action::"ApproveSale"::request{ input.stock: context.input.stock }
}
when guardrail {
    // computed value: an information provider says the stock is not high-risk
    Risk::Elevated(context.input.stock).high == false
};
```

- A **`temporal { … }`** clause is evaluated against the event history the
  authorizer has accumulated — this is why the authorizer is stateful.
- A **`guardrail { … }`** clause invokes an information provider (declared in
  the schema's provider declarations) and reads its output.

Reusable fragments of either can be factored into macros
(`def cedar` / `def temporal`) and shared through the schema's macro library.

## Exporting compiled artifacts

A [`LoweredPolicySet`] also exposes the artifacts it compiles down to, for use
with tools that consume plain Cedar — including external Cedar-based authorization services:

- [`as_cedar`](LoweredPolicySet::as_cedar) — the compiled Cedar policies.
- [`cedar_schema`](LoweredPolicySet::cedar_schema) — the schema they validate
  against (augmented with any fields the compilation introduced).
- [`is_self_contained_cedar`](LoweredPolicySet::is_self_contained_cedar) —
  whether those artifacts reproduce the policy's meaning on their own. It is
  `true` for a policy with no `temporal` / `guardrail` clauses (fully
  offloadable to a policy store), and `false` when a policy needs Dogwood's monitor to
  supply the history- and provider-derived values at decision time.

The hoisted-leaf and rule mappings a consumer needs to reimplement the decision
loop are also exposed: [`temporal_fields`](LoweredPolicySet::temporal_fields),
[`provider_fields`](LoweredPolicySet::provider_fields), and
[`rules`](LoweredPolicySet::rules) / [`rule_ref`](LoweredPolicySet::rule_ref).
