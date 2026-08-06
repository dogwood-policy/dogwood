# The API and Workflow

This page is the Rust API reference for the `dogwood_language` crate and the end-to-end tutorial for using it. It walks through the authorization workflow — build the two **schema** halves, parse and lower a **LoweredPolicySet**, type-check it with a **Validator**, then drive **Event**s through a stateful **Authorizer** to get a **Response** — with a complete, runnable-looking example. It then documents every public type grouped by role, explains the engine seam that lets you replace the policy or temporal engine with your own, and covers trace replay, MCP schema generation, and Cedar export. If you have never called the crate before, read the tutorial first; if you already know the shape and want a specific signature, jump to the grouped reference.

The API mirrors the `cedar-policy` crate. Wherever a concept has a Cedar counterpart the name matches: `Validator`, `Authorizer`, `Response`, `Decision`, `Diagnostics`, `ValidationResult`. The schema and policy-set types differ because a Dogwood policy set is bound to its (augmented) schema at lower time and Dogwood's schema splits into two halves: Cedar's single `Schema` becomes a `ServiceSchema` + `PolicySchema`, and Cedar's `PolicySet` becomes a `LoweredPolicySet` (with a `ParsedPolicySet` for the schema-free parse phase). Two signatures then depart from Cedar's: `LoweredPolicySet::from_str` *takes* the schemas, and `Validator::new()` takes *none* (details in the Validator section below). Two further divergences are semantic — things Cedar cannot express — and both live on the authorizer:

1. `Authorizer` is **stateful** — each ingested `Event` folds into an accumulated history so temporal operators can see the past.
2. `Authorizer::is_authorized` returns **`Option<Response>`** — `None` for a history-only event whose kind is not a decision kind.

Nearly all of the public API is re-exported at the crate root, so you reach it through `dogwood_language::<T>`; the internal `pub mod` modules exist only to give rustdoc a home (and a few AST types live under `dogwood_language::temporal_ast`).

---

## Your first authorization

The goal of this section is to get you from a schema and a policy to a verdict, and to understand *why* each step exists. The complete program is shown inline below. (If you only need to check or replay policies over files rather than embed the engine, you do not need this API — see [The command line](12-cli.md).)

The scenario is a two-action agent schema (`Login`, `Read`) with a policy that permits `Read` only if the same user logged in within the last hour. That "within the last hour" clause is temporal, which is what makes this stateful and impossible to express in plain Cedar.

### The pipeline, one stage at a time

The sequence is always the same:

```text
ServiceSchema + PolicySchema  ->  LoweredPolicySet  ->  Validator  ->  Authorizer  ->  Event  ->  is_authorized  ->  Response
```

Each stage produces the input for the next, and one ownership handoff matters: a `LoweredPolicySet` is *moved* into the `Authorizer`, so inspect and reuse it before that. The two schema halves are only *borrowed* while lowering and are not needed again (the validator takes none), so they stay available throughout.

**Stage 1 — Schemas.** A Dogwood schema has two halves. The `ServiceSchema` holds the fixed, service-provided inputs — the event schema and provider declarations (both optional, both defaulted) plus the macro library; the `PolicySchema` holds the Cedar action schema. This policy uses only a temporal leaf, so the service defaults are exactly right (`ServiceSchema::defaults()`), and `PolicySchema::from_cedarschema_str` is the one-call shortcut for the action schema.

```rust
use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, PolicySchema, ServiceSchema, Validator, Value,
};

// A minimal agent schema: a `Login` action and a `Read` action, each with a
// `user` input field.
const SCHEMA: &str = r#"
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
"#;

let service = ServiceSchema::defaults();                    // or ServiceSchema::builder()…build()
let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA)?;
```

**Stage 2 — LoweredPolicySet.** Unlike Cedar's `PolicySet::from_str`, Dogwood's takes the two schema halves. Lowering the `temporal { … }` clause derives event signatures from the action schema and *augments* it — it hoists a synthesized `context.<id>` field that the lowered Cedar policies reference. Because those extra schema arguments do not fit `std::str::FromStr`, this is an **inherent method** named `from_str`: call `LoweredPolicySet::from_str(src, &service, &policy_schema)`, **not** `src.parse()`. (When the action schema arrives later than the source, split this into `ParsedPolicySet::parse(src, &service)` then `.lower(&policy_schema)` — see [The parse/lower split](#the-parselower-split).)

```rust
// Permit `Read` only if the same user logged in within the last hour. The
// `temporal { … }` clause is what makes the authorizer stateful.
const POLICY: &str = r#"
permit (
    principal,
    action == Drupe::Action::"Read",
    resource
)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
};
"#;

let policies = LoweredPolicySet::from_str(POLICY, &service, &policy_schema)?; // inherent fn, not .parse()

// The policy hoisted a temporal leaf, so it is NOT self-contained Cedar:
// reproducing it needs Dogwood's monitor, not just the exported Cedar.
// (A pure-Cedar policy would report `true` here and could be shipped to
// external store as-is via `as_cedar()` / `cedar_schema()`.)
println!("self-contained Cedar = {}", policies.is_self_contained_cedar());
```

`LoweredPolicySet::from_str` returns `Error` on syntax, macro, or lowering failure. It does **not** report type errors against the schema — those are validation findings, which is the next stage. Inspect the `LoweredPolicySet` (with `is_self_contained_cedar`, `as_cedar`, `cedar_schema`) *before* stage 4, because the authorizer consumes it.

**Stage 3 — Validator.** `Validator::new().validate(&policies)`. It runs Cedar's own validator over the lowered policies (against the augmented schema) plus each Dogwood dialect's own checks, and rebases every finding to the originating `.dw` source span. Unlike Cedar's `Validator::new(schema)`, Dogwood's takes **no** schema: the schema a policy set was lowered against — augmented with its hoisted `context.<id>` fields — already travels on the `LoweredPolicySet`, and that is what validation runs against. (A Dogwood `LoweredPolicySet` is schema-bound at lower time, so unlike Cedar you cannot reuse one validator across policy sets built from different schemas.)

```rust
let report = Validator::new().validate(&policies);
assert!(report.validation_passed());
```

**Stage 4 — Authorizer.** `Authorizer::new` consumes the `LoweredPolicySet` and is infallible with the built-in backends. The authorizer is stateful: each `is_authorized` call folds the event into history so the temporal leaf can see prior events.

```rust
let mut authorizer = Authorizer::new(policies); // consumes policies
```

**Stage 5 — Event.** An `Event` is Dogwood's generalization of a Cedar `Request`. It carries a first-class `kind` (here `"request"`), an optional principal/resource scope, and input fields exposed to the policy as `context.input.<name>`.

**Stage 6 & 7 — is_authorized and Response.** `is_authorized` takes `&mut self` (stateful) and returns `Option<Response>`. Every event here is a `request` (a decision kind), so each yields `Some(response)`. Read the verdict from `response.decision()` and the explanation from `response.diagnostics()`.

```rust
let events = vec![
    Event::builder("Drupe::Action::Login", "request")
        .timestamp(0)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .build(),
    Event::builder("Drupe::Action::Read", "request")
        .timestamp(10)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .build(),
    Event::builder("Drupe::Action::Read", "request")
        .timestamp(7200)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw1\"")
        .field("input", "user", Value::String("alice".to_string()))
        .build(),
];

let mut decisions = Vec::new();
for event in &events {
    // `is_authorized` returns None for a non-decision (history-only) event;
    // here every event is a `request`, so each yields a Response.
    if let Some(response) = authorizer.is_authorized(event) {
        println!("@{:<5} {:?}", event.timestamp(), response.decision());
        decisions.push(response.decision());
    }
}

//   @0    Login → Deny  (the policy gates Read, not Login)
//   @10   Read  → Allow (login within the 1h window)
//   @7200 Read  → Deny  (login expired: 7200s > 3600s)
assert_eq!(decisions, vec![Decision::Deny, Decision::Allow, Decision::Deny]);
```

### What just happened

Three events went in and the verdict stream came out as `[Deny, Allow, Deny]`. The first `Read` is allowed because a `Login` for the same user landed within the 3600-second window; the second `Read` is denied because that login has expired (7200 > 3600). This is the two Cedar-inexpressible facts made concrete: the authorizer *remembered* the earlier login (statefulness), and — because every event was a decision-kind `request` — each call returned `Some(Response)` rather than `None`.

### Ownership gotchas

- Both schema halves are only **borrowed** by `LoweredPolicySet::from_str(&service, &policy_schema)`, and the validator takes none, so they stay usable afterward — but a `LoweredPolicySet` is bound to the schema it was lowered against, so validation always uses that one.
- `LoweredPolicySet` is **moved** into `Authorizer::new(policies)` / `Authorizer::builder(policies)`, so do any `as_cedar()` / `is_self_contained_cedar()` inspection *before* that.
- `LoweredPolicySet::from_str(src, &service, &policy_schema)` is an inherent method, **not** `src.parse()`.

A version of this tour that exercises every schema option at once — MCP-generated action schema, explicit event schema, a macro library, and provider declarations — is summarized in [MCP schema generation](#mcp-schema-generation) and [Information provider declarations](10-provider-schema.md).

---

## API reference

Everything below is reachable as `dogwood_language::<T>`. The reference groups types by the role they play in the pipeline.

### ServiceSchema and PolicySchema

Cedar has one schema; Dogwood needs **three parts plus a macro library**, grouped into two halves by where each comes from.

The **`ServiceSchema`** — the fixed, service-provided inputs, none of which need an action schema:

1. **event schema** — the Dogwood event-schema DSL describing how event kinds and their fields derive from the action schema. **Optional**; defaults to `DEFAULT_EVENT_SCHEMA` (the request/response convention). Held *parsed but unbound* — derivation against the action schema is deferred to lowering. See [The event schema](03-event-schema.md).
2. **provider declarations** — information-provider signatures and implementations (JSON). **Optional**; defaults to empty. See [The provider schema](10-provider-schema.md).
3. **macro library** — reusable `def cedar` / `def temporal` definitions merged into every policy set at parse time. **Optional**; defaults to `DEFAULT_MACROS`, which ships a small **standard library** of temporal aggregation macros (`count_within`, `sum_within`, `count_distinct_within`, `bind`). A policy's own `def` of the same name takes precedence over a library macro. See [Macros](06-macros.md).

```rust
impl ServiceSchema {
    pub fn builder() -> ServiceSchemaBuilder;
    pub fn defaults() -> ServiceSchema;   // all three defaulted; == builder().build()
}

impl ServiceSchemaBuilder {
    pub fn event_schema_str(mut self, src: &str) -> Self;   // omit for DEFAULT_EVENT_SCHEMA
    pub fn providers(mut self, declarations: ProviderDeclarations) -> Self; // omit for empty
    pub fn macros_str(mut self, src: &str) -> Self;         // omit for DEFAULT_MACROS
    pub fn build(self) -> Result<ServiceSchema, Error>;
}
```

`build()` parses the event-schema DSL (it does **not** derive it — that needs the action schema and happens at lowering). An **empty or whitespace-only** `event_schema_str` is explicitly rejected. A blank event schema parses to zero declarations, which yields a schema with no decision kinds, so `is_authorized` would return `None` for *every* event — a subtle footgun. If you want the default behavior, omit `event_schema_str` entirely rather than passing an empty string. (The default path always derives a `decision request` event, so this never trips there.)

The **`PolicySchema`** — the **action schema** (a Cedar `.cedarschema`: entity types + actions), which typically arrives later and varies per deployment. Supply Cedar text directly, or generate it from an MCP tool manifest (resolved eagerly at construction, so MCP-generation failures surface here):

```rust
impl PolicySchema {
    pub fn from_cedarschema_str(action_schema_src: &str) -> Result<PolicySchema, Error>;
    pub fn from_mcp_manifest(manifest_json: &str) -> Result<PolicySchema, Error>;
    pub fn from_mcp_manifest_with_template(manifest_json: &str, template: &str) -> Result<PolicySchema, Error>;
}
```

- `from_cedarschema_str(src)` — Cedar `.cedarschema` text used verbatim. Mirrors `cedar_policy::Schema::from_cedarschema_str`.
- `from_mcp_manifest(manifest_json)` — generate the action schema from an MCP `tools/list` manifest layered on the embedded Drupe template (the eager form of `mcp_to_cedar_schema`).
- `from_mcp_manifest_with_template(manifest_json, template)` — as above but against a caller-supplied Cedar template stub instead of Drupe.

**Constants:**

- `DEFAULT_EVENT_SCHEMA: &str` — the built-in request/response convention. For every action `A` it derives a `request` **decision** event (input fields, `callerPrincipal`, `callerResource`, `requestId`, and `sessionId`), a `response` **history** event (input plus output fields and the same reserved leaves), and an `error` **history** event (input fields and reserved leaves, no outputs).
- `DEFAULT_MACROS: &str` — the built-in macro library. It ships a small **standard library** of temporal aggregation macros (`count_within`, `sum_within`, `count_distinct_within`, `bind`), embedded at build time so they are available regardless of working directory. A policy's own `def` of the same name takes precedence.

### The parse/lower split

Lowering is split into two phases along the input that motivates it — the action schema:

```rust
impl ParsedPolicySet {
    pub fn parse(source: &str, service_schema: &ServiceSchema) -> Result<ParsedPolicySet, Error>;
    pub fn lower(&self, policy_schema: &PolicySchema) -> Result<LoweredPolicySet, Error>;
    pub fn lower_with_distincter(&self, policy_schema: &PolicySchema, distincter: &str) -> Result<LoweredPolicySet, Error>;
}
```

- `parse(source, &service)` — **phase 1**, schema-free. Parses and macro-expands against the `ServiceSchema` alone; catches syntax and macro-resolution errors but **not** schema-dependent ones (unknown attributes, type errors) — those need the action schema. Useful to reject a broken policy before the action schema is available. The returned `ParsedPolicySet` carries its `ServiceSchema`, so phase 2 needs only the `PolicySchema`.
- `lower(&policy_schema)` — **phase 2**. Derives the event schema against the action schema, lowers to Cedar, augments the schema with hoisted `context.<id>` fields, and injects pins. Produces the `LoweredPolicySet`. Emitted policy ids and hoisted field names use the default `policy_<index>` namespace.
- `lower_with_distincter(&policy_schema, distincter)` — like `lower`, but namespaces this call's policy ids and hoisted field names under `distincter` (ids become `<distincter>_<index>`). Supply a **distinct** value per call when combining independently-lowered sets into one Cedar `PolicySet` / policy store, or when feeding an augmented schema forward. The `distincter` must be a valid Cedar identifier (`[_A-Za-z][_A-Za-z0-9]*`) — else `Error::InvalidDistincter`. It is **not** derived from a source `@id`; distinctness is the caller's decision. Note the plain `lower` path uses the namespace `policy`, so it is not automatically distinct from a `"policy"` distincter.

`LoweredPolicySet::from_str(src, &service, &policy_schema)` (below) is the fused form of `parse` then `lower` for when the action schema is already in hand.

### LoweredPolicySet and the Cedar export accessors

`LoweredPolicySet` is opaque. It is produced by `ParsedPolicySet::lower` (or the fused `from_str` shortcut) and consumed by `Validator::validate` and `Authorizer::new` / `Authorizer::builder`. Beyond lowering, its accessors are the bridge to plain Cedar and external policy stores.

```rust
impl LoweredPolicySet {
    pub fn from_str(source: &str, service_schema: &ServiceSchema, policy_schema: &PolicySchema) -> Result<LoweredPolicySet, Error>;
    pub fn as_cedar(&self) -> &cedar_policy::PolicySet;
    pub fn cedar_schema(&self) -> &cedar_policy::Schema;
    pub fn cedar_schema_str(&self) -> Result<String, Error>;
    pub fn cedar_schema_json(&self) -> Result<String, Error>;
    pub fn is_self_contained_cedar(&self) -> bool;
    pub fn temporal_fields(&self) -> impl Iterator<Item = &TemporalField>;
    pub fn provider_fields(&self) -> impl Iterator<Item = &ProviderField>;
    pub fn rules(&self) -> impl Iterator<Item = DogwoodRuleRef> + '_;
    pub fn rule_ref(&self, cedar_policy_id: &str) -> Option<DogwoodRuleRef>;
    pub fn decision_kinds(&self) -> impl Iterator<Item = &str>;
    pub fn is_decision_kind(&self, kind: &str) -> bool;
}
```

- `from_str(source, service, policy_schema)` — fused parse + lower. Inherent method; returns `Error` on syntax / macro / lowering failure. **Type errors against the schema are not returned here** — run `Validator::validate` for those.
- `as_cedar()` — borrow the lowered Cedar policies (a real `cedar_policy::PolicySet`). This is the artifact to hand to the `cedar-policy` crate directly, or (rendered to policy text) to a policy store's create-policy API.
- `cedar_schema()` / `cedar_schema_str()` / `cedar_schema_json()` — the augmented Cedar schema (action schema plus hoisted `context.<id>` fields), respectively as an opaque `cedar_policy::Schema`, as `.cedarschema` text, and as the Cedar JSON schema form (what a Cedar policy store's schema ingest accepts). The text form round-trips: it can seed a later lowering via `PolicySchema::from_cedarschema_str`.
- `is_self_contained_cedar()` — `true` iff lowering hoisted **no** temporal or provider `context.<id>` fields, so the exported Cedar artifacts fully reproduce the policy's semantics in plain Cedar with no extra context. When `false`, the policy uses `temporal { … }` and/or `guardrails { … }`: a Cedar policy store can still evaluate the exported policies, but each authorization call must be supplied the hoisted `context.<id>` values. Computing those values is Dogwood's temporal-monitor / provider-evaluation job — so in that case **Dogwood produces the enriched context and the policy store performs the final Cedar decision.**
- `temporal_fields()` / `provider_fields()` — the hoisted leaves (each with its `context.<id>` field name, action, and what to evaluate). A consumer reimplementing the decision loop computes each leaf's value and binds it into the request context.
- `rules()` / `rule_ref(id)` — the Dogwood rules as `DogwoodRuleRef`s, and the reverse map from a Cedar policy id (as named in a decision) back to its originating rule.
- `decision_kinds()` / `is_decision_kind(kind)` — which event kinds are decision points (authorization runs and yields a verdict); any other kind is history-only. This is the gate `Authorizer::is_authorized` applies before returning `Some`/`None`.

### Validator, ValidationResult

Validation is the second of Dogwood's two error channels (see [Errors](#errors)): the policy already parsed and lowered, and this stage checks whether it is *correct against the schema*.

```rust
impl Validator {
    pub fn new() -> Self;   // takes no schema — see below
    pub fn validate(&self, policies: &LoweredPolicySet) -> ValidationResult;
}

impl ValidationResult {
    pub fn validation_passed(&self) -> bool;                  // no errors (warnings ignored)
    pub fn validation_passed_without_warnings(&self) -> bool; // no errors AND no warnings
    pub fn validation_errors(&self) -> impl Iterator<Item = &ValidationError>;
    pub fn validation_warnings(&self) -> impl Iterator<Item = &ValidationWarning>;
}
```

- **No schema argument** (unlike `cedar_policy::Validator::new(schema)`). Cedar's validator owns a schema so one validator can be reused across many policy sets — a Cedar schema is policy-independent. Dogwood's is not: lowering *augments* the schema with the `context.<id>` fields hoisted from a policy set's own temporal / provider clauses, so the effective validation schema is a function of the policies and already travels on the `PolicySet`. `validate` reads it from there; a schema argument would be redundant (the same one) or wrong (the un-augmented base).
- Under the hood, `validate` runs Cedar's own validator on the lowered policies (against that augmented schema) *plus* each Dogwood dialect's checks (temporal, provider) and the event-schema names check, rebasing every finding to the originating `.dw` source span. It always uses Cedar's default (strict) mode — there is no mode argument, because the non-strict modes are not meaningful once a hoisted `context.<id>` field must typecheck.
- `ValidationResult` collects every finding rather than stopping at the first. Warnings **never** make validation fail.

Both finding types are `#[derive(Error, Diagnostic, Debug)]` (miette) and are **self-rendering**: each embeds its `.dw` source alongside the span, so `miette::Report::new(err)` prints the underlined snippet with **no** `with_source_code` — the same way the fatal `Error` from `LoweredPolicySet::from_str` renders, and the same way Cedar's own errors do. There are **no accessor methods** on the finding enums; render via their `Display` / miette `Diagnostic` impls or match the variants directly.

```rust
pub enum ValidationError {
    Cedar { message, span, label, help, src, source },              // Cedar's validator rejected the lowered policy
    Extension { code: &'static str, message, span, label, help, src, source }, // dialect finding; code is "temporal" / "provider" / …
}

pub enum ValidationWarning {
    Cedar(cedar_policy::ValidationWarning),                         // Cedar's own warning verbatim
    Extension { code, message, span, label, help, src, source },    // dialect warning (no dialect emits one today)
}
// `src` is the embedded `.dw` source (Arc<str>) — this is what makes a finding
// self-render, so `miette::Report::new(err)` needs no `with_source_code`.
```

### Event, EventBuilder, Value

An `Event` is Dogwood's generalization of `cedar_policy::Request`. Its distinguishing feature is a first-class `kind` string: a `request`-kind event is a decision point (it authorizes), while a `response`-kind event is history-only. *Which* kinds decide is data (the event schema's `decision` flags, queryable via `Schema::decision_kinds()`), not a hardcoded convention.

```rust
impl Event {
    pub fn builder(action: &str, kind: &str) -> EventBuilder;
    pub fn kind(&self) -> &str;
    pub fn action(&self) -> &str;             // unqualified id, e.g. "Login"
    pub fn namespace(&self) -> &[String];     // e.g. ["Drupe", "Action"]; empty if bare
    pub fn timestamp(&self) -> i64;
    pub fn principal(&self) -> Option<String>; // e.g. Drupe::OAuthUser::"alice"; None if history-only
    pub fn resource(&self) -> Option<String>;  // e.g. Drupe::Gateway::"gw1"; None otherwise
    pub fn field(&self, group: &str, name: &str) -> Option<&Value>;      // one logged field, e.g. field("input", "user")
    pub fn fields(&self, group: &str) -> impl Iterator<Item = (&str, &Value)>; // all fields of a logged group
    pub fn from_request(request: &cedar_policy::Request) -> Result<Event, Error>;
}
```

- `builder(action, kind)` — start building. `action` is the qualified Cedar action id, either bare (`"Login"`) or namespaced (`"Drupe::Action::Login"`); the builder splits it into `(namespace, id)`. `kind` is the event-kind string (`"request"`, `"response"`, …).
- The **request scope is optional**: only an event that wraps a request carries a principal/resource, so history-only events return `None` from `principal()` / `resource()`.
- `field(group, name)` reads one field of the **logged temporal record** (`field("input", "user")`); `fields(group)` yields all `(name, value)` pairs of a group — what an engine that persists history outside the process would record on `observe`. There is no `input`-specific accessor: `input` is just the `"input"` group, read like any other. The **Cedar request context** a policy sees as `context.<group>.<name>` is a separate bag, read via `request_context_path`.
- `from_request(&cedar::Request)` — interop bridge for callers coming from `cedar-policy`. It lifts a Cedar `Request` into a **`request`-kind** `Event` at **timestamp `0`**: principal/resource become the scope, the action becomes the qualified action, and `context.input` becomes the input fields. A stateless single-decision authorization is then just a fresh `Authorizer` fed this one event.

```rust
impl EventBuilder {
    pub fn timestamp(mut self, ts: i64) -> Self;              // default 0
    pub fn principal(mut self, uid: &str) -> Self;            // e.g. User::"alice"; makes the event request-wrapping
    pub fn resource(mut self, uid: &str) -> Self;             // e.g. Photo::"vacation.jpg"; makes it request-wrapping
    pub fn field(mut self, group: &str, name: &str, value: Value) -> Self;  // logged temporal record, e.g. field("input", "user", v)
    pub fn request_context(mut self, group: &str, name: &str, value: Value) -> Self; // Cedar request context (context.<group>.<name>)
    pub fn build(self) -> Event;
}
```

- Setting a principal **or** resource marks the event as wrapping an authorization request (it gains a principal/resource scope).
- `timestamp` defaults to `0`; timestamps order events for temporal operators, and the first event of a fresh authorizer can safely stay at `0`.
- `field(group, name, value)` accumulates into the logged record's nested `group` object (`input` is one such group, not privileged). It is **not** read by a policy's `context.<group>.<name>` clause — that reads the separate request-context bag set via `request_context(group, name, value)`. A field a policy reads *and* a temporal predicate correlates on must be supplied to **both**.
- Entity uid strings are parsed as `Type::"id"` (possibly namespaced); a string that is not of that shape yields no scope value.

`Value` is the runtime value type for event fields:

```rust
pub enum Value {
    Null,
    Bool(bool),
    Int(i64),
    Decimal(String),          // canonical text; equality canonicalizes (1.5 == 1.50)
    String(String),
    Entity { ty: String, id: String },
    Array(Vec<Value>),
    Object(BTreeMap<String, Value>),
}

impl Value {
    pub fn dom_eq(&self, other: &Value) -> bool; // structural eq with decimal canonicalization
    pub fn as_int(&self) -> Option<i64>;         // integer view; None if not an Int
}
```

The constructors you will use most are `Value::String(s.to_string())` and `Value::Int(n)`, as in the tour. `Decimal` is canonical text; `Entity` / `Array` / `Object` build the structured shapes.

### Authorizer, AuthorizerBuilder, Response, Diagnostics, Decision

The `Authorizer` is the stateful monitor. It is built from a `LoweredPolicySet` and assembled from two swappable backends (see [The engine seam](#the-engine-seam)): a `PolicyEngine` (decision; default `CedarPolicyEngine`) and a `TemporalEngine` (temporal-leaf evaluation; default `InMemoryTemporalEngine`).

```rust
impl Authorizer {
    pub fn new(policies: LoweredPolicySet) -> Self;                  // built-in backends; infallible
    pub fn builder(policies: LoweredPolicySet) -> AuthorizerBuilder; // to substitute backends
    pub fn is_authorized(&mut self, event: &Event) -> Option<Response>;
}
```

- `new(policies)` — built-in backends, **infallible** (the defaults' `prepare` cannot fail). Consumes the `LoweredPolicySet`.
- `builder(policies)` — for custom backends.
- `is_authorized(&mut self, event)` — `&mut self` (stateful) returning `Option<Response>`:
  - The event is **always** handed to the temporal engine (`observe`) so it sees the history.
  - A **decision-kind** event additionally triggers temporal evaluation, request construction, and the policy engine's decision, yielding `Some(Response)`.
  - A **history-only** event (a kind that is not a decision kind, e.g. `response`) yields `None`: it updates temporal state but produces no verdict.
  - **Evaluation failures do not abort:** a failure (a provider that errors, the temporal engine erroring, a decision event missing a principal/resource) is recorded in `Response::diagnostics().errors()`, and this reference implementation resolves it to `Deny`. Note that for provider errors specifically this is an implementation choice, not a guarantee — an erroring provider is undefined behavior under [the provider contract](05-information-providers.md#the-provider-contract).

```rust
impl AuthorizerBuilder {
    pub fn policy_engine(mut self, engine: impl PolicyEngine + 'static) -> Self;
    pub fn temporal_engine(mut self, engine: impl TemporalEngine + 'static) -> Self;
    pub fn build(self) -> Result<Authorizer, Error>;
}
```

- `policy_engine(engine)` — install the decision backend (e.g. a remote Cedar-based engine). Default `CedarPolicyEngine`.
- `temporal_engine(engine)` — install a custom temporal backend. Default `InMemoryTemporalEngine`.
- `build()` — runs each backend's `prepare` (the policy engine gets the lowered Cedar policies plus schema; the temporal engine gets the temporal leaves plus schema). It **errors if a backend's `prepare` fails** (e.g. a compiling temporal engine rejects a leaf, or a remote policy engine cannot reach its policy store). This is why `builder()` is fallible while `new()` is not.

```rust
impl Response {
    pub fn decision(&self) -> Decision;    // Allow or Deny
    pub fn diagnostics(&self) -> &Diagnostics;
    pub fn allowed(&self) -> bool;         // convenience: decision == Allow
}

impl Diagnostics {
    pub fn reason(&self) -> impl Iterator<Item = &DogwoodRuleRef>; // determining rules; empty for implicit Deny
    pub fn errors(&self) -> impl Iterator<Item = &str>;           // evaluation errors (degrade, not throw)
}
```

- `reason()` — the Dogwood rules that drove the decision. Empty for an implicit `Deny` (no rule matched), exactly as Cedar's `reason()` is.
- `errors()` — problems encountered while evaluating (missing attribute, provider that could not run, decision event with no principal/resource). Evaluation degrades rather than aborting, so these are reported here rather than thrown.

`DogwoodRuleRef` is the enriched analog of Cedar's `PolicyId` in `reason()`. Where Cedar names the lowered policy id, Dogwood maps it back to the originating `.dw` rule:

```rust
pub struct DogwoodRuleRef {
    pub rule_index: usize,       // 0-based index of the rule in the source policy set
    pub cedar_policy_id: String, // synthesized Cedar policy id, e.g. "policy0"
}
```

`Decision` is `pub use cedar_policy::Decision;` — re-exported so consumers need no direct `cedar-policy` dependency. Its values are `Decision::Allow` and `Decision::Deny`, and it is the type returned by `Response::decision()`.

---

## The engine seam

Why does the seam exist? A Dogwood `Authorizer` is really two decisions glued together: *what boolean does each temporal / provider leaf evaluate to right now* (the temporal seam), and *given those booleans folded into the context, does the Cedar policy allow the request* (the policy seam). Each of those has a built-in default, and each is a trait you can implement to replace it. That is how you point Dogwood at a **remote policy engine** for the final Cedar decision, or at an alternative **temporal engine** of your own for the history. You install a custom backend through the builder:

```rust
let mut authorizer = Authorizer::builder(policies)
    .policy_engine(my_remote_engine)     // decision seam
    .temporal_engine(my_temporal_engine) // temporal seam
    .build()?;                           // fallible: runs each backend's prepare()
```

You can swap either or both; anything you do not specify falls back to the default.

### The policy-decision seam (Cedar authorization-service shaped)

This trait is shaped like a Cedar authorization service's `IsAuthorized` (minus the token- and batch-authorization variants Dogwood does not use), so you can implement `PolicyEngine` by **calling a remote Cedar-based service instead of evaluating Cedar locally**.

```rust
pub struct AuthorizationRequest<'a> {
    pub request: &'a cedar_policy::Request,   // <principal, action, resource, context>
    pub entities: &'a cedar_policy::Entities, // Dogwood supplies an empty set; field exists so a
                                              // remote engine can forward its managed entities
}

pub struct AuthorizationDecision {
    pub decision: Decision,                   // Allow or Deny
    pub determining_policy_ids: Vec<String>,  // ids of determining policies (empty for implicit Deny)
    pub errors: Vec<String>,                  // evaluation errors (folded into diagnostics; Deny, not throw)
}

pub trait PolicyEngine: Send {
    fn prepare(&mut self, policies: &cedar_policy::PolicySet, schema: &cedar_policy::Schema) -> Result<(), Error>;
    fn is_authorized(&self, request: AuthorizationRequest<'_>) -> AuthorizationDecision;
}
```

`prepare` is called once at authorizer-build time (analogous to creating and populating a policy store); `is_authorized` decides one request. Implementations **must not panic** — surface problems through `AuthorizationDecision::errors` with a fail-closed `Deny`.

The built-in default is `CedarPolicyEngine` (implements `Default`, with `CedarPolicyEngine::new()`). Its `prepare` keeps the policy set; its `is_authorized` runs `cedar_policy::Authorizer::new().is_authorized(request, policies, entities)` and maps the decision, determining ids, and errors across. If it was never prepared it returns a `Deny` with an error string.

### The temporal-evaluation seam

This trait computes the boolean value of each hoisted `temporal { … }` leaf for the current decision point.

```rust
pub type ExtensionId = String;                          // the context.<id> slot a leaf's boolean binds into (e.g. "__temporal_0")
pub type TemporalBindings = BTreeMap<ExtensionId, bool>; // per-leaf booleans for one decision point

pub trait TemporalEngine: Send {
    fn prepare(&mut self, leaves: &[TemporalField], schema: &cedar_policy::Schema, events: &[EventSignature]) -> Result<(), Error>;
    fn observe(&mut self, event: &Event);
    fn evaluate(&mut self) -> Result<TemporalBindings, String>;
}
```

The lifecycle has three points:

- `prepare(leaves, schema, events)` — **once**, at authorizer-build time. A custom backend does its one-time setup here (an engine that precomputes queries against a store, say, would build them now); `events` carries the declared signature of every event kind the policy set can see (each field's dotted path and type), which such a backend needs to emit type-correct comparisons.
- `observe(event)` — for **every** ingested event (decision or history-only), in timestamp order, before any `evaluate` that includes it. A backend persists the event (in memory, or in an external store).
- `evaluate()` — at each decision point, **after** that point's event has been observed. It returns each leaf's boolean keyed by id. The in-memory backend re-runs the interpreter; a custom backend evaluates however it prepared. A failure (an external store being unreachable, say) **fails the decision closed** by returning `Err(String)`.

The built-in default is `InMemoryTemporalEngine` (implements `Default`, with `InMemoryTemporalEngine::new()`): it keeps the event history in memory and re-runs the in-process temporal interpreter over the trace so far. `prepare` stores the leaves (no compilation), `observe` appends to an in-memory log, and `evaluate` runs the interpreter at the last timepoint.

The leaves handed to `prepare` are `TemporalField`s:

```rust
pub struct TemporalField {
    pub id: ExtensionId,            // the context.<id> slot its boolean binds into
    pub action: ActionScope,        // the action scope its rule pins, as written
    pub target_actions: Vec<ActionRef>, // concrete actions `action` resolves to (a group to its
                                    // members, Unconstrained to all) — what the leaf is checked against
    pub principal: ScopeConstraint, // entity-type axis the rule's `principal` scope admits
    pub resource: ScopeConstraint,  // likewise for `resource`
    pub condition: Temporal,        // the parsed temporal condition
}
```

Supporting types a custom engine will name:

```rust
pub struct ActionRef {
    pub namespace: Option<String>, // None = top-level (unnamespaced) action
    pub id: String,
}

pub enum ActionScope {
    Concrete(ActionRef),           // action == Ns::Action::"X"
    List(Vec<ActionRef>),          // action in [ … ]
    Unconstrained,                 // bare `action` scope, may fire on any action
}
impl ActionScope {
    pub fn concrete(&self) -> Option<&ActionRef>;   // the single == action, else None
    pub fn actions_to_check(&self) -> &[ActionRef]; // one concrete / each listed; Unconstrained => empty slice
}

pub enum ScopeConstraint {
    Any,                 // bare `principal` / `resource`: every type the action permits
    IsType(String),      // `is Ns::T`
    Uid { .. },          // `== Ns::T::"x"` or `in Ns::T::"x"`
}

pub struct Temporal {
    pub condition: Condition, // parsed temporal condition; the Condition AST is public via `dogwood_language::temporal_ast`
    pub span: Span,           // span of the block body in the .dw source
}
impl Temporal {
    pub fn parse(body: &str, body_span: Span) -> Result<Temporal, String>;
}
```

A custom engine reads `TemporalField::condition` to decide what to evaluate; the in-memory engine interprets it directly. `Temporal` is re-exported so a custom engine can name the type, and its inner `condition` AST is public via `dogwood_language::temporal_ast` to walk.

The practical recipe for swapping either backend:

- **Swap the decision backend** (any Cedar-based store): implement `PolicyEngine` and pass it to `Authorizer::builder(policies).policy_engine(...)`. `PolicySet::as_cedar()` / `cedar_schema()` give you the Cedar policies and schema to load into the store.
- **Swap the temporal backend** (a custom evaluation strategy): implement `TemporalEngine` (`prepare` does one-time setup over `&[TemporalField]`, `observe` records each event, `evaluate` computes the leaves at the decision point) and pass it to `.temporal_engine(...)`.

---

## Trace replay

`parse_trace` and `replay_log` are conveniences over the core `Authorizer` loop for driving a recorded `.log` event trace — useful for regression testing and for reproducing a sequence of events without hand-building each `Event`.

```rust
pub fn parse_trace(log: &str) -> Result<Vec<Event>, Error>;
pub fn replay_log(policies: LoweredPolicySet, log: &str) -> Result<String, Error>;
```

- `parse_trace(log)` — parse a `.log` trace into its sequence of `Event`s. Each non-blank line is one timepoint of the form `@<ts> [envelopes] <Action>(<field>: <value>, …)` (the optional `scope` / `entities` / `request_context` envelopes are described below). Values use Cedar surface forms (entity refs `Ns::Type::"id"`, strings, integers, decimals, `true`/`false`, arrays, objects). Feed the events to an `Authorizer` in order to replay them. On failure it returns `Error::TraceParse("…")`.
- `replay_log(policies, log)` — replay a whole `.log` trace through `policies` and return the per-timepoint verdict stream: one `@<ts> (time point <i>): <bool>` line for **every decision point** (`true` for `Allow`, `false` for `Deny`), newline-joined. This is the corpus-comparison format. It **consumes** the `LoweredPolicySet` (it drives a fresh stateful `Authorizer`, so temporal leaves see prior events as history). History-only events (non-decision kinds) contribute **no line**.

```text
@0 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") Drupe::Action::"Login"::request(input: { user: "alice" })
@10 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") Drupe::Action::"Read"::request(input: { user: "alice" })
@7200 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") Drupe::Action::"Read"::request(input: { user: "alice" })
```

Each `.log` line is: the `@<timestamp>`, then up to three optional **request-supplement envelopes** in a fixed order, then the event itself — a **quoted, fully-qualified** action id (`Drupe::Action::"Read"`) with an explicit **`::<kind>`** segment (`::request`) and its trailing `(<field>: …)` group. That trailing group is the **logged** record (the temporal-history fields a predicate correlates on); the envelopes carry the request-only supplements, each parsed positionally when present:

- `scope(principal: …, resource: …)` — the request's principal and resource entities. (A decision-kind event omitting `scope(...)` has no principal/resource and fails closed to `Deny`.)
- `entities(<uid>: { <attr>: … }, …)` — the entity attribute store: each `uid` (e.g. `Drupe::OAuthUser::"alice"`) maps to its attributes, so a policy can read `principal.<attr>` / `resource.<attr>` or a provider can resolve one. A uid `"id"` containing `"` or `\` is escaped as in Cedar (`"a\"b"`).
- `request_context(<group>: { … }, …)` — the request-only context the Cedar request is built from (`input`, `system`, …), distinct from the trailing logged group. A field a policy reads via `context.<group>.<name>` must appear here; a field a temporal predicate correlates on must appear in the trailing logged group. A field both need (`input`) is supplied in both.

The envelopes appear in that order (`scope`, then `entities`, then `request_context`) before the event group, and any may be omitted. Parsing is **strict**: an unterminated envelope, or a **duplicate key** within any group (a repeated uid in `entities(...)`, a repeated group in `scope`/`request_context`, a repeated field in the logged group or a nested record), is a `TraceParse` error rather than a silent last-wins — so a hand-written trace cannot mis-decide on an accidental duplicate.

Running `replay_log` on the trace above (which uses only `scope(...)`) with the tour's policy produces one line per `request`-kind timepoint:

```text
@0 (time point 0): false
@10 (time point 1): true
@7200 (time point 2): false
```

— the same `[Deny, Allow, Deny]` shape you saw in the tutorial (`false`/`true` = `Deny`/`Allow`; note `replay_log` emits a line for *every* decision point, not only allows).

---

## MCP schema generation

Because a Dogwood action schema *is* an MCP tool manifest, you can generate the Cedar `.cedarschema` text directly from a Model Context Protocol `tools/list` payload rather than writing it by hand. The `PolicySchema::from_mcp_manifest` path is the usual entry point, but the underlying functions are also public:

```rust
pub const DRUPE_TEMPLATE: &str; // embedded Drupe .cedarschema template stub
pub fn mcp_to_cedar_schema(manifest_json: &str) -> Result<String, String>;
pub fn mcp_to_cedar_schema_with_template(manifest_json: &str, template: &str) -> Result<String, String>;
```

- `manifest_json` is an MCP `tools/list` payload (or a JSON array of tool descriptions).
- `mcp_to_cedar_schema` uses `DRUPE_TEMPLATE`; `mcp_to_cedar_schema_with_template` takes a caller-supplied template.
- The generator config matches the regression harness: `include_outputs(true)`, `encode_numbers_as_decimal(true)`, and `flatten_namespaces(true)` (so action names are unqualified).
- `DRUPE_TEMPLATE` supplies the principals (`OAuthUser` / `IamEntity` / `UnauthenticatedUser`), the `Gateway` resource, the `system` context, and the base MCP action hierarchy. The generator layers one Cedar action per MCP tool (with input/output context records) on top of the template.
- Note the return type: these return `Result<String, String>` (a plain error string), whereas the `PolicySchema::from_mcp_manifest` path wraps failure as `Error::McpSchema`.

For example, a manifest declaring `SellShares` / `ApproveSale` / `GetStockInfo` tools (each with `stock` / `shares` inputs) passed to `PolicySchema::from_mcp_manifest(MCP_MANIFEST)` layers them onto the Drupe template. See [Generating the action schema from an MCP manifest](11-mcp-schema-generation.md) for the manifest format, the JSON→Cedar type mapping, and the Drupe template in depth.

---

## Cedar export

To hand Dogwood's output to plain Cedar or to an external policy store, you use the `LoweredPolicySet` accessors together with the `dogwood_language::cedar` interop module.

The `dogwood_language::cedar` submodule re-exports exactly the `cedar_policy` types that appear in Dogwood's public API — `Entities`, `EntityUid`, `PolicySet`, `Request`, `Schema`. This lets a consumer name them (to implement a `PolicyEngine`, to read `PolicySet::as_cedar()` / `PolicySet::cedar_schema()`, or to bridge a `cedar::Request` via `Event::from_request`) **without** taking a direct, version-matched `cedar-policy` dependency of their own.

The export workflow is:

- `policies.as_cedar()` gives the lowered Cedar `PolicySet` — render it to policy text for a policy store's create-policy API, or evaluate it with the `cedar-policy` crate directly.
- `policies.cedar_schema()` gives the augmented Cedar `Schema` for a policy store's schema ingest or Cedar's validator.
- `policies.is_self_contained_cedar()` tells you whether that export is the whole story. When it is `true`, the exported Cedar reproduces the policy exactly and a policy store can decide standalone. When it is `false`, the policy uses `temporal { … }` and/or `guardrails { … }` leaves, so each authorization call must be supplied the hoisted `context.<id>` values — and computing those is Dogwood's job. In that split, **Dogwood produces the enriched context and the policy store performs the final Cedar decision** (the pattern a custom `PolicyEngine` follows).

A brief note on terminology you will meet at the boundary: the policy-level clause keyword an author writes for an information provider is `guardrails { … }`, and for a temporal expression it is `temporal { … }`. Internally the hoisted provider artifact is called a `ProviderField`, but the surface keyword is always `guardrails`. See [Information providers](05-information-providers.md).

---

## Errors

Dogwood has a **two-channel-plus-runtime** error model, and knowing which channel a problem lands in tells you where to look for it.

1. **Fatal — `Error`.** Returned by `ParsedPolicySet::parse` / `lower`, `LoweredPolicySet::from_str`, and `ServiceSchema`/`PolicySchema` construction. This is the fatal prefix: a syntax / macro / lowering / schema failure means there is nothing well-formed to validate or authorize.
2. **Findings — `ValidationResult`.** Returned by `Validator::validate`. The policy is well-formed but wrong against the schema (type errors, dialect-check failures). These do **not** appear in `Error`.
3. **Runtime.** During authorization, any evaluation failure is recorded in `Response::diagnostics().errors()` and resolved to `Deny` by this implementation — never thrown. (Provider errors specifically are undefined behavior under [the provider contract](05-information-providers.md#the-provider-contract); the deny is a tendency, not a guarantee.)

The construction error itself:

```rust
#[non_exhaustive]
pub enum Error {
    Parse(ParseErrors),                       // one or more syntax errors (self-rendering)
    Macro(MacroError),                        // def cedar / def temporal expansion failed
    Cedarify(CedarifyError),                  // lowering Dogwood -> Cedar failed
    PolicySet(Box<cedar_policy::PolicySetError>),   // Cedar could not assemble the policy set
    CedarSchema(Box<cedar_policy::CedarSchemaError>), // the augmented Cedar schema was invalid
    McpSchema(String),                        // MCP -> action schema generation failed
    TraceParse(String),                       // a `.log` trace failed to parse
    RequestMissingAction,                     // a Cedar Request had no action
    ContextRead(String),                      // reading a Request's context failed
    EventSchema(String),                      // event-schema DSL failed to parse / derive
    Leaf { id: String, message: String },     // a hoisted extension leaf failed to prepare
    InvalidDistincter(String),                // lower_with_distincter got a non-identifier
    SchemaSerialize(String),                  // rendering the augmented Cedar schema to text failed
    PartitioningUnsupported,                  // a pin-partitioning request the built-ins cannot honor
    // #[non_exhaustive]: more kinds may be added without a breaking change.
}
```

`Error` is a `#[derive(miette::Diagnostic)]`: the spanned variants (`Parse`, `Macro`, `Cedarify`) embed their `.dw` source and self-render, and `PolicySet` / `CedarSchema` forward Cedar's own diagnostic. `Parse` aggregates multiple `ParseError`s via `ParseErrors` (`.iter()` yields them all). Note again that **type errors against the schema are not in `Error`** — run `Validator::validate` to see those as `ValidationResult` findings.

---

## Event kinds, decisions, and failure handling

Two behaviors thread through the whole API and deserve to be stated plainly.

**Event kind is data, not convention.** The event schema marks certain kinds as `decision` (queryable on a lowered set via `LoweredPolicySet::decision_kinds()` / `is_decision_kind(kind)`). With the default event schema, `request` is a decision kind and `response` is history-only. From that single fact everything else follows:

- A **decision-kind event** makes `is_authorized` return `Some(Response)` — it observes the event *and* decides.
- A **history-only event** makes `is_authorized` return `None` — it observes the event to update temporal state but yields no verdict, and contributes no line in `replay_log`.
- **Statelessness is just a special case:** a single stateless decision is a fresh `Authorizer` fed one `request`-kind event (for example via `Event::from_request`).

**Authorization never aborts, and this implementation resolves evaluation failures to `Deny`.** Any evaluation failure — a provider that errors, the temporal engine erroring, a decision event missing a principal/resource, a policy engine that was never prepared — yields a `Deny` with the reason recorded in `Response::diagnostics().errors()`. (For provider errors this deny is a description of this implementation, not a semantic guarantee: an erroring provider is undefined behavior under [the provider contract](05-information-providers.md#the-provider-contract), so a policy set must never rely on deny-on-error.) The temporal seam's `evaluate` returning `Err` and the policy seam's `errors` vector both funnel into this same place. So a caller that wants to distinguish "denied by policy" from "denied because something broke" should always inspect `diagnostics().errors()`, not just `decision()`.

Finally, the three policy-clause forms map cleanly onto the seams, which is a useful mental model when reading a policy:

- `when { … }` — a plain Cedar condition, decided by the `PolicyEngine`.
- `when temporal { … }` — hoisted to a `TemporalField` and evaluated by the `TemporalEngine` (not self-contained Cedar). See [Temporal expressions](04-temporal-expressions.md).
- `when guardrails { … }` — an information-provider invocation, evaluated from `ProviderDeclarations` (not self-contained Cedar). See [Information providers](05-information-providers.md).

---

## See also

- [Introduction](00-introduction.md) — what Dogwood is and why it exists.
- [Getting started](01-getting-started.md) — installing the crate and a first end-to-end run.
- [Policy language](02-policy-language.md) — the `permit`/`forbid` surface syntax, `when` clauses, and the action schema.
- [The event schema](03-event-schema.md) — the event-schema DSL and how decision kinds are declared.
- [Temporal expressions](04-temporal-expressions.md) — `formerly`, `previous`, `since`, aggregation, and what the `TemporalEngine` evaluates.
- [Information providers](05-information-providers.md) — calling providers; [The provider schema](10-provider-schema.md) — `ProviderDeclarations` and the Rhai contract.
- [Macros](06-macros.md) — `def cedar` / `def temporal` and the macro library merged at lowering time.
- [Generating the action schema from an MCP manifest](11-mcp-schema-generation.md) — the manifest format behind `from_mcp_manifest`.
