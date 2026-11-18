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
// The event's `input` goes to its logged record (`field`, what temporal
// predicates correlate on) and to its request context (`request_context`,
// what the policy reads as `context.input`).
let event = Event::builder("Drupe::Action::Read", "request")
    .principal("Drupe::OAuthUser::\"alice\"")
    .resource("Drupe::Gateway::\"gw1\"")
    .field("input", "document", Value::String("report".to_string()))
    .request_context("input", "document", Value::String("report".to_string()))
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

## Syntax tooling

The [`syntax`] module is the canonical parser-backed syntax interface for
complete `.dw` policies and `.dwschema` event schemas. It walks the policy,
temporal, and event-schema Pest grammars owned by this crate and returns
editor-neutral UTF-8 byte ranges. Tools such as `dogwood-lsp` map these spans
to protocol tokens; they do not copy or reinterpret Dogwood grammar.

Use [`syntax::policy_spans`] or [`syntax::event_schema_spans`] only for
structural classification. Continue to use the normal parse and validation
APIs for authoritative diagnostics.

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
  `PolicySchema::from_mcp_manifest` (feature `mcp-schema`).

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
and output fields as the request context. This requires the off-by-default
`mcp-schema` feature:

```toml
dogwood-language = { version = "1.2", features = ["mcp-schema"] }
```

Then use the `PolicySchema::from_mcp_manifest` shortcut (layered on the
built-in Drupe template):

```rust,ignore
let policy_schema = PolicySchema::from_mcp_manifest(mcp_tools_json)?;
```

To supply your own template stub instead of Drupe, use
`PolicySchema::from_mcp_manifest_with_template`. (The lower-level
`mcp_to_cedar_schema` function is also available if you want the generated
`.cedarschema` text directly.)

## Events and the authorizer

An [`Authorizer`] is **stateful**. You build it once from a
[`LoweredPolicySet`] and then feed it [`Event`]s one at a time with
[`is_authorized`](Authorizer::is_authorized);
each event is folded into an accumulated history so that temporal predicates
can look back over earlier events.

Event timestamps are assumed to be **increasing** in ingestion order:
each must be greater than the previous one, so timestamps are also unique.
The authorizer uses ingestion order for trace positions and timestamps for
temporal windows; it neither sorts events nor checks the timestamp assumption.

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

An event must conform to the schemas. Its logged record must be an instance of
its event's signature, and a decision's request context an instance of its
action's context record type. An event that does not conform is not ingested,
so no later decision sees it: [`Authorizer::submit`] reports a nonconforming
history event as a [`Rejection`], and a nonconforming decision event's
decision fails closed.

A [`Response`] carries the [`decision`](Response::decision)
(`Allow` / `Deny`) and [`diagnostics`](Response::diagnostics): the Dogwood
rules that determined the decision ([`reason`](Diagnostics::reason)) and any
evaluation errors ([`errors`](Diagnostics::errors)). Evaluation is
**fail-closed** — if a provider or guard cannot be evaluated, or the data a
decision reads does not conform to the schemas, the decision degrades to `Deny`
with the error recorded in the diagnostics, never a spurious `Allow`.

For a single one-off decision, a fresh `Authorizer` fed one `request`-kind
event is all you need — there is simply no prior history.

## Identifying policies

By default rule `k` is named by its position (`policy_<k>`), and a position
names a different rule once the set is reordered. **Stable ids are opt-in and
additive**: choose an [`IdSource`] with [`ParsedPolicySet::with_ids`] —
each policy's `@id("…")` ([`IdSource::Annotation`]) or ids you supply
([`IdSource::Explicit`]) — and lowering emits each rule under its stable id
(`<distincter>/<id>` under a distincter). Missing, invalid and duplicate ids
are rejected ([`Error::PolicyId`]).

```rust,ignore
let parsed = ParsedPolicySet::parse(src, &service)?.with_ids(IdSource::Annotation)?;
let mut authorizer = Authorizer::new(parsed.lower(&policy_schema)?);
if let Some(response) = authorizer.is_authorized(&event) {
    for p in response.diagnostics().determining() {
        println!("supported by {} (revision {})", p.id(), p.revision());
    }
    let version = response.policy_set().expect("stable ids carry a version");
    println!("policy set generation {} hash {}", version.generation(), version.hash());
}
```

Each supporting policy is a [`PolicyRef`]: its id and a **revision**, a hash of
the canonical lowered rule that ignores positions, formatting, comments and
annotations, so it changes exactly on a semantic edit. Each response names the
[`PolicySetVersion`] it was decided under
([`Response::policy_set`]), and [`Authorizer::update_policies`] replaces the
policy set live, keeping the temporal history. With stable ids, a determining
id the policy engine reports that the set does not contain fails the decision
closed. The hoisted `context.<id>` field names are unchanged, and everything
stays as it was for a caller that does not opt in; see the guide's API chapter
(*Stable policy identity*) for the details and the migration of each consumer.

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

Any backend can also **slice** its per-decision work with [`DecisionLeafMap`],
which answers one question: *which temporal leaves can this decision read?* A
leaf outside that answer is read by no applicable rule, so reporting it `false`
cannot change the decision — and the question is answered once per policy set
rather than once per decision. Build the map in `prepare` from the same `leaves`
and `schema` ([`DecisionLeafMap::build`]), probe it in `evaluate` with the
decision's event ([`needed_for`](DecisionLeafMap::needed_for)), and bind every
installed leaf — the skipped ones `false`.

Two properties make it safe to consume: **any miss means compute every leaf**
(there is no "needs nothing" answer), and **the answer may only shrink across
versions** — the slicing may get finer, never coarser, so a backend needs no
change when it does. Today the map is keyed by the request's action.

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

## The Lean frontend (feature `lean-frontend`)

The **frontend** is everything after the parsers: macro expansion, event-schema
derivation, lowering to Cedar, schema augmentation, pin injection,
relativization, provider resolution, stable ids and identity hashes, and
validation. Besides its Rust frontend, the repository holds a port of the
frontend to Lean 4 (`dogwood-lean/Dogwood/Frontend/`), whose validator is
proved to decide the formal specification's validity and which is tested
against the Rust frontend. The crate can link it and use it instead of the
Rust frontend, or alongside it.

It is **opt-in**. By default the crate builds and runs only its Rust frontend
and needs no Lean toolchain. With the `lean-frontend` feature, the build links
the Lean frontend, and a [`ServiceSchema`] selects the frontend that lowers and
validates the policy sets parsed against it:

```rust,ignore
use dogwood_language::{Frontend, OnMismatch, ServiceSchema};

let lean = ServiceSchema::builder().frontend(Frontend::Lean).build()?;
let both = ServiceSchema::builder()
    .frontend(Frontend::Shadow(OnMismatch::Fail))
    .build()?;
```

- [`Frontend::Rust`] (the default, with or without the feature) is the Rust
  frontend.
- [`Frontend::Lean`] sends the parsers' outputs to the Lean frontend and
  rebuilds the [`LoweredPolicySet`] from its result: the Cedar policies (with
  Cedar's own constructors), the augmented schema (compiled by Cedar), the
  temporal and provider leaves, the event schema, partition keys, decision
  kinds, rule ids and revisions, and the version hash.
- [`Frontend::Shadow`] runs both and compares every observable of the lowered
  set (the Cedar policies, the augmented schema's JSON, the three forms of each
  temporal leaf with their spans, the provider leaves, the event schema, the
  partition keys, decision kinds, rule ids, spans and revisions, the version
  hash, the context reads), the lowering error when both reject the set (its
  kind, message and span; Cedar's own errors by kind), the stable ids, and the
  validator's findings. Findings are compared as the Lean validator's
  correctness claim states their agreement: whether the set validates, the
  categories of the error findings, and their dialect codes; with
  `DOGWOOD_SHADOW_FINDINGS=messages` the messages of the findings other than
  Cedar's are compared too. On agreement it returns the Rust frontend's result.
  On a difference, [`OnMismatch::Fail`] (the default) returns [`Error::Frontend`]
  naming the first difference (from validation, an error finding with code
  `frontend`), and [`OnMismatch::Log`] writes it to standard error and returns
  the Rust result. A difference in an **identity value** of a set both
  frontends lower (a rule's id or revision, whether the ids are stable, the
  version hash, a temporal leaf's content hash, as each frontend computes it)
  is a panic under `Fail`: these values key what is stored about a policy set,
  and a caller that tolerates lowering errors (a fuzz harness, say) would take
  a `Mismatch` error for an input the crate rejects. Such a caller still does
  not see the other differences under `Fail`; run with `Log` to see every one.

The selection covers [`ParsedPolicySet::lower`],
[`lower_with_distincter`](ParsedPolicySet::lower_with_distincter),
[`lower_many`], [`ParsedPolicySet::with_ids`], the one-call
[`LoweredPolicySet::from_str`] / [`from_many_str`](LoweredPolicySet::from_many_str),
and [`Validator::validate`], which validates a set with the frontend that
lowered it. [`ParsedPolicySet::parse`] is the Rust parser and expander in every
mode (the pre-lowering diagnostics of a [`ParsedPolicy`] read its result); the
Lean frontend redoes the expansion from the parser's output when it lowers.

Without the feature, [`Frontend`] and the builder option still exist, so that
code selecting a frontend compiles in every build, but only `Rust` is
available: [`ServiceSchemaBuilder::build`] rejects the others with
[`Error::Frontend`] rather than run another frontend than the one asked for.

**The `DOGWOOD_FRONTEND` environment variable.** With the feature, a service
schema built without an explicit choice (and [`ServiceSchema::defaults`]) takes
its frontend from `DOGWOOD_FRONTEND`: `rust`, `lean`, `shadow` or `shadow-log`;
unset is `rust`, and any other value panics. So the whole test suite runs in
each mode unchanged, e.g. `DOGWOOD_FRONTEND=shadow cargo test --features
lean-frontend`. Without the feature the variable is not read.

**What differs in `Lean` mode.** The Lean frontend computes what the Rust one
does, with the same messages for its own findings (the temporal and provider
dialects', the context reads', the schema's), but some results take another
form:

- Cedar's part of validation is cedar-lean's validator: one `cedar` finding
  with cedar-lean's text for the first error in a rule Cedar rejects, where
  Cedar's Rust validator reports each error with its own message (an impossible
  policy reads as Cedar's Rust validator reports it); Cedar's Rust-only
  warnings (on identifiers and strings) are not reported;
- a finding's span is its rule's, for Cedar's (where the Rust frontend has the
  span of the subexpression Cedar's diagnostic labels), and its leaf's, for a
  temporal leaf's (where the Rust frontend has the span of the offending node in
  the leaf); a provider leaf's findings, the context reads' and the schema's
  have the Rust frontend's spans, and every finding renders against the source
  of its rule's policy set;
- the lowered Cedar policies carry no source locations;
- Cedar's errors are Cedar's own: a schema Cedar rejects is
  [`Error::CedarSchema`], from Cedar's compilation of the Lean frontend's
  augmented schema, and two entries of [`lower_many`] minting one policy id is
  [`Error::PolicySet`], from Cedar's policy set; an error the crate has no
  variant to carry (none arises from the crate's own inputs) is
  [`Error::Frontend`] with kind [`FrontendErrorKind::Lean`];
- the Lean validator runs when the set is lowered, and
  [`Validator::validate`] reports its findings.

Strings, ids, patterns and provider arguments are printed (in the rules'
text, and so in the revisions and the version hash, and in the messages) as
Rust's `escape_debug` and `{:?}` print them, with the Unicode tables of the
Rust release the crate builds with, Rust 1.98.1:
`dogwood-lean/scripts/gen_unicode_tables.py` generates them from the
toolchain's sources, pinned to that release (`RUST_VERSION`, recorded in the
tables' file), and checks them against the toolchain (`--verify`). With the
feature, the build script warns when the compiler is another release than the
tables'; after a toolchain upgrade that changes what `escape_debug` escapes,
the crate's test `escaping_agrees_at_every_boundary_of_the_unicode_tables`
fails, naming both releases, until they are regenerated — unless
`src/lean_frontend/escape_changes.txt` (from the script's `--changes`) lists
the two releases: then the test leaves out the characters they escape
differently, checks that the compiler escapes those as the file says, and
warns.

**Testing in Lean mode.** `scripts/test-lean-mode.sh` runs the whole test suite
with `DOGWOOD_FRONTEND=lean` and fails unless the failing tests are exactly
those `tests/lean-mode-expected.txt` lists: the tests that read the wording or
the span of Cedar's own diagnostics, the span of a finding inside a temporal
leaf, or the source locations of the lowered Cedar policies. Each line names
the test and the reason. In `shadow` mode the whole suite passes.

**Building with the feature** needs a prebuilt archive, or Lean 4.34.0 (the
version `dogwood-lean/lean-toolchain` pins; elan selects it) and the
`dogwood-lean` sources of the repository. The archive sits next to its
manifest, `libdogwood_lean_frontend.link`, which records the SHA-256 digests of
the sources it was built from, of the archive file, of the crate's side of the
bridge (`build.rs` and `src/lean_frontend/`) and of the built Lean packages, and
the Lean version. The build script:

- links a prebuilt archive when there is one it can use: the
  `libdogwood_lean_frontend.a` that `DOGWOOD_LEAN_PREBUILT` names (which must
  be usable, or the build fails), else one found on `PATH`, as
  `<dir>/../lib/libdogwood_lean_frontend.a` for a `<dir>` on `PATH`, in the
  package's own published `lib/` or a library farm's copy of it (`build.rs` says
  exactly where; any other is ignored). An archive is usable when its Lean
  version is this crate's, its digest the manifest's, and the manifest's source
  digest that of the Lean sources, when they are present, or else (a crate
  fetched from a registry has none) its bridge digest this crate's. This route
  runs neither Lean nor Lake and needs neither the Lean sources nor network
  access. A build from source's `$OUT_DIR` is itself a prebuilt directory: it
  holds the archive, the manifest, the built Lean packages (`dogwood-lean/`,
  which the manifest lists) and the list of the packages' files
  (`libdogwood_lean_frontend.files`), which a packaging step publishes, the
  packages when dependents are to compile Lean code against them;
- otherwise (or with `DOGWOOD_LEAN_FROM_SOURCE=1`) builds it from the sources
  at `DOGWOOD_LEAN_SOURCE` (default `../dogwood-lean`): it copies them into
  `$OUT_DIR` with their dependencies (cedar-lean, Batteries): the sources in
  `dogwood-lean/.lake/packages` when present, else `dogwood-lean/vendor/`, a
  pinned export of exactly the modules the frontend's library and the whole
  specification import (each the
  upstream file, Apache-2.0, with its license; `vendor/MANIFEST` records every
  file's digest, which the build checks, and
  `dogwood-lean/scripts/vendor_deps.py` writes and checks the export), so that
  Lake fetches nothing; runs `lake build frontendFfi`; and merges the Lean
  frontend's library, Lean's `Init` and `Std` libraries (whole), the parts of
  Lean's `Lean` library and of the Lean kernel they reach, the Lean runtime, and
  their static dependencies into one archive. A dependency configured in
  `lakefile.toml` (Batteries) is given the equivalent `lakefile.lean`, with which
  it is built, so that every package root has one;
- finds the toolchain with `LEAN_SYSROOT`, else `lean --print-prefix` (its
  headers in `include/`, or `stage1/include/`); compiles Lean's generated C with
  `LEAN_CC`, else the C compiler the `cc` crate selects, archives with
  `LEAN_AR`, else the `cc` crate's archiver, and runs `LAKE`, else the
  toolchain's `lake`. The static C++, GMP and libuv libraries of an upstream
  toolchain go into the archive; a toolchain built against the system's C++
  library, GMP, libuv and mimalloc takes their static archives from
  `DOGWOOD_LEAN_EXTRA_ARCHIVES` (colon-separated paths), whose members the
  runtime reaches go into the archive; without them it is linked against the
  shared libraries, searched in `DOGWOOD_LEAN_LINK_SEARCH` (colon-separated) and
  the toolchain's `lib` directories. Either of the first two needs nothing at
  run time beyond the system's libc, `libpthread`, `libdl`, `librt` and `libm`.

The archive is about 210 MB: on Linux it is one relocatable object of the shim,
the frontend's library, Lean's runtime and standard library, and the members of
Lean's other libraries they reach. The frontend's library leaves out Batteries'
tactics, linters and code actions, which the frontend never runs (cedar-lean's
data modules import them for their proofs), and with them Lean's elaborator, so
a binary that links the archive holds about 7 MB of Lean code (stripped). The
build script's documentation (`build.rs`) has the details.

**Linking Lean code of your own.** With the feature, the crate's archive is the
process's one Lean runtime, and holds the Lean frontend's library
(`Dogwood/Frontend/Library.lean` and what it imports). A crate that depends on
this one directly can compile Lean modules of its own against that library and
link them into the same process:

- The crate declares `links = "dogwood_lean"`. Its build script prints
  `lean=1`, `LEAN_VERSION` (`4.34.0`), `SOURCE_SHA256` (the digest of the Lean
  sources the library was built from), `TOOLCHAIN` (the toolchain's prefix),
  `PACKAGES` (`DogwoodSpec=<dir>;Cedar=<dir>;batteries=<dir>`, the built Lake
  packages) and, from source, `CC` and `AR`; a dependent's build script reads
  them as `DEP_DOGWOOD_LEAN_<KEY>`. Without the feature it prints `lean=0`
  alone. From a prebuilt archive, `TOOLCHAIN` is `LEAN_SYSROOT` (else empty),
  and `PACKAGES` the packages the manifest lists, when they are there and their
  files have the manifest's digest, copied into `$OUT_DIR` (Lake writes a lock
  file into a package it loads, and a published directory may be read-only),
  else empty. Only the toolchain that built the packages reads their `.olean`
  files, so a dependent compiles against them with that toolchain.
- The dependent requires the packages by path from a Lake project of its own,
  builds its own modules only (Lake finds the library up to date), and links
  their archive, which holds no Lean runtime and no module of the library.
  Its modules may import any module of the library, of `Init` and of `Std`.
  The final link must collect unreferenced sections (`--gc-sections`, as rustc
  links executables unless `-C link-dead-code`): the library keeps one
  unreached reference into a left-out module of Batteries. A prebuilt archive
  of the dependent records the `SOURCE_SHA256` it was compiled against.
- The crate owns the runtime: `dogwood_lean_init()` (idempotent, thread-safe, 0
  on success) initializes the runtime, restores the host's signal handlers,
  initializes every module of the library and ends Lean's initialization, once;
  `dogwood_lean_thread_enter()` and `dogwood_lean_thread_exit()` register a
  thread with Lean, counting nested registrations. A dependent calls
  `dogwood_lean_init` first, then initializes its own root module once, on a
  registered thread, and runs Lean code on registered threads only. The
  [`frontend`] module's documentation states the contract in full.
- To lower with its own Lean code, a dependent sends
  `frontend_export::inputs` (feature `frontend-export`: the parsers' outputs,
  exactly the Lean frontend's input, with no frontend stage run) to its
  module, which calls the library's pipeline and hands back the lowered set's
  Cedar part as Cedar prints it (`Full.cedar`); `frontend_export::cedar_policy_set`
  and `cedar_schema` build the Cedar policy set (with ids and annotations) and
  the augmented schema from it, as the crate does for its own Lean mode, which
  builds the policies from their policy JSON and does not re-parse their text.
  Shadow mode checks that the Lean frontend's printed policy JSON, text and
  schema JSON are Cedar's printing of the Rust frontend's set.
- To have the crate's whole [`LoweredPolicySet`] of its own Lean run, a
  dependent's module hands back the pipeline's outcome as the library encodes
  it (`Driver.outcomeToJson`: the lowered set and the validator's findings, or
  the error), or the lowered set alone (`Full.toJson`), and
  `frontend::lowered_from_lean` (with the feature) builds the set from it, as the crate builds
  the set of its own Lean mode, with no Rust lowering: the Cedar policies and
  schema, the leaves, the event schema, the ids and the identity hashes. Every
  method of the set works on it
  ([`check_event_conformance`](LoweredPolicySet::check_event_conformance), an
  [`Authorizer`], [`Validator::validate`], which reports the Lean validator's
  findings when the outcome carries them); a rejection is the crate's error, as
  the crate's Lean mode returns it.

`dogwood-language/lean-dependent` (not published) is such a dependent: `cargo
test -p dogwood-lean-dependent --features lean` compiles a Lean module against
the library, and calls it and the crate's Lean frontend from several threads in
one process, and checks that the sets `frontend::lowered_from_lean` builds from
the module's own runs of the pipeline are the crate's Lean mode's.
