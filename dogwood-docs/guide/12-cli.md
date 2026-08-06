# The command line

The `dogwood` CLI runs the whole Dogwood pipeline — parse, macro expansion,
lowering, type-checking, and stateful replay — over plain files. It is the
quickest way to check a policy or watch a temporal policy decide across an event
trace, and it needs no Rust: everything is a file in, a verdict (or a
diagnostic) out.

Every policy-level example in this guide is a complete, runnable **bundle** in
this crate's `examples/` directory, and a test harness runs each one through
this exact CLI on every build. So the commands below are not illustrative — they
are what checks the documentation.

## The two schema halves

A Dogwood schema comes in two parts, and the CLI mirrors that split:

- **The action schema** — a Cedar `.cedarschema` declaring entities, actions,
  and each action's `context` shape. Required wherever a schema is needed;
  passed with `--policy-schema`.
- **The service schema** — the event schema, information-provider declarations,
  and macro library. All optional; each defaults sensibly. Supplied with
  `--event-schema`, `--providers`, and `--macros` when a policy needs a
  non-default one.

See [The policy language](02-policy-language.md) for the action schema, and
[The event schema](03-event-schema.md) / [The provider schema](10-provider-schema.md)
/ [Macros](06-macros.md) for the service-side pieces.

## Commands

Every command takes the policy set as a positional argument (a `.dw` file, or
`-` to read stdin) and `--format human|json` (human is the default; JSON is the
stable machine shape). Exit codes are uniform: **0** success, **1** a usage or
I/O error (a missing file, a bad flag), **2** rejected input (a policy, schema,
or trace that does not check out). That `0` vs `2` split lets a CI job tell "the
tool broke" from "the policy was rejected".

### `validate`

```text
dogwood validate policy.dw --policy-schema schema.cedarschema \
    [--event-schema events.dwschema] [--providers providers.json] [--macros macros.dw]
```

Parses, lowers against the schema, and type-checks in one shot — the two error
classes (syntax/macro/lowering failures, and schema-aware type errors) are both
covered, so a clean `validate` means the policy is fully accepted. On success it
prints `OK: validation passed …` and exits 0; on rejection it prints each
finding as an underlined source snippet pointing at the offending `.dw` span and
exits 2.

```text
$ dogwood validate examples/write_after_read/policy.dw \
    --policy-schema examples/write_after_read/schema.cedarschema
OK: validation passed with no errors or warnings.
```

Add `--format json` for findings as structured data (each with a `message` and a
byte-offset `labels` span) instead of rendered snippets — the form a CI job or
an editor integration wants.

**`--providers` and `scriptFile`: inline your Rhai for CLI use.** A
`providers.json` `implementation` carries its Rhai two ways: inline
**`script`** (source as a JSON string) or **`scriptFile`** (a path to an
external `.rhai`, resolved relative to the declarations file). The CLI reads
`--providers` **as text**, so a `scriptFile` reference is never resolved:
`validate` and `lower` still work (they don't evaluate providers), but
`replay` fails at every provider evaluation with *"rhai implementation has no
script."* When a bundle will be driven through the CLI, put the Rhai inline
under `implementation.script` — every runnable bundle in
[`examples/`](../examples/) does exactly this. (Library callers are
unaffected: load with `ProviderDeclarations::from_json_file`, which folds
`scriptFile` contents in. An `implementation`-less, interface-only declaration
validates and lowers through the CLI too, but `replay` cannot evaluate it —
its value comes from your code via a `ProviderResolver`.)

### `replay` — watch a temporal policy decide

Validation proves a policy is *legal*; `replay` shows what it *does*. It feeds a
whole event trace through a stateful authorizer, so temporal operators see the
accumulated history, and prints one verdict per decision point:

```text
dogwood replay policy.dw --policy-schema schema.cedarschema --trace trace.log
```

```text
$ dogwood replay examples/write_after_read/policy.dw \
    --policy-schema examples/write_after_read/schema.cedarschema \
    --trace examples/write_after_read/trace.log
@0 (time point 0): DENY
@100 (time point 1): ALLOW  [rules: 0]
@5000 (time point 2): DENY
```

Each line is `@<timestamp> (time point <index>): ALLOW|DENY`, optionally followed
by `[rules: …]` — the indices of the `.dw` rules that determined the decision.
History-only events (a non-decision event kind) update the history but produce
no line. This is the way to catch a policy that validates but does
not *mean* what you intended — a mis-pinned "same user" correlation, or a window
that is too narrow. `--format json` emits a structured verdict stream.

A trace is one event per line. The events in `examples/write_after_read/trace.log`
look like:

```text
@0 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: { shares: 5, stock: "AMZN" }) Drupe::Action::"ApproveSale"::request(input: { shares: 5, stock: "AMZN" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw1", requestId: "u1")
```

— a timestamp, optional request envelopes (`scope(...)`, and here
`request_context(...)` — the context the Cedar request is built from), and the
fully-qualified action with its explicit `::request` (or other) kind and its logged
`input` record. See
[The event schema](03-event-schema.md) for the event model.

### `lower` — see the generated Cedar

```text
dogwood lower policy.dw --policy-schema schema.cedarschema --emit both
```

Lowers the `.dw` to Cedar and emits the artifacts: the Cedar policies, the
augmented action schema (with the hoisted `context.*` fields Dogwood adds for
temporal leaves and providers), or — with `--emit cedar-json` — the schema as
Cedar JSON (suitable for any Cedar-based policy store). `--emit` is one of
`cedar-policies`, `cedar-schema`, `cedar-json`, or `both` (the default). When the
lowered Cedar is not self-contained — because temporal or provider fields were
hoisted and need Dogwood at authorize time — `lower` says so on stderr.

### `check-parse` — syntax only

```text
dogwood check-parse policy.dw
```

Parses and macro-expands, reporting only syntax and macro errors — no schema
required. Useful as a fast first pass, or when you do not yet have the action
schema. It reports each policy's temporal-leaf and provider-call counts, and
flags any provider a policy calls that the service schema does not declare.

### `schema` — check a schema part on its own

```text
dogwood schema action    schema.cedarschema
dogwood schema event     events.dwschema
dogwood schema providers providers.json
```

Each checks one schema artifact in isolation — that it parses and is
well-formed — so you can tell "my schema is broken" from "my policy is broken"
before running `validate`. `dogwood schema mcp --manifest tools.json` generates a
Cedar action schema from an MCP tool manifest (see
[MCP schema generation](11-mcp-schema-generation.md)).

## Pipelines and stdin

`-` reads stdin or writes stdout, so commands compose. To lower a policy and
hand the Cedar straight to Cedar's own tooling:

```text
dogwood lower policy.dw --policy-schema schema.cedarschema --emit cedar-policies | cedar validate ...
```

## When to reach for the library instead

The CLI covers checking and replaying policies over files. When you need to
*embed* the engine — build events programmatically, feed them one at a time,
read each `Response`, or replace the policy or temporal engine with your own
— use the Rust API instead. See [The API and workflow](07-api-and-workflow.md).
