# The Dogwood Guide

Complete documentation for the Dogwood policy language — its syntax, its
temporal expressions and information providers, its schemas, and the Rust API
for evaluating policies.

The guide is organized so the **core language** comes first, read through the lens
of a fixed setup: the event schema, the information providers, and the macro
library are all taken as *given*. The **Advanced topics** section then covers how
each of those fixed inputs is built.

## A. Introduction to the language

The core language, assuming the event schema, providers, and macros are given.

- **[Introduction](00-introduction.md)** — what Dogwood is, the problem it solves,
  and the concepts you need. Read this first if you are new.
- **[Getting started](01-getting-started.md)** — your first schema, policy, and
  authorization, end to end, with runnable code.
- **[The policy language](02-policy-language.md)** — the core (Cedar-derived)
  syntax: the **action schema** (entity/action declarations and the
  `context.input` / `context.output` convention), `permit`/`forbid`, the
  `(principal, action, resource)` scope, `when`/`unless` conditions, and the full
  expression language.
- **[Temporal expressions](04-temporal-expressions.md)** — the
  `when temporal { … }` sublanguage: reasoning about event history with
  `formerly`, `previous`, `since`, windows, `exists`, `tp`, and the `count` /
  `sum` aggregations.
- **[Information providers](05-information-providers.md)** — consulting values
  computed on demand: calling a provider as a plain Cedar call inside an ordinary
  `when { … }` clause, and how its output composes with a condition.
- **[Calling macros](09-calling-macros.md)** — invoking `def cedar` and
  `def temporal` macros: where a call may appear and what shape its arguments take.

## B. Advanced topics

Deep dives on the three fixed inputs the core language takes as given, plus MCP
schema generation.

- **[The event schema](03-event-schema.md)** — the event-schema DSL (`.dwschema`):
  the four selectors, spreads, named fields, nested records, pins, decision kinds,
  and the default request/response schema.
- **[The provider schema](10-provider-schema.md)** — declaring providers: the
  `providers.json` format, the Rhai implementation contract (sandbox, host
  functions, decimal, the `net` feature), output methods, no-implementation
  providers, and the `guardrails { … }` sugar.
- **[Macros](06-macros.md)** — defining macros: `def cedar` / `def temporal`, the
  two parameter sigils, hygiene, every rejection rule, and the macro library.
- **[Generating the action schema from an MCP manifest](11-mcp-schema-generation.md)**
  — a Dogwood action schema *is* an MCP tool manifest; the manifest format, the
  JSON→Cedar type mapping, and the Drupe template.

## C. Running Dogwood

- **[The command line](12-cli.md)** — the `dogwood` CLI: `validate`, `replay`,
  `lower`, `check-parse`, and the `schema` subcommands, driven over plain files.
  The quickest way to check a policy or watch a temporal policy decide across a
  trace, with no Rust.
- **[The API and workflow](07-api-and-workflow.md)** — the Rust API reference and
  end-to-end workflow: `ServiceSchema`/`PolicySchema` → `LoweredPolicySet` →
  `Validator` → `Authorizer` → `Event` → `Response`.

## D. Reference

- **[Formal specification](08-formal-specification.md)** — the precise reference:
  the grammars in BNF, the abstract syntax, and the lowering / validation /
  authorization rules, each cross-referenced to its source of record.

## Runnable examples

Every policy-level example in this guide is a complete, runnable **bundle**
under this crate's [`examples/`](../examples/) directory — a `policy.dw`, its
`schema.cedarschema`, and (for history-dependent examples) a `trace.log` plus
the expected verdict stream, along with any `providers.json` / `macros.dw` /
event schema the example needs. A test harness checks every bundle on each
build (validating each policy, and replaying traces against the expected
verdict stream), so a guide example that stops parsing, validating, or
replaying as written is a build failure. To run one yourself, see
[The command line](12-cli.md).

To *embed* the engine rather than drive it over files — building events
programmatically and feeding them one at a time to a stateful `Authorizer` —
use the Rust API, walked through end to end in
[The API and workflow](07-api-and-workflow.md).

## Reading order

If you read straight through, this order builds naturally:

1. [Introduction](00-introduction.md)
2. [Getting started](01-getting-started.md)
3. [The policy language](02-policy-language.md)
4. [Temporal expressions](04-temporal-expressions.md)
5. [Information providers](05-information-providers.md)
6. [Calling macros](09-calling-macros.md)

Then reach into the Advanced topics as you need them:
[the event schema](03-event-schema.md), [the provider schema](10-provider-schema.md),
[macros](06-macros.md), and [MCP schema generation](11-mcp-schema-generation.md).
Integrate from Rust with [The API and workflow](07-api-and-workflow.md), and
consult the [Formal specification](08-formal-specification.md) as the reference.
