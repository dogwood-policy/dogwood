# Dogwood Language — Release Notes

Release notes for the Dogwood policy language reference interpreter.

## [1.2.0] (2026-11-18)

### Summary

This release adds a formal specification of Dogwood in Lean, the `dogwood-ops`
crate, the `dogwood-lsp` language server and Verus proofs about the checks on
`exists` binders and aggregation `for` lists.

The authorizer and the validator also check each input against its
declaration. Policies and schemas that 1.1.2 accepted despite a mismatch can
fail validation or fail to load (see Fixed), and the authorizer can deny
requests and drop events that 1.1.2 accepted (see Breaking changes).

Some verdicts change, with no error, for input that both versions accept. The
release also requires Cedar 4.14.0, moves MCP schema generation behind the
`mcp-schema` Cargo feature, and adds the `max_horizon` event-schema directive
and Rust APIs to replace policies in a running authorizer and to see rejected
events. All comparisons in this section are with 1.1.2.

### Highlights

#### `dogwood-lean`: a formal specification in Lean

`dogwood-lean/` is a Lake project in the repository that states in Lean 4, on
cedar-lean `v4.14.0`, what each decision means and what validation requires.
It is for implementers who want to prove an engine correct. Its theorems rest
only on Lean's three standard axioms, and one proves that at a decision whose
checks pass, over conforming events, each rule of a valid policy set evaluates
to a Boolean or to a runtime error that validation cannot rule out.
`conformance/run.sh` compares the specification's verdicts and validation
findings (by category) with the crate's, on the guide's examples, crate test
corpora and probes of the specification's rules, and fails on a disagreement
that its baseline does not list. The off-by-default `lean-frontend` feature of
`dogwood-language` links a Lean port of the crate's frontend, which
`ServiceSchemaBuilder::frontend` selects in place of the Rust frontend, or
alongside it to compare the two. A build with the feature needs a prebuilt
archive, or Lean 4.34.0 and the repository's `dogwood-lean/`. See
[the specification README](dogwood-lean/README.md) and
[the Lean frontend](dogwood-language/README.md#the-lean-frontend-feature-lean-frontend).

#### `dogwood-ops`: the CLI's operations as a Rust library

`dogwood-ops` is a crate on crates.io with the operations of the `dogwood` CLI,
other than `format`, as functions. Each function returns a serializable report
or an `OpError`, which the CLI prints as its `--format json` output. Its
`LiveAuthorizer` authorizes one event per call and returns an error for an
unknown action or kind, an out-of-order timestamp or a dropped history event.
It is for Rust programs that run these operations in process instead of calling
the CLI. See [the `dogwood-ops` README](dogwood-ops/README.md).

#### `dogwood-lsp`: a language server

`dogwood-lsp` is an editor-agnostic language server for `.dw` policies and
`.dwschema` event schemas. For each open policy, it publishes the diagnostics
that `dogwood validate` gives with the policy's schemas, providers and macros.
It finds them in the policy's directory or a parent directory in the
workspace, or reads their paths from its initialization options. It also
publishes diagnostics for each open event schema, and semantic tokens that an
editor can show as syntax highlighting. It is for policy authors whose editor
has a Language Server Protocol client, and it ships no editor extension. It is
in the repository, not on crates.io. To build and configure it, see
[the `dogwood-lsp` README](dogwood-lsp/README.md).

#### Verus proofs about the `exists` and `for` checks

Dogwood checks the `exists` binders and aggregation `for` lists of a temporal
condition when it parses a temporal block, and again after macro expansion.
Verus proofs in `dogwood-language` show that these checks cannot panic on a
binder that is still a macro parameter (`?p`) or fresh binder (`$t`), index out
of bounds or cause an arithmetic overflow, and that they end if the helper
functions they call end. The proofs assume that these helper functions do not
panic or run forever, and do not cover the parser, macro expansion, stack
overflow or whether the checks accept the right conditions. To check the proofs,
run `cargo verus verify` from the root of the repository, with Verus release
`0.2026.09.20.aef82ed`, which matches the `vstd` version that `dogwood-language`
requires.

### Added

- **The event-schema directive `max_horizon = <interval>` makes
  `dogwood validate` (not `lower` or `replay`) reject a condition whose nested
  `within` windows along one chain add up to more than the interval.** See
  [capping the look-back](dogwood-docs/guide/03-event-schema.md#capping-the-look-back-max_window-and-max_horizon).
- **`Authorizer::update_policies` replaces an authorizer's policies and keeps
  its temporal history.**
- **`Authorizer::submit` returns `Rejection::Nonconforming` for a dropped
  history event.**
- **`AuthorizerBuilder::mirror_rule` selects `MirrorRule::Strict` (the
  default), `Current` or `Unchecked`, which skips only the checks on mirrored
  and pinned fields.** No setting makes the authorizer ingest every event as
  1.1.2 did.
- **`ParsedPolicySet::with_ids` gives opt-in stable policy ids, and
  `PolicyRef`, `LoweredPolicySet::version_hash` and
  `TemporalField::content_hash` identify a rule, a policy set and a temporal
  leaf.** See
  [stable policy identity](dogwood-docs/guide/07-api-and-workflow.md#stable-policy-identity-ids-revisions-versions-opt-in).
- **`PolicyEngine` and `TemporalEngine` have new trait methods with defaults,
  among them `PolicyEngine::authorize`, `TemporalEngine::set_authored_leaves`
  and `TemporalEngine::try_observe`.**
- **An action schema can declare `external` entity types and actions
  (Cedar 4.14), but `dogwood validate` then fails each rule, and the
  authorizer denies every decision for an `external` action.**
- **The Rust API has these other new items.** `Diagnostics::erroring`,
  `LoweredPolicySet::check_event_conformance`, `LoweredPolicySet::check_event`,
  `EventSignature::check_pins`, `EventPin::is_symmetric`, `decision_request`,
  `DecisionRequestCache`, `Value::extension`, `Value::is_null`,
  `Value::canonical`, `Event::canonical`, `Value::canonical_decimal`,
  `ParsedPolicy::effect`, `ParsedPolicy::temporal_construct_counts`,
  `LoweredPolicySet::policy_schema`, `PolicySchema::cedarschema_str`,
  `LoweredPolicySet::temporal_slice`, `temporal_ast::condition_text`,
  `temporal_ast::parse_condition`, `temporal_ast::field_path::{join, split}`,
  `syntax::policy_spans`, `syntax::event_schema_spans`, `spec_entities` and
  `EventSignature::spec_fields`.

### Breaking changes

#### Requests, events and provider outputs must match their declarations

- **The authorizer denies a request that does not match the action schema
  (`nonconforming request`).** Such a request has a context that does not
  match the action's declared context, or a principal or resource type
  outside `appliesTo`. Under the default event schema, a principal or
  resource of the wrong type gives `nonconforming decision event` instead.
  Under the Drupe template, the base action schema of `dogwood schema mcp`,
  every request must supply `system.now` as a `datetime`. The authorizer also
  denies every request with a top-level context attribute whose name is
  `providers` or ends in `__temporal_` and one or more digits
  (`x__temporal_0`), even when the set has no temporal or provider leaf and
  `dogwood validate` passes.
- **The authorizer denies a decision event whose logged fields do not match
  its event signature (`nonconforming decision event`).** It does not record
  such an event. Causes include a missing required field, a wrong type, an
  entity without its namespace, a value outside its enum, an unlogged pinned
  field and an undeclared action.
- **The authorizer drops a history event (by default a `response` or `error`
  event) that does not match its event signature.** It also drops one whose
  action and kind the event schema does not declare. No later temporal
  condition sees a dropped event, so verdicts that depended on it can change,
  in either direction. `Authorizer::is_authorized` returns `None` for a
  dropped event, as for a recorded one.
- **A logged field that mirrors the request must hold the value in the
  event's scope or request context.** The fields that mirror the request are
  `callerPrincipal`, `callerResource` and every field pinned to `principal`,
  `resource` or a context path. When the event has no such value, the field
  must be absent. The authorizer drops a history event and denies a decision
  event that breaks this rule. Under the default event schema, it drops every
  history event with no principal in its scope. See
  [the mirror rule](dogwood-docs/guide/03-event-schema.md#the-mirror-rule-an-event-carries-the-key-it-reports-on).
- **The authorizer denies a decision when a provider output is not a value of
  its declared type (`nonconforming provider output`).** Every provider call
  in the set runs on every decision event, so a script that returns a bad
  output (for example, for an absent argument) also denies decisions for
  actions whose rules never call it.

#### Verdicts change for input that both versions accept

- **A `null` in a logged field, the request context or a provider output
  counts as absent.** As a result, `*` and binders do not match it and `has`
  is false for it. Arrays compare as sets in temporal correlations.
- **`dogwood replay`, `parse_trace` and `replay_log` read `datetime("…")`,
  `duration("…")`, `ip("…")` and `decimal("…")` in a trace as Cedar
  values.** 1.1.2 read them as strings, so Cedar conditions on them can decide
  differently.
- **In temporal conditions, pins and provider arguments, `principal.id`,
  `principal.type`, `resource.id` and `resource.type` are ordinary
  attributes.** When the request supplies no entity data, the value is
  absent, so a predicate that correlates on it matches no event. 1.1.2 fell
  back to the uid's id or type name.
- **A `principal` or `resource` provider argument reads the request scope, not
  the logged `callerPrincipal` or `callerResource`.** Results differ only
  under an event schema that does not declare that field.
- **A pin to `principal`, `resource` or a context path on every event kind
  gives
  [key-local semantics](dogwood-docs/guide/03-event-schema.md#universal-symmetric-pins-key-local-semantics-and-the-partition-guarantee)
  whatever the field is called, as the default `callerPrincipal` pin does.**
  This can change `previous` and `since` verdicts.
- **The authorizer ignores entity data that a request supplies for a declared
  action, and uses the schema's action entities.** 1.1.2 denied such a
  request unless the data matched the schema.
- **In temporal conditions and pins, an attribute whose name holds a dot
  (`"user.id"`) and the attribute `id` inside `user` are different fields.**
  In 1.1.2, when the request context held both, `context.input.user.id` could
  read the value of `"user.id"`.
- **A bare type name in an action's context also resolves in the root
  namespace, as in Cedar.** A spliced `...inputs(A)` or `...outputs(A)` of a
  root-namespace common type then has its fields, which events must log as
  their signature requires.

#### Build, dependencies and Rust API

- **MCP schema generation exists only with the off-by-default `mcp-schema`
  Cargo feature.** This applies to `dogwood schema mcp`,
  `mcp_to_cedar_schema[_with_template]`, `DRUPE_TEMPLATE` and
  `PolicySchema::from_mcp_manifest[_with_template]`. A default `dogwood`
  build reports `unrecognized subcommand 'mcp'`.
- **Dogwood requires exactly Cedar 4.14.0.** Lowered Cedar text has fewer
  parentheses and keeps `has a.b.c` as one test, so stored or hashed lowered
  policies can change.
- **`dogwood-language` requires `vstd = "=0.0.0-2026-09-20-0158"` and
  `rustc-literal-escaper = "=0.0.8"`.** The `mcp-schema` feature requires
  `cedar-policy-mcp-schema-generator = "=0.7.0"` and `mcp-tools-sdk = "=0.5.0"`.
  A dependent's own requirements must allow these versions. The crate
  declares `links = "dogwood_lean"`, so a dependency graph can hold only one
  copy of `dogwood-language` 1.2 or later.
- **The authorizer denies a decision when a temporal engine binds a name that
  is not a leaf, or leaves unbound a leaf that a policy reads.**
- **A distincter must be a Cedar identifier with nothing around it.** Any
  other string gives `Error::InvalidDistincter`.

#### CLI output

- **`dogwood replay` prints `REJECTED, not ingested` for a dropped history
  event.** Its JSON report adds a `rejected` array when it drops one. It still
  exits 0, so CI must check the output for `error:` and `REJECTED` lines.
- **`dogwood explain` quotes an attribute name that is not a Cedar identifier,
  and puts parentheses around an `if` operand of `&&` or `||`.** In
  `--format json`, a span in a `def cedar` body is a byte offset in the file
  that defines the macro, where 1.1.2 counted from the start of the body.
- **Validation, temporal and provider messages name entity types with their
  namespace (`Drupe::Tool2_Input_mode`).**

### Changed

- **A temporal `principal.<path>` or `resource.<path>` whose type differs
  between two entity types the rule admits validates where each use is well
  typed, as in Cedar.** 1.1.2 rejected every such read when one action of
  the rule admits both entity types.

### Deprecated

- **`Diagnostics::determining` and `PolicyRef` replace `Diagnostics::reason`
  and `DogwoodRuleRef`.** The old items stay supported in 1.x.

### Fixed

#### Validation checks

`dogwood validate` and `Validator::validate` reject these policy sets and
schemas, which 1.1.2 accepted. `dogwood lower`, `dogwood replay` and the
authorizer still load them.

- **A rule that Cedar finds false for every request its scope admits fails.**
- **A temporal condition that reads an optional attribute needs a `has` test
  that guards it in the Cedar part of the rule.**
- **Validation type-checks temporal conditions, their event-schema fields,
  pins and provider arguments for every action, principal type and resource
  type the rule admits.** Entity types compare by qualified name, and action
  literals must name declared actions. A variable that an event-schema field
  binds must have a type that covers every value of the field. A provider
  argument must have exactly its declared type, so a bare `principal`, the
  whole `context` and every `datetime`, `duration` or `ipaddr` value fail. A
  rule fails on a read of `principal.id`, `principal.type`, `resource.id` or
  `resource.type` when an entity type it admits does not declare that
  attribute. A pin, the default `callerPrincipal` pin included, must read
  `principal`, `resource` or a declared, required attribute of a type the
  pinned field can hold.
- **A binder's type must be `Long`, `String`, `Bool`, `decimal`, `Timepoint` or
  a declared entity type with its namespace, and applies only in its own
  body.**
- **A provider method's `inputType` must match the output type of the stage
  before it.**
- **Temporal conditions reject terms of type `datetime`, `duration` and
  `ipaddr`, and `decimal("…")` literals that Cedar rejects.**
- **An event-schema field whose type names neither a builtin type nor a
  declared entity type takes no pin and no argument other than `*`.**
- **An aggregation `for` list must not repeat a name, and a wildcard must not
  be a comparison operand.**
- **An `==` or `!=` between a variable and a term that is not a variable
  fails when the two sides have different entity types.**
- **In a temporal condition, an `==` or `!=` between two sets or two records
  whose types differ only in entity types or in record attributes fails, as in
  Cedar.** A predicate argument fails in the same way when it is a set of
  records whose type differs from the field's.
- **When the set has temporal or provider leaves, the Cedar part of a rule
  must not read `context` whole.**
- **A rule must not read a top-level context attribute whose name is
  `providers` or ends in `__temporal_` and one or more digits.**
- **An enumerated entity type must not be an ancestor of another entity
  type.**

#### Load errors

These errors are new in 1.2.0, for input that 1.1.2 loaded.

- **In every command, an event kind declared twice is an error.** So is a
  `max_window` whose length in seconds overflows a signed 64-bit integer.
- **Lowering fails when any action's context declares an attribute with the
  name of one of the set's temporal leaves (`<rule>__temporal_<n>`).** This
  applies to `dogwood validate`, `lower` and `replay`, and to lowering in
  Rust. Lowering also fails when any action's context declares `providers`
  and the set calls a provider, unless the attribute is the provider type of
  an earlier lowering.

#### Other fixes

- **A common type that contains itself is an error, not a stack overflow.**
- **A provider output field whose name is not a Cedar identifier lowers.**
- **A provider output field of a builtin type keeps that type in a namespace
  that declares a type of the same name.**
- **A macro expansion error in a temporal block, or in a `def` body of the
  policy file, points at its position in that file.**
- **Validation diagnostics list entity types and request environments in name
  order, so they are the same on every run.**

### Documentation

- **The event-schema chapter describes the mirror rule and the `max_horizon`
  cap.**
- **The API and workflow chapter describes stable policy identity, retries and
  event ids, and the mirror-rule options.**
- **The formal-specification chapter describes the event-log contract and the
  check that runs before an event is observed.**

### Experimental

These are non-official, opt-in features. Their syntax and behavior may change
or be removed in a future release.

- **With `experimental-arithmetic`, an aggregate inside a compound operand
  gets the pins and validation checks of a bare aggregate.** An array constant
  in such an operand fails lowering.

### Upgrade notes

- Run `dogwood validate` on each policy set. Guard a temporal read of an
  optional attribute with an earlier `when { context.input has tag }` clause,
  or, if the condition holds when no event matches (`!formerly`,
  `count … <= N`), with
  `when { if context.input has tag then temporal { … } else true }`.
- Under the default `callerPrincipal` pin, remove a binder that only
  correlates on `callerPrincipal`, because the pin already does.
- Where a rule admits a principal type that a predicate's action does not,
  scope the rule with `principal is …`. Replace a temporal test of
  `principal.type` or `resource.type` with `principal is …` or
  `resource is …` in the scope. In both cases, if the condition holds when no
  event matches, add a copy of the rule without the temporal condition for
  the other types.
- To keep a rule that reads `principal.id`, write one copy of it for each
  entity type that declares `id` (`principal is A::User`), and supply `id` in
  each request's entity data. Under the Drupe template, declare `id` on
  `Drupe::User` first (in your own template, or in the generated schema). A
  rule that tests one fixed principal can instead compare `principal` in its
  scope.
- Compare `datetime`, `duration` and `ipaddr` values in Cedar conditions, not
  in temporal ones.
- Replay existing traces. Log each event with the scope it reports on, and
  write extension values with their constructor, or with `Value::extension`
  in Rust.
- `dogwood validate` does not run provider scripts, so check them with
  `dogwood replay`, also for requests where an argument is absent.
- Regenerate stored or hashed lowered policies.
- In a custom `PolicyEngine`, override `authorize` to report which policies
  erred.

## [1.1.2] (2026-11-11)

### Summary

This patch release limits the depth and the size of the trees that parsing,
macro expansion and lowering build, where earlier releases could overflow the
stack or run out of memory.

### Breaking changes

- **A rule with four or more `when` or `unless` clauses lowers to a balanced
  `&&` tree, so its lowered Cedar text and JSON change.** Evaluation order
  does not change.

### Added

- **`ParseOptions` sets the two limits (`max_depth` and `max_nodes`) for
  `ParsedPolicySet::parse_with`, `LoweredPolicySet::from_str_with` and
  `LoweredPolicySet::from_many_str_with`.** The other entry points use
  `DEFAULT_MAX_DEPTH` and `DEFAULT_MAX_NODES`.

### Fixed

- **Nesting or chaining deeper than 32 levels in policy or event-schema text
  is a parse error.** In policy text, `ParseOptions::max_depth` sets this
  limit. In a chain such as `a || b || …`, each term adds one level, and in a
  `has` path, each segment does.
- **A policy set whose macro expansion or lowering needs more than
  `ParseOptions::max_nodes` tree nodes (default 1,000,000) is an error.**
- **A temporal keyword must end at a word boundary.**
- **A Cedar action schema with more than 64 brackets, records or `Set<…>`
  types open at once is an error (`Error::ActionSchema`).**
- **The guard of a relativized pinned leaf (a pinned `previous`, or a positive
  `since`) is a balanced tree, not a chain.** Verdicts do not change.
- **A syntax error in a `def cedar` body of the policy file points at its
  position in the body.**

### Upgrade notes

- If a policy fails a limit, shorten its chains or nesting, or in Rust pass a
  larger `ParseOptions` to a `_with` entry point. The `dogwood` CLI has no
  option for the limits.
- Treat stored or hashed lowered policies of rules with four or more clauses,
  and stored relativized pinned leaves, as new.

## [1.1.1] (2026-10-29)

### Summary

This patch release makes the parser read policy text as Cedar does. 1.1.0
gave some text a meaning other than the written one, such as a temporal
threshold outside the `i64` range, which it read as `0`.

### Breaking changes

- **A `//` comment does not change a policy, also in a `temporal` block or a
  `def` body.** 1.1.0 read part of some comments as policy text, so such a
  policy can decide differently.

### Fixed

- **A block whose closing `}` follows a `//` comment on the same line is a
  syntax error, because the `}` is part of the comment.**
- **An integer literal outside the `i64` range is an error in the Cedar and
  temporal dialects.**
- **A `def temporal` body must not use a plain identifier as a variable or
  binder.**
- **A chain of relational operators without parentheses is an error.**
- **The right-hand side of `has` must be an attribute path, so a name that is
  not an identifier needs quotes.**
- **The right-hand side of `like` must be one string literal.**
- **A provider argument must not use `-` except directly before a number.**
- **A record key must be a string literal or an unqualified name, and must
  not repeat.**
- **A provider call names the same provider however its qualified name is
  spaced.**
- **`expanded_source` quotes a record key that Cedar reserves.**

### Upgrade notes

- Run `dogwood validate` on each policy set, and rewrite the text that it
  rejects. In a `def temporal` body, write `$x` for a variable that the macro
  binds itself, or declare a `?x` parameter.
- Render `expanded_source` again from the original source. Text that 1.1.0
  rendered can contain `has "x".y`, which 1.1.1 does not parse.

## [1.1.0] — 2026-10-09

### Summary

This release adds enum-typed provider values, two new policy tooling commands
(`dogwood format` and `dogwood explain`), and a `lower_many` API for lowering
several policy sets into one. It also hardens the provider pipeline so that
wrong-shaped or out-of-enum provider values fail closed. The provider-value
change carries one source-level breaking change for Rust API consumers; policy
authoring and existing `providers.json` files are unaffected.

### Breaking changes

- **providers**: `ProviderDeclarations` and `ParamType` gain public fields
  (`entity_type_decls`, `entity_type`) and now derive `Default`. Rust struct
  literals must add the new fields or end in `..Default::default()`, and
  exhaustive destructuring patterns need `..`. JSON input is unaffected —
  existing `providers.json` files load as before.

### Added

- **providers**: Enum-typed provider values. A providers file can declare
  entity-type enums (e.g. `GuardDuty::Severity` with `enum: ["LOW", "HIGH"]`)
  and type provider values by them, so Cedar catches typos in policies and an
  out-of-list value is denied at runtime. Only the enums actually used by the
  providers and methods a policy set calls are exported, each once, into the
  action schema's home namespace (with `::` rewritten to `_` and tagged
  `@dogwood_provider_enum`). Authoring is unchanged; Cedar diagnostics map back
  to the declared enum names.
- **syntax**: New `dogwood-syntax` crate (`dogwood-syntax`) owning the
  shared concrete syntax — the Pest policy grammar, a lossless tokenizer, and
  grammar-derived spans. Both the semantic parser and the formatter now parse
  through it, so the two grammars cannot drift.
- **formatter**: `dogwood format`, a source-preserving pretty-printer for `.dw`
  policy source. It formats from a lossless token stream, so comments, BOMs,
  strings, and authored operator spelling are preserved — only whitespace
  changes. Formatting is idempotent, targets an 80-column width, and returns
  unparseable source unchanged, making it safe for editor save hooks. New crate:
  `dogwood-formatter` (`dogwood-formatter`).
- **informalize**: `dogwood explain`, a deterministic policy-to-semi-English
  translator (`ParsedPolicySet::informalize` / `ParsedPolicy::informalize`),
  so a policy can be checked against the requirement it came from. It is a pure
  function of the AST plus optional action and event schemas — no language
  model — and is meaning-preserving. Text and JSON output
  (`--format json`) are supported.
- **api**: `lower_many(policies, policy_schema)` lowers several parsed policy
  sets, each under its own `Distincter`, into one `LoweredPolicySet` over a
  policy schema augmented once. `LoweredPolicySet::from_many_str` is the
  parse-then-lower one-call form. New public surface: `Distincter` (validated
  as a Cedar identifier at construction), `lower_many`, `from_many_str`, and
  `Error::{DuplicateDistincter, NoPolicies, MismatchedServiceSchema}`.

### Changed

- **api**: `ServiceSchema` is now `Arc`-backed; `clone` is a reference-count
  bump. The public surface is unchanged. Every entry passed to `lower_many`
  must be parsed with a clone of one `ServiceSchema`, checked by identity.
- **validation**: `ValidationWarning::Extension` now declares `Warning`
  severity, so `dogwood validate --format json` no longer labels dialect
  warnings `"severity": "error"`.

### Fixed

- **render**: A temporal gensym binder (`t$78`) no longer aliases a user binder
  spelled `t_78` in `expanded_source`; the gensym becomes `t_78_1`. Output is
  byte-identical when nothing collides.

### Documentation

- **events**: Clarified event semantics with a checked enforcement example —
  how events represent attempts and completions, how observed ingestion order
  differs from the timestamps used for time windows, and the caller's ordering
  and timestamp requirements.

### Experimental

These are non-official, opt-in features. Their syntax and behavior may change
or be removed in a future release, and they are off by default.

- **temporal**: Arithmetic in temporal comparison operands, gated behind the
  off-by-default `experimental-arithmetic` Cargo feature (forwarded by the
  `dogwood` CLI). A default build rejects compound operands with "arithmetic in
  comparison operands is not yet supported"; with the feature on, policies are
  accepted and validation warns once per policy set that the operators are
  experimental and may change.

### Upgrade notes

- Rust consumers constructing `ProviderDeclarations` or `ParamType` by struct
  literal must add the new fields or `..Default::default()`; exhaustive
  destructuring patterns need `..`. No changes are required for
  `providers.json` input or for policy authoring.



