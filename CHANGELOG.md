# Changelog

All notable changes to the Dogwood workspace are documented here.

## 1.2.0 (2026-11-18)

### Added

- **ops**: the new crate `dogwood-ops` gives the operations of the CLI
  commands other than `format` as functions that return serializable reports or
  an `OpError`. Its `LiveAuthorizer` authorizes one event per call and returns
  an error for an unknown action or kind, an out-of-order timestamp or a dropped
  history event
- **lsp**: the workspace package `dogwood-lsp` is an editor-agnostic
  Dogwood language server (binary `dogwood-lsp`)
- **syntax**: `syntax::policy_spans` and `syntax::event_schema_spans` classify
  the spans of policy and event-schema text for syntax highlighting
- **event schema**: under an optional `max_horizon = <interval>` directive,
  validation rejects a condition with a chain of nested `within` windows whose
  sum is larger than the interval. The interval is also the default
  `max_window`, and a longer `max_window` is an error
- **identity**: `PolicyRef` contains the id and revision of a rule, and
  `LoweredPolicySet::version_hash` gives a hash of a policy set.
  `TemporalField::content_hash` names a leaf without its position
- **identity**: `ParsedPolicySet::with_ids` gives opt-in stable policy ids. With
  stable ids, the authorizer denies a decision when the policy engine reports
  an id that is not in the set
- **authorizer**: `Authorizer::update_policies` replaces the policies of an
  authorizer and keeps its temporal history. If an engine fails to prepare the
  new policies, the authorizer denies every decision and records no event until
  an update succeeds
- **authorizer**: `Diagnostics::determining` and `erroring` name each policy by
  its `PolicyRef`
- **authorizer**: `Authorizer::submit` returns `Rejection::Nonconforming` for a
  dropped history event, which `is_authorized` does not report, and
  `LoweredPolicySet::check_event_conformance` runs the same check but does not
  ingest the event. `AuthorizerBuilder::mirror_rule` selects
  `MirrorRule::Strict` (the default), `Current` or `Unchecked`, which skips only
  the checks on mirrored and pinned fields
- **engine**: `PolicyEngine::authorize`, `supports_policy_update` on the two
  engine traits, and `TemporalEngine::set_generation`, `set_authored_leaves` and
  `try_observe` (which can return `Rejection::Unavailable`) are new trait
  methods with defaults. `LoweredPolicySet::decision_request`,
  `dogwood_language::decision_request` and `DecisionRequestCache` (for many
  decisions against one schema) give the Cedar request of a decision before its
  temporal and provider leaves have values
- **engine**: `LoweredPolicySet::check_event`, `EventSignature::check_pins` and
  `EventPin::is_symmetric` let an engine that logs events itself apply the
  checks on mirrored and pinned fields
- **values**: `Value::extension` builds a Cedar `datetime`, `duration` or
  `ipaddr` value, and `Value::is_null` tests for `null`. `Value::canonical`,
  `Event::canonical` and `Value::canonical_decimal` return a canonical form,
  which is the same for any two values that `Value::dom_eq` finds equal
- **api**: `ParsedPolicy::effect` returns whether a policy is a `permit` or a
  `forbid`, and `ParsedPolicy::temporal_construct_counts` returns how many of
  each temporal operator it holds. `LoweredPolicySet::policy_schema` returns the
  policy schema of a lowered set, and `PolicySchema::cedarschema_str` returns
  its text
- **api**: `temporal_ast::condition_text` writes a temporal leaf as text that
  `temporal_ast::parse_condition` reads back. `LoweredPolicySet::temporal_slice`
  returns the leaves of the rules that can apply to an action, and
  `LoweredPolicySet::action_groups` and `ActionScope::narrowed_to` give the
  rule it selects them by
- **api**: `spec_entities` and `EventSignature::spec_fields` give a schema's
  entity types and actions, and an event signature's fields, as `Spec*` values
  in the form of the formal specification
- **frontend**: the off-by-default `lean-frontend` feature adds a frontend
  written in Lean, which `ServiceSchemaBuilder::frontend` selects (see the crate
  README)
- **language**: an action schema can declare `external` entity types and actions
  (Cedar 4.14), and validation then reports the incomplete-schema error of Cedar
  for each rule. The authorizer denies a decision for an `external` action, and
  one whose entity data has a record of an `external` type

### Changed

- **authorization** (breaking): the authorizer denies a decision, and does not
  record its event, when the event does not conform to the event schema
  (`nonconforming decision event`). It also denies a decision whose request
  does not match the action schema (`nonconforming request`), or whose
  provider output does not match its declared type
  (`nonconforming provider output`)
- **authorization** (breaking): the authorizer drops a history event that does
  not conform to the event schema, so no later decision sees it.
  `dogwood replay` prints `REJECTED, not ingested` for it, lists it under
  `rejected` in its JSON report, and still exits 0
- **authorization** (breaking): by default (`MirrorRule::Strict`), a mirrored
  field (`callerPrincipal`, `callerResource`, or a field pinned to `principal`,
  `resource` or a context path) must hold the event's scope or context value, or
  be absent when the event has none. Each event must also log its pinned fields,
  and the authorizer drops a history event or denies a decision event that fails
  these checks
- **authorization** (breaking): under the default event schema and mirror rule,
  the authorizer drops a history event whose scope has no principal, even one
  that logs `callerPrincipal` (give it the principal of its request)
- **cli** (breaking): `dogwood schema mcp` exists only in a build with the
  off-by-default `mcp-schema` feature. A default build reports
  `unrecognized subcommand 'mcp'`
- **language** (breaking): `mcp_to_cedar_schema`,
  `mcp_to_cedar_schema_with_template`, `DRUPE_TEMPLATE` and
  `PolicySchema::from_mcp_manifest[_with_template]` require the `mcp-schema`
  feature, which depends on exactly `cedar-policy-mcp-schema-generator` 0.7.0
  and `mcp-tools-sdk` 0.5.0
- **language** (breaking): Dogwood requires exactly Cedar 4.14.0, where 1.1.2
  used 4.11.0. Cedar 4.14 prints lowered policies with fewer parentheses and
  keeps an `e has a.b.c` of plain identifiers as one test, so the lowered Cedar
  text changes
- **language** (breaking): `dogwood-language` depends on the exact versions
  `vstd = "=0.0.0-2026-09-20-0158"` and `rustc-literal-escaper = "=0.0.8"`
  (1.1.2 used `=0.0.7`), which a dependent's own requirements must allow. The
  crate also declares `links = "dogwood_lean"`, and Cargo allows only one
  package with that value in a dependency graph
- **authorization** (breaking): the authorizer denies a decision when a temporal
  engine returns a value for a name that is not a leaf. It also denies a
  decision when the engine returns no value for a leaf that a policy reads
- **validation** (breaking): an impossible policy, a rule that Cedar finds
  false for every request its scope admits, fails validation. 1.1.2 gave a
  warning
- **validation** (breaking): a temporal condition that reads an optional
  attribute needs a `has` test that guards it in the Cedar part of the rule
- **validation** (breaking): a variable that an event-schema field binds must
  have a type that covers every value of the field
- **validation** (breaking): a provider argument must have exactly its declared
  type for every action, principal type and resource type that the rule
  admits. The whole `context` and every `datetime`, `duration` or `ipaddr`
  value fail this check
- **validation** (breaking): a provider method's `inputType` must be the same
  Cedar type as the output of the pipeline stage before it
- **validation** (breaking): a temporal term of type `datetime`, `duration` or
  `ipaddr` fails validation, and so does a temporal `decimal("…")` literal that
  Cedar rejects. A predicate can still leave a `datetime`, `duration` or
  `ipaddr` field out or match it with `*`
- **values** (breaking): `parse_trace`, `replay_log` and `dogwood replay` read a
  trace's `datetime("…")`, `duration("…")`, `ip("…")` and `decimal("…")` as
  Cedar values, which 1.1.2 read as strings. Cedar conditions on such values can
  decide differently
- **validation** (breaking): a binder must have the type `Long`, `String`,
  `Bool`, `decimal`, `Timepoint` or a declared entity type with its namespace.
  An aggregation `for` list must not repeat a name, and a wildcard must not be a
  comparison operand
- **validation** (breaking): the two sides of an `==` or `!=` between a variable
  and a non-variable term must have the same type
- **validation** (breaking): the validator types each temporal condition and its
  event-schema fields for every action, principal type and resource type that
  the rule admits. Entity types compare by qualified name, action literals must
  name declared actions, and messages name entity types with their namespace
- **validation** (breaking): a pin, or an argument other than `*`, of an
  event-schema field whose declared type names no type fails validation
- **language** (breaking): in temporal conditions, pins and provider arguments,
  `principal.id`, `principal.type`, `resource.id` and `resource.type` are
  ordinary attributes, absent when the request supplies no entity data. A rule
  that reads one fails validation when an entity type it admits declares no such
  attribute
- **authorization** (breaking): a `principal` or `resource` provider argument
  reads the scope of the request, not the logged `callerPrincipal` or
  `callerResource`
- **validation** (breaking): a pin must read `principal`, `resource` or a
  declared, required attribute, of a type that the pinned field can hold. The
  check applies in every request that the rule admits, and to the default
  `callerPrincipal` pin
- **authorization** (breaking): a pin to `principal`, `resource` or a context
  path on every event kind gives key-local semantics whatever its field is
  called. This can change `previous` and `since` verdicts
- **event schema** (breaking): an event kind declared twice is an error, and so
  is a `max_window` whose length in seconds overflows a 64-bit integer
- **validation** (breaking): when the policy set has a temporal or provider
  leaf, the Cedar part of a rule must not read `context` whole. A condition must
  not read a context attribute with the name of a hoisted leaf
  (`<rule>__temporal_<n>`, `providers`)
- **lowering** (breaking): a declared context attribute with the name of a
  hoisted temporal leaf fails lowering, where 1.1.2 accepted it. A declared
  `providers` attribute fails lowering when the set has a provider leaf, unless
  it refers to the provider type of an earlier lowering
- **validation** (breaking): an enumerated entity type must not be an ancestor
  of an entity type (finding code `schema`), although Cedar allows it
- **distincters** (breaking): a distincter must be a Cedar identifier
  (`[_A-Za-z][_A-Za-z0-9]*`) with nothing around it, else
  `Error::InvalidDistincter`
- **authorization** (breaking): the authorizer ignores entity data that a
  request supplies for a declared action and uses the action entities of the
  schema. 1.1.2 denied such a request unless the data matched the schema
- **authorization** (breaking): in a policy that fails validation, a temporal
  comparison that orders a timepoint, or computes with one, is false
- **validation**: a temporal `principal.<path>` or `resource.<path>` with
  different types on two entity types the rule admits validates where each use
  is well typed, as in Cedar. 1.1.2 rejected every such read

### Deprecated

- **authorizer**: `Diagnostics::determining` and `PolicyRef` replace
  `Diagnostics::reason` and `DogwoodRuleRef` (with its `rule_index`). The old
  items stay supported in 1.x and have no `#[deprecated]` attribute

### Fixed

- **interpreter** (breaking): a `null` in a logged field, the request context or
  a provider output counts as absent, and arrays compare as sets in temporal
  correlations. `Value::dom_eq` and `partition_value_key` apply the two rules,
  so the key of an array or a record can differ from the key 1.1.2 gave
- **explain** (breaking): `dogwood explain` quotes an attribute name that is not
  a Cedar identifier, and puts parentheses around an `if` operand of `&&` or
  `||`. Its text and JSON output change for such conditions, and JSON spans in a
  `def cedar` body are byte offsets in the macro's file (1.1.2 counted from the
  start of the body)
- **interpreter** (breaking): `context.input.user.id` and
  `context.input["user.id"]` are different paths in temporal terms and pins.
  `temporal_ast::field_path::{join, split}` write and read a path with its
  segments escaped
- **temporal** (breaking): with `experimental-arithmetic`, an aggregate inside a
  compound operand gets the pins and the validation checks of a bare aggregate
  (declared events, time dependence). An array constant in such an operand fails
  lowering
- **relativization** (breaking): a pinned `previous` or `since` decides as
  written when the leaf has a variable named like a binder of the pin rewrite
  (such as `__pin_ti0`). In 1.1.2 the rewrite could capture that variable and
  change the verdict
- **event schema** (breaking): a bare type name in an action's context resolves
  in the action's namespace and then in the root namespace, as in Cedar. A
  spliced `...inputs(A)` or `...outputs(A)` of a root-namespace common type then
  has its fields
- **lowering** (breaking): a provider output field of a builtin type keeps that
  type in a namespace that declares a type of the same name
- **validation** (breaking): the declared type of a binder applies only in its
  own body. A name that an aggregation `for` list binds again keeps its outer
  type outside the aggregation
- **lowering**: a provider output field whose name is not a Cedar identifier
  passes lowering, where 1.1.2 gave an error
- **lowering**: a common type that contains itself fails lowering with an error,
  not a stack overflow
- **macros**: an expansion error in a temporal block or in a `def cedar` or
  `def temporal` body points at its position in the source. The error for a
  binding equality names the value operand when that operand is not an aggregate
- **validation**: diagnostics list entity types and request environments in
  name order, so they are the same on every run

## 1.1.2 and 1.0.2 (2026-11-11)

### Fixed

- **parser**, **lowering** (breaking): a policy set whose macro expansion or
  lowering needs more than `ParseOptions::max_nodes` tree nodes (default
  1,000,000, set through `ParsedPolicySet::parse_with` and the other `_with`
  functions) is an error
- **parser** (breaking): nesting or chaining deeper than
  `ParseOptions::max_depth` (default 32, set the same way for policy text) in
  policy or event-schema text is a parse error
- **parser** (breaking): a multi-segment `has` path counts about one level per
  segment toward `ParseOptions::max_depth`
- **parser** (breaking): a temporal keyword must end at a word boundary
- **lowering** (breaking): a rule with four or more `when` or `unless` clauses
  lowers to a balanced `&&` tree, so its Cedar text changes
- **api** (breaking): an action schema that has more than 64 records, `Set<…>`
  types or brackets open at once is an error (`Error::ActionSchema`)
- **pins**: the guard of a relativized pinned leaf is a balanced tree, not a
  chain, and verdicts do not change. With 4 or more derived events (2 or more
  actions under the default event schema), the leaf changes shape, so a stored
  fingerprint of the leaf no longer matches
- **parser**: a parse error in a `def cedar` body, such as an invalid variable,
  points at its position in the body

## 1.1.1 and 1.0.1 (2026-10-29)

### Fixed

- **temporal**, **parser** (breaking): an integer literal outside the `i64`
  range is an error in the Cedar and temporal dialects
- **macros** (breaking): a `def temporal` body must not use a plain identifier
  as a variable or binder
- **parser** (breaking): a `//` comment does not change a policy, also in a
  `temporal` block or a `def` body. A `}` after a `//` on the same line is part
  of the comment and closes no block
- **parser** (breaking): a chain of relational operators without parentheses is
  an error, as in Cedar
- **parser** (breaking): the right-hand side of `has` must be an attribute path,
  as in Cedar
- **parser** (breaking): the right-hand side of `like` must be one string
  literal, as in Cedar
- **parser** (breaking): a provider argument must not use `-` except directly
  before a number, as in Cedar
- **parser** (breaking): a record key must be a string literal or an
  unqualified name and must not repeat, as in Cedar
- **parser**: a provider call names the same provider however its qualified
  name is spaced
- **render**: `expanded_source` quotes a record key that Cedar reserves

## 2026-10-09

### Changed

- **temporal**: arithmetic (`+`/`-`/`*`) in comparison operands is now gated
  behind the off-by-default Cargo feature `experimental-arithmetic`. A default
  build rejects a policy that uses it at parse time (*"arithmetic in
  comparison operands is not yet supported"*); a build with the feature on
  accepts it, and validation warns once per policy set that arithmetic
  operators are experimental and may change in a future release. The
  implementation, tests, and docs are unchanged otherwise; the four
  arithmetic example bundles carry a `requires-experimental-arithmetic`
  marker and are checked only in feature-on test runs

## 2026-10-07

### Added

- **providers**: Enum-typed provider values. `providers.json` declares enums
  under `entityTypes` and types values with `"paramType": "entity"` +
  `"entityType"`, so Cedar validates enum literals in policies
- **providers**: Each used enum is exported into the action schema's first
  namespace with actions as `<Ns>::<Vendor>_<Name>`, tagged
  `@dogwood_provider_enum`; no namespace is added. A clash with the action
  schema is an error. `lower_many` exports each enum once
- **providers**: A provider value outside its enum denies the request (fail
  closed). So does a value of the wrong shape where the declared type contains
  an enum (a bare id for a record, a missing required enum field); types
  without an enum are unchanged
- **providers**: `context` enum fields can be passed to `entity` parameters.
  Validation compares the enum type only for a direct `context` field, not
  inside a set or record argument or for a `principal`/`resource` attribute
- **providers**: `ProviderDeclarations::check`, also run by
  `ServiceSchemaBuilder::build` (new `Error::Providers`)

### Changed

- **providers**: An unknown `paramType` involving an entity type is an error
- **providers**: `ProviderDeclarations` and `ParamType` gain public fields and
  derive `Default`; struct literals need the new fields or
  `..Default::default()`

### Fixed

- **validation**: `dogwood validate --format json` labels dialect warnings
  `"severity": "warning"`, not `"error"`

### Deprecated

- **providers**: Any other unknown `paramType` still falls back to `String`,
  now with a warning; it becomes an error in the next major version

## 2026-09-28

### Added

- **api**: `Distincter`, a distincter validated as a Cedar identifier at
  construction (`FromStr`, `TryFrom<&str>`, `TryFrom<String>`); a malformed
  string is `Error::InvalidDistincter`
- **api**: `lower_many(policies, policy_schema)`, which lowers each
  `(&ParsedPolicySet, Distincter)` independently against `policy_schema`, as
  `lower_with_distincter` would, and returns one merged `LoweredPolicySet` whose
  schema is `policy_schema` augmented once with every entry's hoisted fields.
  Every entry must be parsed with clones of one `ServiceSchema`. Validation
  findings render against the text of the policy they come from
- **api**: `Error::DuplicateDistincter`, returned by `lower_many` when two
  entries share a distincter; `Error::NoPolicies`, when it gets no entries; and
  `Error::MismatchedServiceSchema`, when an entry was parsed with a different
  `ServiceSchema`
- **api**: `LoweredPolicySet::from_many_str(policies, service_schema,
  policy_schema)`, the fused form of `ParsedPolicySet::parse` on each
  `(&str, Distincter)` entry then `lower_many`. An empty `policies` yields no
  policies over `policy_schema`

### Changed

- **api**: `ServiceSchema::clone` is now a reference-count bump

### Fixed

- **render**: A temporal gensym binder (`t$78`) no longer aliases a user binder
  spelled `t_78` in `ParsedPolicy::expanded_source`; the gensym becomes `t_78_1`.
  Output is unchanged when nothing collides

## 2026-09-22

### Changed

- **providers**: Hoisted provider fields are defined once in a shared generated
  common type per touched namespace (normally `DogwoodProviders`, with a
  collision-avoiding suffix). Actions reached by at least one provider policy
  reference that type; untouched actions omit `providers`, eliminating the
  previous fields-times-actions schema expansion. Generated types carry
  `@dogwood_provider_context("1.1")` to identify the representation version.

### Testing

- **providers**: Cover shared-type export, untouched actions, feed-forward
  accumulation, cross-namespace updates, inline-record migration, and generated
  type-name collisions.

## 2026-09-11

### Added

- **engine**: Optional decision-leaf slicing — precomputes which temporal leaves each action can read, with conservative fallback
- **language**: Render expanded policies back to valid `.dw` with macros inlined
- **api/event**: Lossless request-context and `Event` → `EventBuilder` conversion, separating durable temporal fields from request-only Cedar context

### Changed

- **engine**: Name the leaf map's contract, keyed on Cedar's `EntityUid` (breaking)

### Fixed

- **partition**: Equivalent decimals (`1.5`, `1.50`) now share one temporal partition
- **parser/lowering/validation**: Decode Cedar escapes (`\u{…}`, string literals, annotations, enum/action ids) matching Cedar's behavior

### Testing

- Nested temporal operators, escaped identifiers, leaf-map slicing differentials, decimal pins, and replay round trips

## 2026-08-12

### Added

- **providers**: Validate field-path argument existence and type

### Changed

- **api**: Mark ProviderField and TemporalField non_exhaustive
- **types**: Replace stringly-typed rich types with a RichType enum

### Documentation

- **providers**: Document field-path argument validation
- **guide**: Warn that a positive since-left is rarely what you want

### Fixed

- **cli**: Strip UTF-8 BOM in check_action_schema
- **parser**: Decode `like` patterns with Cedar's escaper
- **parser**: Decode string literals with Cedar's unescaper

### Testing

- **parser**: Corpus cases for string-escape Cedar divergences
