# Changelog

All notable changes to the Dogwood policy language are documented here.

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
