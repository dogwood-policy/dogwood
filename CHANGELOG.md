# Changelog

All notable changes to the Dogwood policy language are documented here.

## 2026-11-11

### Fixed

- **pins**: the guard μ that relativizes a pinned leaf (a pinned `previous`,
  a positive `since`) is balanced, ⌈log₂ n⌉ deep over its n alternatives
  (one per derived event), which keep their order. It was chained one
  alternative inside the next, so 100 actions gave a guard about 300 levels
  deep, which overflows recursive consumers on a 2 MiB thread stack. Verdicts
  are unchanged; a relativized leaf changes shape once the event schema has 4
  or more derived events (with the default event schema, any action schema
  with 2 or more actions), so a consumer that persists or fingerprints the
  relativized leaves must treat those fingerprints as new
- **parser**, **lowering**: a policy set whose macro expansion or lowering
  would build an exponentially large tree is an error instead of running out
  of memory. `def cedar d(?x) { ?x && ?x }` called on its own result 30 deep
  is 2^30 nodes, and with a universal pin, as the default service schema has,
  lowering a nested `previous within 1h (…)` copies the body twice per level
  and a right-nested `READ since within 1h (…)` three times per level. A new
  limit, `ParseOptions::max_nodes`, by default
  `dogwood_language::DEFAULT_MAX_NODES` (1,000,000), bounds the tree nodes
  macro expansion may create for one parsed policy set
  (`macro expansion exceeds the node budget of 1000000`) and, separately, the
  nodes lowering may create for that set's temporal leaves
  (`lowering exceeds the node budget of 1000000`), reported at the macro call
  or leaf that exhausted it, before the excess is built. Nodes are counted as
  they are allocated and never credited back. The new entry points
  `ParsedPolicySet::parse_with`, `LoweredPolicySet::from_str_with`, and
  `LoweredPolicySet::from_many_str_with` take the options; the existing ones
  use the default. A parsed set keeps its options, so `lower`,
  `lower_with_distincter`, and `lower_many` apply the budget it was parsed
  with, and `lower_many` gives each set its own budget. Real policies need at
  most 117 nodes to expand one condition and 449 to lower one leaf, so the
  default covers a set of about 2,000 such worst-case policies; a typical
  `Read since within 1h Write` leaf is about 105 nodes, so about 9,500 of
  those fit, and a caller that loads larger sets passes a larger limit.
  Lowering of every policy within the budget is unchanged. A caller who raises the limit owns the memory and
  time the larger trees need
- **parser**: deeply nested or chained policy text is a parse error instead
  of a stack overflow that aborted the process. One limit, by default
  `dogwood_language::DEFAULT_MAX_DEPTH` (32) and configurable with
  `ParseOptions::max_depth` (`ParsedPolicySet::parse_with` and the other
  `_with` entry points), bounds the depth of every finished tree the frontend
  returns, temporal blocks included. It is enforced in two places. A lexical
  scan bounds the generated parsers' recursion before each runs
  (`nesting exceeds the maximum depth of 32`): each bracket and each keyword
  that introduces an operand counts — `if` in a policy; `exists`, `where`,
  `formerly`, `previous`, `since`, `count`, `sum`, and `for` in a temporal
  block — and only a closing bracket subtracts, releasing the keywords
  counted inside it. And every finished tree is measured with an
  explicit-stack walker and refused if deeper than the limit: the parsed
  expression at its root (`expression nested deeper than the limit of 32`,
  or `temporal expression nested deeper than the limit of 32` for a temporal
  body), and each macro expansion (`macro expansion nested deeper than the
  limit of 32`), whose depth is the sum of the body's and the argument's.
  The builders do not count: chains (`a && b && …`, `x.a.b.…`, `!!!…x`)
  build flat text into deep trees with loops, and the surface trees free
  themselves with an explicit worklist instead of recursion, so a tree of
  any depth is safe to build, measure, reject, and discard. A chain of more
  than 32 terms is rejected; earlier releases accepted at least fifty, and
  that guarantee is withdrawn. Real policies in the repository corpus
  measure at most 9 levels of nesting and 16 of expression depth. The
  event-schema DSL applies the same limit. At the default, a policy parses the same way on every host,
  thread, and build profile, and too-deep text is an error rather than a
  stack overflow on a 2 MiB thread; a caller who raises the limit owns the
  stack that later passes over the deeper trees need. Error messages name
  the limit in effect. A policy's `when`/`unless` clauses lower to a balanced
  `&&` tree, so the clause count no longer adds depth; evaluation order and
  short-circuiting are unchanged, and the lowered Cedar text and JSON of a
  rule with four or more clauses change shape, so a consumer that persists
  or fingerprints lowered policies must treat those as new. Temporal
  keywords now require a word boundary, as the scan counts them, so
  run-together keywords such as
  `countfor(t:Long).where` are a syntax error instead of parsing as
  `count for (t: Long). where`
- **parser**: a multi-segment `has` path (`context has a.b.c`) is measured
  at the depth it lowers to, one level per segment (Cedar 4.11 desugars every
  such path to a chain of `&&`ed `has` tests), so a long one is a parse error
  instead of a stack overflow in lowering
- **api**: a Cedar action schema with more than 64 brackets, records or
  `Set<…>` types open at once is refused as the new `Error::ActionSchema`
  by every `PolicySchema` constructor and by `dogwood schema action`,
  before Cedar's recursive schema parser reads it
- **parser**: an error inside a `def cedar` body, such as an invalid variable,
  points at the body. Its location used to be counted from the start of the
  file

## 2026-10-29

### Fixed

- **temporal**: an integer literal outside the `i64` range in a temporal
  block or `def temporal` body is rejected at parse time
  (`` integer literal `…` is out of range ``), as in the Cedar dialect. It was
  read as `0`, so a threshold such as `n >= 20000000000000000000` loaded as
  `n >= 0`
- **parser**: a Cedar-dialect `9223372036854775808` (2^63) is rejected unless it
  is directly negated, as Cedar does. It was read as `i64::MIN`;
  `-9223372036854775808` is still `i64::MIN`, and `-(9223372036854775808)` is
  rejected
- **macros** (breaking): a `def temporal` body may not contain a plain
  identifier variable or binder; write `$x` for a variable the macro binds
  itself, or declare a `?x` parameter. Expansion kept a plain binder as
  written, so it captured a same-named variable of a spliced call-site argument,
  and a plain free variable bound to the caller's same-named variable: the
  expanded policy silently differed from the authored one (a forbid that
  correlated on the caller's variable could permit what it was written to
  deny). The default macro library is not affected
- **parser** (breaking): a `//` comment inside a `temporal { … }` block or a
  `def` body runs to the end of the line and is inert, as it is for the
  sub-parsers that read the block. The raw block capture ignored comments, so a
  `}` in a comment closed the block early and the rest of the comment line was
  parsed as live policy: a comment such as
  `// }; permit (principal, action, resource) when temporal { …` cut the
  enclosing rule short and added a hidden permit, with no diagnostic. A `{` or
  `"` in a comment likewise moved the block's end, and an innocent unbalanced
  brace in a comment was a confusing syntax error. A block whose closing `}`
  follows a comment on the same line (`when temporal { … // note };`) is now a
  syntax error, since the `}` is part of the comment
- **parser**: a chain of relational operators such as `a == b == c` is
  rejected at parse time (`multiple relational operators (>, ==, in, etc.) must
  be used with parentheses to make ordering explicit`), as in Cedar. It was
  folded left, so `context.x == false == false` loaded as
  `(context.x == false) == false`, which is `context.x`
- **parser**: the right-hand side of `has` must be an attribute path, as in
  Cedar: a name, a name followed by `.field` accesses, or a string literal.
  Any other operand is a parse error (``invalid right-hand side of `has` ``).
  The parser used to test the operand's leftmost name, so an unquoted
  `has tool-approval` (which is `tool - approval`) tested `has tool`, and
  `has x["y"]`, `has !x`, and `has (x || y)` tested `has x`. A name that is not
  an identifier must be quoted: `has "tool-approval"`. Policies that used these
  spellings no longer load. An `expanded_source` rendered by an earlier version
  wrote a dotted path with a quoted first segment (`has "x".y`), which no
  longer parses; render it again from the original source
- **parser**: the right-hand side of `like` must be a single string literal, as
  in Cedar. Any other operand is a parse error (`` `like` requires a
  string-literal pattern ``). The parser used the first string literal anywhere
  in the operand, so `like "~/secrets" + "/*"` matched `"~/secrets"` only,
  `like context.prefix + "/*"` matched `"/*"`, and
  `like (if c then "a/*" else "b/*")` matched `"a/*"`. A literal in parentheses
  is also refused, as Cedar refuses it. Policies that used these spellings no
  longer load. Write a fixed pattern as one literal (`like "~/secrets/*"`); a
  pattern that depends on a runtime value cannot be written with `like`
- **parser**: a `//` comment between two tokens no longer changes a policy.
  The parser read some values from source text that included comments: a `!`
  or `-` inside a comment in a run of `!` or `-` counted as an operator
  (`! // not!` then `! x` was `!!!x`), and text inside a comment in a qualified
  name became part of the name (`Ns // ::Admin` then `::User::"alice"` was
  `Ns::Admin::User::"alice"`) or made it invalid. A comment after the type of an
  `is`, or after a record key, made a valid policy fail to load. These values
  are now read from tokens, as Cedar reads them
- **parser**: a run of `-` before a number folds only the innermost `-` into
  the literal, as in Cedar, so `--5` lowers to `-(-5)` rather than `5`. In a
  condition the value does not change. A provider argument no longer
  accepts it: `Ns::Fn(--5)` used to call `Ns::Fn(5)`, and is now refused
  (`` a provider argument is not allowed to use `-` except directly before a
  number ``), as Cedar refuses `--5` in a restricted expression
- **parser**: a record key must be a string literal or an unqualified name, as
  in Cedar. Other keys used to load, for example `{ a.b: 1 }` with the key
  `a.b`, `{ true: 1 }` with the key `true`, and `{ ("a"): 1 }` with the key
  `a`. They no longer load. Quote the key instead: `{ "a.b": 1 }`. A key that
  appears twice, compared after decoding (`{ a: 1, "a": 2 }`), is an error
  (`` duplicate key `a` in record literal ``), as in Cedar; the last value used
  to win. In a `def cedar` body, a macro parameter is not a key: `{ ?x: 1 }`
  used to load with the literal key `?x`, never substituted, and is now
  refused. A body with a repeated or invalid key is refused when the file is
  parsed, even if the macro is never called
- **parser**: a call through a qualified name (`Ns::Fn(1)`) names the provider
  `Ns::Fn` however it is spaced. The name was taken from its text, so
  `Ns :: Fn(1)` called `Ns :: Fn`, and a comment after the name became part of
  it, which `expanded_source` then wrote out, commenting out the rest of the
  policy
- **render**: `expanded_source` quotes a record key that Cedar reserves
  (`{ "true": 1 }`), which it used to write bare

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
