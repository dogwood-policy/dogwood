# Dogwood Language — Release Notes

Release notes for the Dogwood policy language reference interpreter.

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



