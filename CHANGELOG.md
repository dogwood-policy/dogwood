# Changelog

All notable changes to the Dogwood policy language are documented here.

## 2026-08-26

### Added

- **engine**: `DecisionLeafMap` — which temporal leaves a decision can read, so
  any `TemporalEngine` can slice its per-decision work
  (`LoweredPolicySet::leaf_map`, `DecisionLeafMap::build`,
  `InMemoryTemporalEngine::slice_leaves`). Any miss means compute every leaf, and
  the answer may only shrink across versions, so a backend needs no change when
  the slicing gets finer; it is keyed by the request's action today

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
