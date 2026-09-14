# Changelog

All notable changes to the Dogwood policy language are documented here.

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
