# Changelog

All notable changes to the Dogwood policy language are documented here.

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
