# Dogwood formatter

`dogwood-formatter` pretty-prints authored Dogwood (`.dw`) policy source
without parsing it into the semantic AST. It uses the shared
`dogwood-syntax` grammar and lossless token stream, preserving macro
definitions, strings, comments, and the exact spelling of operators and
identifiers.

```rust
let formatted = dogwood_formatter::format_policies(
    "permit (principal, action, resource) when { true };",
);
assert_eq!(
    formatted,
    "permit (principal, action, resource)\nwhen { true };",
);
```

The default layout uses an 80-column target and two-space indentation. It
changes whitespace only. If the shared syntax grammar rejects the source, a
string is unterminated, or a line comment occurs inside a statement, the
formatter returns the original source unchanged.

The `dogwood` binary exposes this as:

```text
dogwood format policy.dw
```
