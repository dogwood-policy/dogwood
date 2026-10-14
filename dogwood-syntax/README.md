# Dogwood syntax

`dogwood-syntax` is the shared, source-preserving syntax layer for
Dogwood (`.dw`) policy files. It owns the policy grammar, a lossless tokenizer,
and the concrete spans needed by both the semantic parser and the formatter.

The semantic `dogwood-language` crate builds its AST from this grammar.
The `dogwood-formatter` crate uses the same grammar and lossless tokens
while retaining comments, strings, authored operator spelling, and whitespace.
