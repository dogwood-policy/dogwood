# cedar_starts_with_f_like

A Cedar macro whose body is a `like` wildcard pattern: `starts_with_f(?s)`
wraps `?s like "F*"`. The macro is defined inline and used from a `permit`
rule that allows `GetStockInfo` only when `context.input.stock` starts with
the letter `F`.

This shows that a `def cedar` macro body can be any Cedar expression,
including a `like` pattern, not just a comparison.

Validate:

```text
dogwood validate policy.dw --policy-schema schema.cedarschema
```

Referenced by `guide/06-macros.md`.
