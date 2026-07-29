# call_cedar_macro_is_small

A `def cedar` macro called in an ordinary `when { … }` position:
`is_small(context.input.shares)` slots into the clause exactly like plain
Cedar. The macro is defined in the macro library (`macros.dw`, supplied via
`--macros`), not redeclared in `policy.dw`, and it guards a `SellShares`
permit against the reusable Drupe schema.

Validate with:

```
dogwood validate policy.dw --policy-schema schema.cedarschema --macros macros.dw
```

Referenced by `guide/09-calling-macros.md`.
