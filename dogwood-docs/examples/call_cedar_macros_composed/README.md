# call_cedar_macros_composed

Two Cedar macros composed with `&&` in one `when { … }` clause:
`is_eligible(context.input.shares, context.input.stock) && is_not_blocked(context.input.stock)`.
Both macros are defined in the macro library (`macros.dw`) and loaded via
`--macros`; each is called with a different argument shape (a `Long` and a
`String`), showing that `?p` literal-splicing carries call-site types through.

Validate with:

```
dogwood validate policy.dw --policy-schema schema.cedarschema --macros macros.dw
```

Referenced by `guide/09-calling-macros.md`.
