# cedar_is_small_threshold

The simplest `def cedar` macro: `is_small(?n)` names the `< 100` threshold so
the bound lives in exactly one place, then calls it in a `when { … }` clause of
a `SellShares` permit. The macro is defined inline in `policy.dw` (no separate
`macros.dw`), and the default event schema is used.

Validate with:

```
dogwood validate policy.dw --policy-schema schema.cedarschema
```

Referenced by `guide/06-macros.md`.
