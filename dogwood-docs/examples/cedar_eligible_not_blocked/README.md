# cedar_eligible_not_blocked

Two `def cedar` macros of different argument types composed with `&&` inside one
`when { … }` clause. `is_eligible(?shares, ?stock)` takes a `Long` and a
`String`; `is_not_blocked(?stock)` takes a `String`. Composing them proves that
`?p` literal-splicing carries the call-site types (`context.input.shares: Long`,
`context.input.stock: String`) through macro expansion into the lowered Cedar.

Both macros are defined inline in `policy.dw` (no `macros.dw`). The schema is the
Drupe `SellShares` schema (`SellSharesInput.shares: Long`,
`.stock: String`); the default request/response event schema is used.

Validate with:

```
dogwood validate policy.dw --policy-schema schema.cedarschema
```

Referenced by `guide/06-macros.md`.
