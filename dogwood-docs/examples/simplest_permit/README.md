# simplest_permit

The simplest possible policy: a bare `permit` for `GetStockInfo` with no
conditions. It has a scope triple (`principal`, `action ==
Drupe::Action::"GetStockInfo"`, `resource`) and no `when` / `unless`
clauses, so every `GetStockInfo` request is allowed.

Validate:

```
dogwood validate policy.dw --policy-schema schema.cedarschema
```

Referenced by `guide/02-policy-language.md` — The Policy Language.
