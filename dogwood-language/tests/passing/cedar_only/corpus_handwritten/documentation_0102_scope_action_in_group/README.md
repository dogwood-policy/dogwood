# 0102 — Scope: `action in [...]`

When one rule should cover several tools, list them in a Cedar set
on the `action` position and use `in` instead of `==`.

```dogwood
permit (
    principal,
    action in [Drupe::Action::"SellShares", Drupe::Action::"ApproveSale"],
    resource
);
```

## Why no body?

Each listed action has its own input schema. `SellShares` has
`{ stock, shares }`; `ApproveSale` has `{ stock, shares }` too,
but other groupings (e.g. mixing in `GetStockInfo`, which has only
`{ stock }`) would not type-check against a body that referenced
`context.input.shares`. With a multi-action scope, the body is
limited to fields common to every listed action — often easier to
leave empty and let the scope itself do the work.

The next case (0104) shows the single-action form
(`action == Drupe::Action::"SellShares"`), which unlocks the
full tool-specific input shape inside `when`.
