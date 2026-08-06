# 0001 — The simplest permit

The smallest Dogwood policy that grants something:

```
permit (
    principal,
    action == Drupe::Action::"GetStockInfo",
    resource
);
```

It says: any principal can invoke the `GetStockInfo` tool on any
resource.

A few things to notice:

- A policy file is a list of **rules**. Each rule begins with
  either `permit` or `forbid`.
- Each rule has a **scope** — the parenthesised triple
  `(principal, action, resource)`. Bare `principal` and bare
  `resource` mean "any" of those; `action == ...` constrains
  the action to a specific tool.
- This rule has **no further conditions**. The semicolon at the
  end terminates the rule.

The action reference `Drupe::Action::"GetStockInfo"` is
the fully-qualified Cedar UID of the `GetStockInfo` tool
declared in the schema. Tool names are quoted strings; the
`Drupe::Action::` prefix is the namespace inherited from
the schema.

Dogwood's default decision when no rule matches is **deny**.
With only this rule in the file, every other tool — `SellShares`,
`ApproveSale`, anything else — would be denied.
