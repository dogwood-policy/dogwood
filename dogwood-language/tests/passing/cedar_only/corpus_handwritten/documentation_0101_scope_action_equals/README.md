# 0101 — Scope: `action ==` pins one tool

The scope's middle slot is where you say *which tool* a rule is
about. The standard form is equality against a fully-qualified
Cedar UID:

```
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
);
```

This rule applies only to invocations of `SellShares`. A request
to `GetStockInfo` or `ApproveSale` does not match this rule, so
it is not permitted by it (and, since the default decision is
deny, would be denied unless some other rule permits it).

## Why scope, not `when`?

You could in principle write the same restriction as a `when`
clause comparing `action`. Don't. The scope slot is the
idiomatic place for tool selection — it is more readable, it
is what every other example in this curriculum uses, and the
validator and downstream tooling can specialise on it. Reserve
`when` for predicates over `context`, `principal` attributes,
and `resource` attributes (see 0002 for the canonical pairing
of `action ==` with a `when` clause that narrows by input).

## Bare `principal` and bare `resource`

The other two scope slots are unconstrained here. Bare
`principal` means "any principal" and bare `resource` means
"any resource". Later cases will show how to constrain those
slots too.
