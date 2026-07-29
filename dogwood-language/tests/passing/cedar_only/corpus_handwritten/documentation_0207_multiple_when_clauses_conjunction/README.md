# 0207 — Multiple `when` clauses are conjoined

A single rule may carry more than one `when` clause. The rule
fires only if **every** `when` body holds, so stacking clauses
is equivalent to joining their bodies with `&&`.

## Shape

`policy_1.dw` uses two clauses, one per precondition:

```text
permit(principal, action == Drupe::Action::"SellShares", resource)
when { context.input.shares < 100 }
when { context.input.stock == "AMZN" };
```

`policy_2.dw` collapses them into one clause with `&&`:

```text
permit(principal, action == Drupe::Action::"SellShares", resource)
when { context.input.shares < 100 && context.input.stock == "AMZN" };
```

Both policies admit the exact same set of requests.

## Why prefer the multi-clause form

When each conjunct represents an independently meaningful
precondition — a size cap, a ticker allowlist, a tenant check —
the multi-clause form reads as a checklist: every line is one
thing the rule requires. This matters for audit readability and
for diffs that add or remove a single precondition without
reshuffling a long boolean expression.

For a tightly coupled expression (`x > 0 && x < 100`), the
single-clause `&&` form is fine. See 0002 for the original
single-clause shape and 0003 for how `forbid` rules combine
across a policy.
