# 0211 — denylist-by-pattern via `unless { … like … }`

This case combines two earlier ideas:

* pattern matching with `like` (see 0204), which lets a string
  comparison span an open-ended family of values, and
* the exception-shaped `unless` clause (see 0108), which carves
  values *out* of an otherwise broad permit.

## Shape

```dogwood
permit (
    principal,
    action == Drupe::Action::"GetStockInfo",
    resource
)
unless { context.input.stock like "TEST_*" };
```

A single rule permits `GetStockInfo` for every stock ticker
*except* those that begin with the literal prefix `TEST_`. The
`like` glob handles the open universe of disallowed values
(`TEST_AMZN`, `TEST_FOO`, `TEST_anything`); `unless` flips the
predicate so a match means "do not permit". Equivalent to
`when { !(context.input.stock like "TEST_*") }`, but reads more
naturally as "permit, with this exception".

## When to reach for this shape

Use the `unless { … like … }` shape when the disallowed values
have a *structural* form (a prefix, a suffix, a glob) rather than
an enumerated list. Enumerating with `!=` chains works only when
you know every excluded ticker; `like` lets a single clause cover
the whole family. Compare with 0003, where two explicit rules
(permit + forbid) achieve a similar denylist via deny-overrides —
use that shape instead when the exception needs its own clauses
or a separate principal/resource scope.
