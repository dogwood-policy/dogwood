# 0114 — Rule scope unlocks the per-tool input shape

The `action ==` constraint in a rule's scope is more than a filter
for which requests the rule applies to — it also tells the type
checker which tool's input record `context.input` resolves to
inside the body.

## Two scopes, two input shapes

`policy_1.dw` is scoped to `SellShares`, whose input is
`{ stock: String, shares: Long }`. Inside the body,
`context.input.shares` is a `Long`, so `< 100` type-checks.

`policy_2.dw` is scoped to `GetStockInfo`, whose input is
`{ stock: String }` — there is no `shares` field. Inside that
rule, `context.input.stock` is a `String`, so `== "AMZN"`
type-checks. Writing `context.input.shares` in this rule would
fail validation because the GetStockInfo input record does not
declare a `shares` field.

## Why this matters

Without a single-action scope, `context.input` would have to be
the union of every tool's input shape, and only fields common to
all tools would be safely accessible. Pinning `action == ...`
lets you write per-tool rules that read tool-specific fields
directly. See 0002 for the basic `when` clause and 0001 for the
scope shape.
