# 0108 — `unless` is the negation of `when`

Some constraints read more naturally as exceptions than as
positive conditions. Dogwood offers `unless { B }` as sugar
for `when { !B }` so the policy can be written in whichever
direction matches intent.

```
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
unless {
    context.input.shares > 10000
};
```

This rule permits `SellShares` for any request *except* one
asking to sell more than 10000 shares. Equivalently, it could
have been written as `when { context.input.shares <= 10000 }`
(see 0002 for the positive `when` shape). Pick the form that
reads better at the call site.

## Semantics

`unless { B }` matches the request iff `B` evaluates to false.
A rule with multiple clauses still requires every clause to
match — `unless` joins the others with conjunction, just like
`when`. There is nothing else new here; `unless` is purely
syntactic.
