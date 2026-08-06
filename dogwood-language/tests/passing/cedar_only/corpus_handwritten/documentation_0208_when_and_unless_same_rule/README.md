# 0208 — `when` and `unless` on the same rule

A rule may carry any number of `when` and `unless` clauses.
The rule fires only when every `when` body holds AND every
`unless` body fails. Read the rule below as: *permit small
sales, except for blocked stocks.*

```dogwood
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
when   { context.input.shares <= 1000 }
unless { context.input.stock == "BLOCKED" };
```

## Equivalent single-`when` form

The rule above is logically the same as folding the exception
into a single `when`:

```dogwood
when { context.input.shares <= 1000
    && !(context.input.stock == "BLOCKED") }
```

Both shapes validate and behave identically. Prefer the
`when` + `unless` split when the policy reads naturally as a
positive precondition with a carved-out exception: the `when`
states the rule's intent, the `unless` names the exception.
The single-`when` form is fine for tightly coupled conjuncts
but buries the exception inside a negation.

See 0108 for `unless` in isolation and 0002 for `when` in
isolation.
