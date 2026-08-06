# 0109 — Multiple Cedar clauses in one rule

A rule may carry any number of `when` and `unless` clauses.
They are conjoined: the rule applies only if **every** clause
body evaluates to true.

## Shape

```dogwood
permit (principal, action == Drupe::Action::"SellShares", resource)
when { context.input.shares < 100 }
when { context.input.stock == "AMZN" };
```

This is equivalent to a single `when` whose body ANDs the two
conditions together. Splitting them across clauses is purely a
readability choice — group one fact per clause when each one
stands on its own.

## `unless` composes the same way

Each `unless { B }` adds another `!B` conjunct to the rule's
guard. Mixing `when` and `unless` clauses on one rule is fine
and they are all conjoined together.

This composition rule is Cedar-only. Temporal clauses live
under a stricter regime (a rule can hold either temporal or
non-temporal clauses, never both); see Section 4 for how
temporal mixing is handled across rules.
