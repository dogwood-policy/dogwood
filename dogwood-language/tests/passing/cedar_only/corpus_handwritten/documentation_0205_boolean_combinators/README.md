# 0205 — Combining sub-conditions with `&&`, `||`, `!`

A `when` body is a boolean expression. Earlier examples used a
single comparison; real conditions usually combine several. The
three boolean operators are the standard ones:

- `!B` — negation
- `A && B` — conjunction
- `A || B` — disjunction

```
when {
    (context.input.shares < 100 || context.input.stock == "AMZN")
    && !(context.input.stock == "BLOCKED")
}
```

The rule permits `SellShares` when the trade is either small or
for `AMZN`, but never when the stock is on the blocked list.

## Precedence

`!` binds tightest, then `&&`, then `||`. Without parentheses
`a || b && c` parses as `a || (b && c)`. The example above
relies on the explicit parentheses around the `||` clause to
force the intended grouping; without them the `&&` would bind
to only the right operand of the `||`.

When in doubt, parenthesize. A redundant pair of parentheses is
cheaper than a subtle bug.

## `!(x == y)` vs. `x != y`

The negated equality `!(context.input.stock == "BLOCKED")` is
equivalent to `context.input.stock != "BLOCKED"`, and the `!=`
form usually reads better at the call site. Reach for `!` when
the sub-expression is genuinely a compound predicate (e.g.
`!(a && b)`); use `!=` for simple inequality.
