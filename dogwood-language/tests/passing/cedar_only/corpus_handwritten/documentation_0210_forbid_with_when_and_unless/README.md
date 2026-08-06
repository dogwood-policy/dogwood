# 0210 — `forbid` with `when` and `unless`

A single rule may combine `when` and `unless` clauses. They are
conjoined: the rule fires only when every `when` body holds AND
no `unless` body holds. `unless { B }` is sugar for `when { !B }`,
so this is just a convenient way to express "deny broadly, with
a narrow exception" in one rule.

## Shape

```dogwood
forbid (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
when   { context.input.shares > 100 }
unless { context.input.stock == "AMZN" };
```

The forbid fires when the request asks for more than 100 shares
*and* the stock is not AMZN. Sales of 100 or fewer shares, or
sales of any size for AMZN, are not denied by this rule.

## A note on composition

Validation here is structural — a lone `forbid` is well-formed
on its own. But under deny-overrides with default-deny (see
0003), a request is permitted only when at least one `permit`
matches and no `forbid` matches. In a real policy, you would
pair this rule with a permissive rule (e.g. an unconditional
`permit` on `SellShares`, as in 0001) so that requests not
caught by the forbid actually go through. See 0003 and 0006 for
multi-rule patterns that combine `permit` and `forbid`.
