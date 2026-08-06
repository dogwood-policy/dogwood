# 0106 — Reading `context.output` and decimal equality

Every `when` clause we've written so far looked at
`context.input` — the arguments the tool was invoked with. Tool
schemas also declare an *output* shape, and a policy can read it
through `context.output`. This case introduces two facts about
that read.

```
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
when {
    if context has output
    then context.output.proceeds == decimal("0.0")
    else false
};
```

## `output` is optional

In the shared schema the request context is
`{ system, input, output? }` — the `?` means `output` is only
present after the tool has resolved. A clause that mentions
`context.output.X` is therefore implicitly a *post-output* check:
it only makes sense once the result is in hand. Guard the read
with `context has output` (or an `if context has output then …
else …` like above) so the clause is well-typed for both
pre-response and post-response evaluation.

## Decimals only support `==` and `!=`

The `SellShares` action declares `proceeds` as a `decimal`.
Decimals in Dogwood are equality-comparable but not
order-comparable: `==` and `!=` are valid, while `<`, `<=`, `>`,
`>=` fail type-checking. Use integer fields like
`context.input.shares` (see 0002) when you need ordered
comparisons; reach for `proceeds` only for equality checks or
for sum aggregations in temporal bodies. Section 3 returns to
`context.output` with examples that read non-decimal output
fields and that compose output reads with temporal history.
