# 0112 — `if/then/else` inside a `when` body

A Cedar `when` body is an expression, and `if cond then a else b`
is itself an expression — so it can appear anywhere a value is
expected. The most useful place is when the *threshold* a request
must meet depends on some other field of the request.

```
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
when {
    if context.input.stock == "AMZN"
    then context.input.shares <= 10
    else context.input.shares <= 1000
};
```

Reading that aloud: permit `SellShares` when, **if** the ticker is
`AMZN`, the request asks for at most 10 shares; **otherwise** it
asks for at most 1000.

## Branch typing

Both branches of an `if` must produce the same type. Here both
branches are `Bool`, so the whole conditional is a `Bool` and is
usable as a `when` body. An `if` whose branches return integers
or strings would be valid as the *operand* of a comparison but
not as a `when` body on its own.

## Contrast with the two-rule form

`policy_2.dw` expresses the same intent by splitting into two
`permit` rules — one for `AMZN`, one for everything else. Either
shape is fine. The inline `if/then/else` keeps the per-field
threshold local to a single rule, which is easier to read once
you have more than two cases (chain `else if ...`). The two-rule
form is easier to extend when each branch needs its *own* extra
clauses; remember from 0003 that `permit` rules combine with
permit-overrides among themselves.
