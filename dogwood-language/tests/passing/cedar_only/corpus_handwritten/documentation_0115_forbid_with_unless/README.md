# 0115 — `forbid` with `unless`

The dual of permit-with-`when` (see 0002): a `forbid` rule with
an `unless` clause. `unless { B }` is just sugar for
`when { !B }`, but the keyword pairing reads more naturally with
`forbid`.

## Shape

```dogwood
forbid (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
unless { context.input.shares <= 100 };
```

Read it as English: *forbid SellShares unless the request is
small.* Equivalently, `forbid … when { context.input.shares > 100 }`.
Use whichever direction makes the policy intent clearer at the
call site.

## Composing with a permit

Recall deny-overrides + default-deny from 0003: a request is
allowed iff some `permit` matches **and** no `forbid` matches.
This rule on its own never authorizes anything — it only vetoes
large SellShares requests. To get a working policy, combine it
with a `permit` (e.g. the bare permit from 0001). Together they
mean: "allow SellShares, but block requests over 100 shares."
