# 0003 — `forbid` overrides; order doesn't matter

So far we've only seen `permit`. The other kind of rule is
`forbid`. Its shape is identical to `permit` — same scope, same
clauses — but its meaning is the opposite: a matching `forbid`
**denies** the request.

The interesting case is when both kinds of rules apply to the
same request:

```
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
);

forbid (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
when {
    context.input.stock == "AMZN"
};
```

A request to sell `AMZN` matches both rules. The permit says
yes; the forbid says no. **The forbid wins.** This is Dogwood's
combining rule: a request is permitted only if at least one
`permit` matches *and* no `forbid` matches.

Three concrete cases to make this vivid:

| Request                      | Matches `permit`? | Matches `forbid`? | Verdict |
|---|---|---|---|
| `SellShares { stock: "GOOG" }` | yes | no  | **allow** |
| `SellShares { stock: "AMZN" }` | yes | yes | **deny** (forbid wins) |
| `ApproveSale { … }`            | no  | no  | **deny** (no permit) |

A useful way to read it: **a `forbid` carves a hole out of an
otherwise-allowing `permit`.** The permit alone would allow every
`SellShares`; the forbid removes AMZN from that set. Without the
permit, the forbid would have nothing to carve out of, and every
`SellShares` would already be denied by default.

## Order doesn't matter

`policy_2.dw` in this directory contains the same two rules as
`policy_1.dw`, but written in the opposite order — `forbid` first,
`permit` second. The verdict for every request is identical.

This is by design: the deny-overrides combining rule is a property
of the rule set, not of the source text. You can read a Dogwood
file in any order and reason about it the same way.
