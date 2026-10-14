# refund_budget_settled_plus_current

> **EXPERIMENTAL.** This bundle uses arithmetic in temporal comparison
> operands, gated behind the off-by-default Cargo feature
> `experimental-arithmetic`. A default build rejects this policy; the test
> harnesses check this bundle only when built with that feature.

This bundle exercises `+` between a `sum` and a `context` field (a budget
combining unlike sources).

Permit a `Refund` only when the settled refund value in the window
(`Refund::response` amounts), plus the amount being requested right now,
stays at or under 100.

```text
permit (principal, action == Drupe::Action::"Refund", resource)
when temporal {
    (sum a for (a: Long), (t: Timepoint). where (
        formerly within 24h (Drupe::Action::"Refund"::response{ output.amount: a } && tp(t))
    )) + context.input.amount <= 100
};
```

When a sum matches the *same* event kind the policy decides, the `+` term is
not just unnecessary but wrong: temporal windows are closed and reflexive, so
such a sum already includes the in-flight request's amount, and adding
`context.input.amount` double-counts it. Here the sum matches `response`
events, the request being decided is a `request`, and nothing else puts its
amount into the total — the `+` term is genuinely load-bearing. Counting
responses is also the more accurate accounting: a denied refund does not
consume budget.

## Replay

| Decision point | This request | Settled + this request | Verdict |
|---|---|---|---|
| `@0` | 60 | 0 + 60 = 60 | allow |
| `@10` | 50 | 60 + 50 = 110 | deny |
| `@20` | 30 | 60 + 30 = 90 | allow |
| `@30` | 15 | 90 + 15 = 105 | deny |
| `@40` | 10 | 90 + 10 = 100 | allow |

The denied `@10` request never settles, so its 50 does not count at `@20` —
contrast a request-kind quota, where a denied attempt stays in the trace and
keeps counting. `@40` sits exactly at the budget (closed bound).

## Files

- `policy.dw`: the permit with the settled-sum-plus-current guard.
- `schema.cedarschema`: `Drupe` action schema with `Refund` only
  (`RefundOutput` carries the settled `amount`).
- `trace.log`: five refund requests by alice; the allowed ones settle with a
  matching `response`.
- `expected.out`: the per-decision-point verdict stream.

Reproduce (run from this directory):

```
dogwood validate policy.dw --policy-schema schema.cedarschema
dogwood replay   policy.dw --policy-schema schema.cedarschema --trace trace.log
```

World: `drupe`. Default event schema; no providers.

Referenced by guide/04-temporal-expressions.md (arithmetic in comparison
operands).
