# touchless_share_capped

> **EXPERIMENTAL.** This bundle uses arithmetic in temporal comparison
> operands, gated behind the off-by-default Cargo feature
> `experimental-arithmetic`. A default build rejects this policy; the test
> harnesses check this bundle only when built with that feature.

This bundle exercises `*` (ratio and percentage guards).

A share-of-total cap: touchless approvals may proceed only while they make
up at most 85% of the human decisions in the window. Percentages are written
cross-multiplied, which stays exact over integers; the language has no
division, deliberately.

```text
permit (principal, action == PriorAuth::Action::"TouchlessApprove", resource)
when temporal {
    100 * (count for (t: Timepoint). where (
        formerly within 24h (PriorAuth::Action::"TouchlessApprove"::response{} && tp(t))
    ))
    <= 85 * count for (t: Timepoint). where (
        formerly within 24h (PriorAuth::Action::"Decide"::response{} && tp(t))
    )
};
```

Note the fencing: the left aggregate is parenthesized (its greedy `where`
body would otherwise swallow the `<=`); the right one is the final position
of the final operand and stays bare.

## Replay

| Decision point | Event | 100 × touchless vs 85 × decided | Verdict |
|---|---|---|---|
| `@0`, `@2`, `@4` | human decisions d1–d3 | not `TouchlessApprove` | deny |
| `@10` | touchless t1 | 0 <= 255 | allow |
| `@20` | touchless t2 | 100 <= 255 | allow |
| `@30` | touchless t3 | 200 <= 255 | allow |
| `@40` | touchless t4 | 300 > 255 | deny |
| `@50` | human decision d4 | not `TouchlessApprove` | deny |
| `@60` | touchless t5 | 300 <= 340 | allow |

The `@50` human decision is what reopens automated capacity at `@60`.

## Files

- `policy.dw`: the permit with the cross-multiplied share cap.
- `schema.cedarschema`: `PriorAuth` action schema (`Decide`,
  `TouchlessApprove`).
- `trace.log`: three human decisions, four touchless attempts, one more
  human decision, one more touchless attempt.
- `expected.out`: the per-decision-point verdict stream.

Reproduce (run from this directory):

```
dogwood validate policy.dw --policy-schema schema.cedarschema
dogwood replay   policy.dw --policy-schema schema.cedarschema --trace trace.log
```

World: `priorauth`. Default event schema; no providers.

Referenced by guide/04-temporal-expressions.md (arithmetic in comparison
operands).
