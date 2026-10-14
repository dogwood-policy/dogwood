# cap_open_agent_prs_windowed

> **EXPERIMENTAL.** This bundle uses arithmetic in temporal comparison
> operands, gated behind the off-by-default Cargo feature
> `experimental-arithmetic`. A default build rejects this policy; the test
> harnesses check this bundle only when built with that feature.

This bundle exercises `-` between two aggregates (a cap on open PRs).

A cap on concurrently open pull requests. A coding agent may hold at most
3 open PRs at once, so a new open is allowed only while fewer than 3 are
open, measured as opens minus completed reviews in the 24h window. The
guard runs before the new PR lands, which is why "at most 3 open" reads
as `< 3` at decision time.

```text
permit (principal, action == Repo::Action::"OpenPullRequest", resource)
when temporal {
    (count for (t: Timepoint). where (
        formerly within 24h (Repo::Action::"OpenPullRequest"::response{} && tp(t))
    ))
    - (count for (t: Timepoint). where (
        formerly within 24h (Repo::Action::"CompleteReview"::response{} && tp(t))
    )) < 3
};
```

Without arithmetic only the exact comparison `reviewed < opened` is writable;
the cap constant has nowhere to go. Both aggregates are parenthesized (the
fencing rule: an aggregate anywhere but the final position of the final
operand fences its greedy `where` body). The counts match `response` events,
so a *denied* open attempt does not consume the cap.

## Replay

`opened − reviewed` is the number of PRs open at the moment of decision;
the request being decided is not yet among them.

| Decision point | Event | Open PRs (opened − reviewed) | Verdict |
|---|---|---|---|
| `@0` | open r1 | 0 − 0 = 0 | allow (r1 is the 1st open PR) |
| `@10` | open r2 | 1 − 0 = 1 | allow (2nd) |
| `@20` | open r3 | 2 − 0 = 2 | allow (3rd) |
| `@30` | open r4 | 3 − 0 = 3 | deny (r4 would be the 4th) |
| `@40` | review v1 | not `OpenPullRequest` | deny |
| `@50` | open r5 | 3 − 1 = 2 | allow (back up to 3 open) |

The denied `@30` attempt has no `response`, so it does not count at `@50`;
the completed review at `@41` is what reopens capacity.

## Files

- `policy.dw`: the permit with the count difference.
- `schema.cedarschema`: `Repo` action schema (`OpenPullRequest`,
  `CompleteReview`).
- `trace.log`: four open attempts, one completed review, one more open, all
  by the agent principal `devin`.
- `expected.out`: the per-decision-point verdict stream.

Reproduce (run from this directory):

```
dogwood validate policy.dw --policy-schema schema.cedarschema
dogwood replay   policy.dw --policy-schema schema.cedarschema --trace trace.log
```

World: `repo`. Default event schema; no providers.

Referenced by guide/04-temporal-expressions.md (arithmetic in comparison
operands).
