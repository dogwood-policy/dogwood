# 0110 — Naming a rule with `@id`

Rules can carry an `@id("...")` annotation that gives the rule
a stable, human-readable name. The annotation appears on the
line before `permit` / `forbid`:

```
@id("sell_small_only")
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
when {
    context.input.shares <= 50
};
```

## What `@id` does

The id is metadata. It does **not** affect evaluation: the rule
still matches exactly the same requests it would without the
annotation (here, `SellShares` calls with `shares <= 50`).
What it gives you is a label that diagnostics, audit logs, and
reports can use to point back at this specific rule — much
nicer than "the third rule in `policy_2.dw`".

## Placement and uniqueness

- `@id(...)` MUST precede the `permit` / `forbid` keyword. It
  binds to the rule that follows.
- Treat ids as a stable identifier across policy revisions:
  pick names you're willing to grep for and reference in
  tickets.

Ids are optional — every prior example (0001-0006) omitted them
and validated fine. Use them once a policy grows past a handful
of rules and you want to talk about individual rules without
ambiguity.
