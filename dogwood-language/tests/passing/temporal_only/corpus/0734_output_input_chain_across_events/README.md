# 0734 output→input chaining across events

Demonstrates **data-flow chaining** between two distinct past events: a
value produced as one event's *output* is joined to another event's
*input* through a shared existential variable — the temporal analogue of
`exists a. (resolved_grant{ output.amount: a } && request_charge{ input.amount: a })`.

The `Read` policy permits only when, for the same user, there exists an
amount `a` such that:

- a prior `Grant::response` *returned* `output.amount == a`, **and**
- a prior `Charge::request` *was asked for* `input.amount == a`.

`exists (a: Long). (…)` introduces the join variable; `output.amount: a`
binds it from the response (a range-restrictor), and `input.amount: a`
then constrains the charge to carry that same value. Without a single
amount that was both granted and charged, the existential is empty and
the rule does not fire.

## Trace and verdicts

- **alice** is granted `500` (`@1` response) and charges `500` (`@2`),
  so at her `Read` (`@3`) the join succeeds on `a = 500` → **true**.
- **bob** is granted `300` (`@5`) but charges `999` (`@6`), so no shared
  `a` exists and his `Read` (`@7`) → **false**.

### Why there are verdicts at the `Charge` timepoints

Under the request/response event schema, `Charge::request` is itself a
**decision** event, so it receives its own verdict (`@2`, `@6`). The
`Read`-scoped policy never applies to a `Charge` action, so those
verdicts are `false`. Only `@3` and `@7` are the `Read` decisions this
case is about. (`Grant::request` at `@0`/`@4` likewise gets a `false`;
the `response` events at `@1`/`@5` are history-only and produce no
verdict.)
