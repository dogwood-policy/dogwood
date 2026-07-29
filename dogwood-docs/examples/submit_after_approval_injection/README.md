# submit_after_approval_injection

A `def temporal` macro (`approved_recently`) whose predicate-valued parameter
`?s` is **refined inside the macro body** with an injected field
(`?s{ input.status: "approved" }`). The refinement forces the
`input.status: "approved"` filter onto whatever event the caller passes; the
call site never writes `input.status` -- it supplies only
`Drupe::Action::"Approve"::request{ input.user: context.input.user }`.
The window `?w` is filled at the call site with a bare interval literal (`1h`,
no `within` keyword). The policy permits a `Submit` only if the same user was
`formerly` Approved within 1h **with status "approved"**.

This is the load-bearing `?s{…}` refinement-in-macro-body path.

## Files

- `policy.dw` -- the macro definition and the `permit … when temporal { approved_recently(1h, …) }` rule.
- `schema.cedarschema` -- Cedar action schema (Approve + Submit under `Drupe`), lifted from macros corpus `0041_field_injection_omitted_field`.
- `trace.log` -- five events exercising both outcomes.
- `expected.out` -- captured verbatim from `dogwood replay`.

## Trace outcomes

| tp | event | verdict | why |
|----|-------|---------|-----|
| 0  | alice Approve (status "approved") | DENY  | only `Submit` is permitted |
| 1  | alice Submit | ALLOW | alice was formerly Approved within 1h with status "approved" |
| 2  | bob Submit   | DENY  | bob was never Approved |
| 3  | carol Approve (status "pending") | DENY | only `Submit` is permitted |
| 4  | carol Submit | DENY  | carol's prior Approve was status "pending" -- excluded by the injected `input.status: "approved"` filter |

## Reproduce

Run from this directory (so relative paths resolve):

```
dogwood validate policy.dw --policy-schema schema.cedarschema
dogwood replay   policy.dw --policy-schema schema.cedarschema --trace trace.log
```

## Note on the guide's `same_session` macro

The guide's literal `same_session` example (guide/04-temporal-expressions.md:482)
injects a deep context path (`context.__drupe.session.id`) and does **not**
pass `validate` -- the validator rejects that deep path (only the corpus's
replay-only test accepts it). This bundle substitutes the semantically
equivalent, *validating* field-injection macro from corpus
`0041_field_injection_omitted_field` to teach the same `?s{…}`
refinement-in-macro-body point.

Referenced by guide/04-temporal-expressions.
