# 0113 — Probing optional context fields with `has`

The `context` record passed into a Dogwood rule has shape
`{ system, input, output? }`. The `output` field is **optional**:
it is present only after the tool has resolved. A request that
asks "may this call proceed?" *before* the tool runs carries no
`output`; a post-response check (the same tool call evaluated
again after it returned) does.

A rule that reads `context.output.X` directly is therefore
ill-defined on pre-output requests. The fix is `has`:

```
when {
    context has output && context.output.approved == true
}
```

`has` is a record-field probe that returns a `Bool`. Because
`&&` short-circuits, the right-hand access only runs when the
field is present, so the rule is well-typed for both pre- and
post-output evaluation.

## Pre-output vs post-output

| Phase        | `context has output` | Rule contributes? |
|---|---|---|
| pre-output   | `false`              | no (clause is false) |
| post-output, `approved == true`  | `true` | yes |
| post-output, `approved == false` | `true` | no |

The rule is silent on pre-output requests and only grants the
action once the tool has actually returned `approved: true`. This
lines up cleanly with the post-output guardrail pattern in
Section 5: any time you want a rule to fire only *after* a tool
resolves, gate it on `context has output`.

## Idiom for nested fields

For boolean output fields, an equivalent shape uses `if … then
… else …`:

```
when {
    if context has output then context.output.approved else false
}
```

Both forms are interchangeable. Pick whichever reads better at
the call site; the `&&` form composes more naturally when other
post-output conditions follow.
