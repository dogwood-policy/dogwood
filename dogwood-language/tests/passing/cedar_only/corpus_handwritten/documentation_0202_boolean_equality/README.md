# 0202 — Boolean equality

Bool fields can be compared with `== true` and `== false`. Both forms
are valid Cedar; the explicit equality reads more clearly in policy
text than relying on truthiness.

## Shape

`policy_1.dw` permits when the approval is true:

```
when { if context has output then context.output.approved == true else false }
```

`policy_2.dw` is the dual — a `forbid` that fires when the approval
is explicitly false:

```
when { if context has output then context.output.approved == false else false }
```

## Notes

`context.output.approved` on its own and `!context.output.approved`
are also valid Bool expressions, so `when { ... approved }` and
`when { !... approved }` would type-check too. We prefer the explicit
`== true` / `== false` form because policy authors and reviewers
should not have to recall whether a field is Bool versus, say, an
optional that needs a `has` probe.

Both files use the `if context has output then ... else false` guard
because `output` is optional on tool actions in the shared schema
(see the curriculum intro). When the tool has not yet resolved,
neither rule fires and the request falls back to default-deny.

See 0003 for `forbid` and deny-overrides semantics — combining
`policy_1.dw` and `policy_2.dw` in the same deployment is redundant
(the forbid never adds denials the missing-permit wouldn't already
produce), but each illustrates one half of the equality idiom.
