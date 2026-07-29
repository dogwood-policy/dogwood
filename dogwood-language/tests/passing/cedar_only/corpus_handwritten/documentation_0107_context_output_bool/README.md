# 0107 — Reading a Bool field from `context.output`

Earlier cases narrowed a permit by inspecting the tool's *inputs*
(see 0002 for `context.input.shares`). A clause can also inspect
the tool's *outputs* — the values the tool produced — through
`context.output.X`.

```
permit (
    principal,
    action == Drupe::Action::"ApproveSale",
    resource
)
when {
    if context has output
    then context.output.approved == true
    else false
};
```

`ApproveSale` declares its output as `{ approved: Bool }`, so
`context.output.approved` is a `Bool`. House style is to compare
Bool fields explicitly against the literals `true` and `false`:
`context.output.approved == true`. Writing the bare expression
`context.output.approved` would also type-check (it is already a
Bool), but the `== true` form makes the intent obvious to readers
and keeps the shape uniform with numeric and string comparisons
elsewhere in the curriculum.

## Why the `has output` guard

In the Drupe schema, `output` is declared optional on tool
actions: a request being evaluated may or may not carry the
result of a tool call yet. A clause that mentions
`context.output.X` without first proving `context has output`
fails type-checking. The standard idiom for a Bool output field
is:

```
if context has output then context.output.approved else false
```

or, when comparing explicitly,

```
if context has output then context.output.approved == true else false
```

The `else false` branch makes the rule simply not match when no
output is attached, which combines correctly with the
default-deny semantics from 0001.
