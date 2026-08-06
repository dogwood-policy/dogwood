# 0201 — Decimals compare with `==` / `!=` only

Dogwood borrows Cedar's decimal type for fields like
`SellShares.proceeds` (see 0006 for an earlier proceeds-style
example). Decimals are deliberately restricted: you can ask
*equal* or *not equal*, but you cannot order them.

```
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
when {
    context has output && context.output.proceeds != decimal("0.0")
};
```

## The new idea

- A `decimal("...")` literal is the only way to write a decimal
  constant. The string form pins the precision exactly.
- The validator only accepts `==` and `!=` on decimal operands.
  Writing `context.output.proceeds < decimal("100.0")` would
  fail type-checking — there is no `<` for decimals here.
- `output` is optional in the tool-action context, so reads of
  `context.output.X` should be guarded with `context has output`
  (or `if context has output then ... else ...`). The guard is
  what makes the access well-typed when the tool hasn't resolved
  yet.

## Patterns when you actually need a threshold

If a policy needs an ordered comparison on a money-like value,
reach for an integer-typed field instead. The shared schema
exposes `context.input.shares` as `Long`, so a request-time
threshold like "reject any sale of 1000+ shares" is expressible
directly with `<` / `>=`. For aggregate amounts, sum an integer
field inside a temporal `let total = sum a where ... in ...`
aggregation and compare the integer total. Keep `proceeds` for
presence checks (`!= decimal("0.0")`) and exact matches.
