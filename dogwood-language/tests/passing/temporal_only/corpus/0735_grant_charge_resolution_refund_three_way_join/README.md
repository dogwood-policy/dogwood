# 0735 three-way join: two past events + the current request

Extends `0734`'s two-past-event chaining with a **third** join condition
on the *current* decision request. One existential variable `a` is pinned
by three independent facts:

```
exists (a: Long). (
    formerly within 1h Grant::response{ input.user: context.input.user, output.amount: a }   // (1) a past output
    && formerly within 1h Charge::response{ input.user: context.input.user, input.amount: a } // (2) a past input
    && context.input.amount == a                                                                 // (3) the current request
)
```

The `Refund` is permitted only for an amount that was **granted** (a past
`Grant::response` *returned* it), **actually charged** (a past
`Charge::response` *completed* for it), and **equals what this refund
asks for** (`context.input.amount`). Clause (1) binds `a` from a past
event's output; clause (2) constrains a second past event's input to that
value; clause (3) constrains the current request via a `==` comparison
against the decision context (a different mechanism from a predicate
field match).

## Why the charge is a `response`, not a `request`

Refunding against a mere *request* would let a charge that never went
through be refunded. Keying clause (2) on `Charge::response` means only
a **completed** charge qualifies — the "requested but not yet resolved"
(in-flight) case is correctly excluded. Row `@9` below is exactly that
case.

## Trace and verdicts

- **alice** is granted `500` (`@1`), her charge for `500` **resolves**
  (`@3`), so:
  - `@4` Refund `500` → **true** — all three clauses agree on `a = 500`.
  - `@5` Refund `400` → **false** — clauses (1) and (2) still hold for
    `500`, but the current request is `400`, so clause (3) fails. (Same
    user, identical history as `@4`; only the current amount differs —
    isolating clause (3).)
- **bob** is granted `300` (`@7`) and his charge for `300` is only
  **requested** (`@8`), never resolved:
  - `@9` Refund `300` → **false** — clauses (1) and (3) hold for `300`,
    but no `Charge::response` exists, so clause (2) fails. This is the
    in-flight charge that must not be refundable.

### Intermediate verdicts

`Charge::request` (`@2`, `@8`) and `Grant::request` (`@0`, `@6`) are
decision events, but the `Refund`-scoped policy never applies to them, so
each is `false`. The `response` events (`@1`, `@3`, `@7`) are
history-only and produce no verdict.
