# 0100 — Bare scope, no constraints

The absolute minimum scope: every slot is left bare.

```
@id("allow_anything")
permit (
    principal,
    action,
    resource
);
```

Bare `principal`, bare `action`, and bare `resource` each mean
"any". With no clause body, this rule matches *every* request
and permits it. Compare 0001, which constrains `action` to a
specific tool; here even that constraint is dropped.

## The four request entities

A Dogwood authorization request is a 4-tuple. Three of them
are named in the rule scope; the fourth lives outside it:

- **`principal`** — who is making the request (e.g. an
  `Drupe::OAuthUser`).
- **`action`** — what they are trying to do (e.g.
  `Drupe::Action::"SellShares"`).
- **`resource`** — what they are acting on (e.g. an
  `Drupe::Gateway`).
- **`context`** — the ambient request data: `context.system.now`,
  `context.input.<field>`, and (when the action has run)
  `context.output.<field>`.

Only the first three appear in the scope triple. `context` is
never named there; you reach into it from inside clause bodies
(`when { context.input.shares < 100 }`, etc.).

## What "unconstrained" means

A bare scope slot is not a wildcard you have to match — it is
the absence of any predicate. The rule applies regardless of
which principal, action, or resource the request carries.
Narrowing happens by replacing a bare slot with `==` or `in`
(e.g. `action == Drupe::Action::"GetStockInfo"` from 0001),
or by adding a clause body that filters on `context`.

The `@id("allow_anything")` annotation is an optional label
attached to the rule. It has no effect on evaluation; it is
there so tooling and humans can refer to the rule by name.
