# 0103 — Principal-typed scope

Scopes can constrain by **entity type** as well as by equality.
The `is` form restricts a rule to a particular principal type:

```
permit (
    principal is Drupe::OAuthUser,
    action == Drupe::Action::"GetStockInfo",
    resource
);
```

This rule fires only for requests whose principal is an
`Drupe::OAuthUser`. An `Drupe::IamEntity` or
`Drupe::UnauthenticatedUser` making the same call does not
match and falls through to the default deny (see 0001 for
default-deny semantics).

## The three principal types

The Drupe template ships three principal entity types:

- `Drupe::OAuthUser` — a human caller authenticated through
  an OAuth flow. Carries an `id` attribute and string tags.
- `Drupe::IamEntity` — an AWS IAM principal (role or user)
  with an `id` attribute.
- `Drupe::UnauthenticatedUser` — anonymous callers.

`OAuthUser` is the most common case for tool authorization, so
it's the one used here.

## `is` vs `==`

`principal is T` is a **type** predicate — it does not require
an equality constant. Use it when the rule should apply to every
principal of a given type. `principal == T::"alice"` would pin
the rule to a single named principal instead.
