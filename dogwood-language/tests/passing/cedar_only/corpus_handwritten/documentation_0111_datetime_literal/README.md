# 0111 — datetime literals and `context.system.now`

## The new idea

Every request carries a wall-clock timestamp at
`context.system.now`. You can compare it against a literal
datetime written `datetime("<ISO-8601-UTC>")`.

```dogwood
when { context.system.now > datetime("2024-01-01T00:00:00Z") }
```

This rule permits `SellShares` only for requests issued strictly
after midnight UTC on 2024-01-01.

## What's allowed on datetimes

Unlike `decimal` (which is restricted to `==` and `!=`),
`datetime` supports the full ordered comparison set: `==`, `!=`,
`<`, `<=`, `>`, `>=`. The literal must be an ISO-8601 string in
UTC (`Z` suffix).

Datetime arithmetic — adding or subtracting a duration from
`context.system.now` to express "within the last hour" — is
covered in Section 3. For purely past-relative reasoning, prefer
the temporal clauses introduced from 0005 onward over hand-rolled
`now`-arithmetic.
