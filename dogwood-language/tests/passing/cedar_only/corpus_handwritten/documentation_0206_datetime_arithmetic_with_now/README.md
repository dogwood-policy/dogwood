# 0206 — Datetime arithmetic with `context.system.now`

The new idea: `context.system.now` is a `datetime` and can be
compared against datetime literals (see 0111 for literal syntax)
using the full set of ordered comparison operators. The example
encodes a window-of-validity policy: SellShares is permitted iff
the request's wall-clock time falls inside calendar year 2025.

## Shape

```dogwood
when {
    context.system.now >= datetime("2025-01-01T00:00:00Z")
    && context.system.now < datetime("2026-01-01T00:00:00Z")
}
```

## Why this works for datetimes but not decimals

Datetimes are fully ordered: `<`, `<=`, `>`, `>=`, `==`, and `!=`
are all valid. Decimals in this dialect are restricted to `==`
and `!=` only — a half-open range like the one above cannot be
expressed over a `decimal` field. When you need ordered
comparisons on a numeric quantity, reach for a `Long` (e.g.
`context.input.shares`) or for `context.system.now`.

Note that this policy is purely non-temporal: it inspects the
request's own clock, not any past response events. For
"happened in the last hour" semantics, use `formerly within 1h`
(see 0005).
