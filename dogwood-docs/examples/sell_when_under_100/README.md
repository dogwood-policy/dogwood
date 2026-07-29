# sell_when_under_100

A basic `when { ... }` condition clause: a `when` body must evaluate true for
the rule to fire. Here the rule permits `SellShares` only when the order is a
strict share threshold under 100 (`context.input.shares < 100`).

Referenced by `guide/02-policy-language.md` — The Policy Language.
