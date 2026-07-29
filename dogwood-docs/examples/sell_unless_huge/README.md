# sell_unless_huge

Basic `unless { ... }` clause: permit `SellShares` *unless* the order is
enormous (more than 10,000 shares). An `unless` clause blocks the rule when its
body holds, so it is exactly sugar for `when { !B }`.

Referenced by `guide/02-policy-language.md` — The Policy Language.
