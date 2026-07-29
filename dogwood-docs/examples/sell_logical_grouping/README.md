# sell_logical_grouping

Logical connectives `||`, `&&`, and `!` with parenthesized grouping to override
precedence. `&&` binds tighter than `||`, so the small-or-AMZN test is wrapped in
parentheses to keep it as a single disjunction before it is ANDed with the
"not BLOCKED" guard: permit `SellShares` when the request is for fewer than 100
shares OR the stock is `AMZN`, AND the stock is not `BLOCKED`.

World: drupe (schema shared with the other Drupe examples).

Referenced by `guide/02-policy-language.md` — The Policy Language.
