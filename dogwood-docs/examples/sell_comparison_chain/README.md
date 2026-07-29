# sell_comparison_chain

Several comparison operators chained in a single `&&` conjunction on a `Long`.
Comparisons chain and fold left, so a range check plus an inequality
(`shares >= 1 && shares <= 1000 && shares != 777`) all live in one `when` block
over `context.input.shares` (a `Long`, which supports the full ordered set of
comparison operators).

Referenced by `guide/02-policy-language.md` — The Policy Language.
