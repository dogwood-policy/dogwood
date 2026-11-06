# sell_comparison_chain

Several comparisons combined in a single `&&` conjunction on a `Long`. A range
check plus an inequality (`shares >= 1 && shares <= 1000 && shares != 777`) all
live in one `when` block over `context.input.shares` (a `Long`, which supports
the full ordered set of comparison operators). Comparisons themselves do not
chain: `1 <= shares <= 1000` is rejected and must be written with `&&`.

Referenced by `guide/02-policy-language.md` — The Policy Language.
