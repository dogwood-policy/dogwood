# sell_when_unless_mix

Mixing `when` and `unless` clauses on a single `permit` rule. Because clauses
are conjoined, this permit fires only when **both** hold: the sale is capped
(`context.input.shares <= 1000`) **and** the stock is not blocked
(`unless { context.input.stock == "BLOCKED" }`).

Referenced by `guide/02-policy-language.md` — The Policy Language.
