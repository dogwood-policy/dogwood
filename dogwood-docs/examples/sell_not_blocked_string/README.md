# sell_not_blocked_string

String inequality (`!=`) — one of the two operators strings support (`==` and
`!=`). This policy permits `SellShares` for any stock **except** the sentinel
value `"BLOCKED"`: `when { context.input.stock != "BLOCKED" }`.

Referenced by `guide/02-policy-language.md` — The Policy Language.
