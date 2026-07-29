# sell_after_2024_datetime

A single `datetime` literal compared with an ordinary comparison operator
(`>`) — no datetime operator arithmetic. Permits `SellShares` only when the
request's `context.system.now` is later than `datetime("2024-01-01T00:00:00Z")`.

Referenced by `guide/02-policy-language.md` — The Policy Language.
