# sell_datetime_window

Datetime ordered comparison expressing a calendar-year time window: permit
`SellShares` only when `context.system.now` falls within calendar year 2025
(`>= 2025-01-01T00:00:00Z` and `< 2026-01-01T00:00:00Z`). Because `datetime`
supports the full ordered set, the window is expressed directly with `>=` and
`<` — no temporal block is needed.

Referenced by `guide/02-policy-language.md` — The Policy Language.
