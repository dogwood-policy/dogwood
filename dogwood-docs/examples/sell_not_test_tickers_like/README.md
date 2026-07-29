# sell_not_test_tickers_like

The `like` string-pattern operator used under `unless` as a denylist idiom: a
`permit` for `SellShares` is retracted whenever the requested ticker matches the
`TEST_*` family, rejecting a whole value family in one condition.

Referenced by `guide/02-policy-language.md` — The Policy Language.
