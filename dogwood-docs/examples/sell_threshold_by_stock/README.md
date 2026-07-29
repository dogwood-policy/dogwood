# sell_threshold_by_stock

An `if / then / else` used as the whole body of a `when` clause reads like a
conditional rule: a stricter per-share cap for `AMZN` (`<= 10`) than for every
other stock (`<= 1000`). Because `if/then/else` is an expression, both branches
must produce the same type (here, `Bool`).

The trace exercises both branches, each in its allow and deny form:

- `@0` — alice sells 5 AMZN → the `then` branch (`5 <= 10`) → **allow**.
- `@100` — alice sells 50 AMZN → the `then` branch (`50 <= 10`) → **deny**.
- `@200` — bob sells 500 MSFT → the `else` branch (`500 <= 1000`) → **allow**.
- `@300` — bob sells 5000 MSFT → the `else` branch (`5000 <= 1000`) → **deny**.

Referenced by `guide/02-policy-language.md` — The Policy Language.
