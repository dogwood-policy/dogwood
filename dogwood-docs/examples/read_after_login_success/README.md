# read_after_login_success

Response predicate + output-field filter: permit a `Read` only if the **same
user** had a `Login` that **succeeded** (`output.result: true`) within the last
hour. A response predicate reads `output.*` fields and matches the *result*
event, not the request — so it can gate on the login's outcome.

The trace shows both verdicts:

- `@100` — alice reads `doc1`, 100s after a `Login::response` with
  `output.result: true` for alice → **ALLOW** (a matching successful login is
  within the window).
- `@300` — bob reads `doc2`, after a `Login::response` with
  `output.result: false` for bob → **DENY** (the login failed, so the
  `output.result: true` filter rejects it).

Referenced by `guide/04-temporal-expressions.md`.
