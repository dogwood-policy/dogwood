# alert_same_user_login_and_transfer

A shared `exists` variable **joins** two different predicates through a common
value: permit an `Alert` only if the **same** user both logged in *and* made a
transfer within the last hour. Binding `u` across both `formerly`s is the whole
point — a broken join that accepted "some login AND some (other-user) transfer"
would wrongly permit.

The trace shows both outcomes and the discriminating case:

- `@0` — alice `Login` (history-only event; no `Alert`, so deny).
- `@1` — alice `Alert` with a login but **no** transfer yet → **deny**.
- `@2` — alice `Transfer` (history-only event → deny).
- `@3` — alice `Alert` after both her login (`@0`) and transfer (`@2`) →
  **allow** (one user satisfies both sides of the join).
- `@5000` — bob `Login`; `@5001` — carol `Transfer` (both history-only → deny).
- `@5002` — carol `Alert`: a login (bob) and a transfer (carol) both exist in
  the window, but **no single user did both** → **deny**. This is what the
  shared-`u` join buys you; a broken join would wrongly allow here.

Referenced by `guide/04-temporal-expressions.md`.
