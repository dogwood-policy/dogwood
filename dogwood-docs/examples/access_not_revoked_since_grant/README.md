# access_not_revoked_since_grant

The "open session" idiom: a **negated left operand** on `since` expresses "has
not happened since." Because `!` binds tighter than `since`, `!A since within W
B` negates only `A`, giving "no `A` has happened since `B`." Here: permit an
`Access` only if the user has **not** been `Revoke`d on this resource since they
were `Grant`ed it within the last hour (`!Revoke since within 1h Grant`, with
both `input.user` and `input.resource` pinned).

The trace shows both outcomes:

- `@0` — `Grant` for `doc1`/`alice` (a history-only event here; no `Access`
  permit applies, so the decision is a deny).
- `@100` — `alice` accesses `doc1`, after the grant and with no intervening
  revoke → **allow** (the not-revoked-since-grant chain holds).
- `@200` — `Revoke` for `doc1`/`alice` (history-only; deny).
- `@300` — `alice` accesses `doc1` again, but a `Revoke` now sits between the
  grant and this access → **deny** (the negated-left chain is broken).

Referenced by `guide/04-temporal-expressions.md`.
