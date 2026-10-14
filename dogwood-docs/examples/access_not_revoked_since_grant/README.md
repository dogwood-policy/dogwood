# access_not_revoked_since_grant

The "open session" idiom: a **negated left operand** on `since` expresses "has
not happened since." Because `!` binds tighter than `since`, `!A since within W
B` negates only `A`, giving "no `A` has happened since `B`." Here: permit an
`Access` only if a completed grant has been observed for this user and resource
within the last hour, with no completed revocation observed since
(`!Revoke::response since within 1h Grant::response`, with both `input.user`
and `input.resource` pinned).

The trace shows a delayed revocation notice, with timestamps in seconds since
midnight. Access is revoked at 10:00, but the notice arrives at 10:02:

- `@35940` (09:59) — `Grant::response` reports a completed grant for `doc1`/`alice`
  (history-only; no verdict).
- `@36060` (10:01) — `alice` requests access to `doc1`, with no revocation
  observed since the grant → **allow**.
- `@36120` (10:02) — `Revoke::response` reports the completed revocation for
  `doc1`/`alice` (history-only; no verdict); the notice was delayed.
- `@36180` (10:03) — `alice` requests access to `doc1` again, but a revocation
  has now been observed since the grant → **deny**.

Had the revocation notice arrived before the 10:01 request, that request would
have been denied. Increasing timestamps cannot compensate for missing history,
and the late notice does not revise the earlier verdict.

Referenced by `guide/04-temporal-expressions.md`.
