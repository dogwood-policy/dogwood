# read_since_login

Positive-left `since within 1h`: the left operand must have **held
continuously since** the anchor. Permit a `Read` only if a `Login` by the same
user has held continuously since a `Login` by that user within the last hour
(`left since within W right`, the classic MFOTL `left S right`).

This is corpus case `0034_since_explicit`, lifted verbatim.

## What the trace shows

By the `since` semantics, `left since within W right` holds at the decision
timepoint `i` only if the left operand (`Login`) holds at **every** step from
just after the anchor through `i` itself. But the rule's scope is
`action == Read`, so every applicable decision point is a `Read` event — and a
`Read` event is never a `Login::request`. The left operand therefore fails at
the decision step, so the condition can never hold. **This policy is
structurally always-DENY** — matching corpus 0034, whose reference outputs are
all `false`. An ALLOW is not achievable for a faithful positive-left
`Login since Login` guarding a `Read`; interleaving extra logins between the
reads (verified against the CLI) does not change this.

The trace exercises the natural cases, all of which deny:

- `@0`, `@10` — two `Login`s by alice (history-only; the scope is `Read`, so no
  permit applies → deny).
- `@12`, `@20` — alice `Read`s within an hour of her logins. The anchor
  (`Login`) is in the window, but the left operand (`Login`) does not hold at
  the `Read` decision step, so the `since` is false → deny.
- `@30` — bob `Read`s with no prior login of his own → deny.

This is the intended contrast with the "open session" idiom (`!left since …`,
corpus `0418`/`0547`), where a *negated* left holds at the read step and the
policy can allow.

Referenced by `guide/04-temporal-expressions.md`.
