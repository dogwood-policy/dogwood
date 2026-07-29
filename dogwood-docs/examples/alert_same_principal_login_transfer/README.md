# alert_same_principal_login_transfer

An entity-typed `exists` binder that correlates on the **request principal**
via the reserved `callerPrincipal` field. The policy permits an `Alert` only
if the *same* principal both logged in (`Login`) and made a transfer
(`Transfer`) within the last hour — the join on the bound `pr:
Drupe::OAuthUser` variable is the whole point.

The guide illustrates the pattern with `Login` + `Deny`, but no shipped schema
declares a `Deny` action, so this example is adapted to `Login` + `Transfer`
(both present in the lifted `ea_0012_exists_correlation` schema). The shape of
the correlation — `callerPrincipal: pr` on both sides — is identical.

Schema lifted from the `temporal_only` corpus case
`ea_0012_exists_correlation` (declares `Login`, `Transfer`, `Alert`, and the
`OAuthUser` entity). Uses the default event schema.

Referenced by `guide/04-temporal-expressions`.
