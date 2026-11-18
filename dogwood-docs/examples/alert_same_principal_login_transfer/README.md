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

A variable bound by a field must have a type every value of the field has.
`callerPrincipal` is declared `principalType(A)`: on an event of `Login`, it
holds an entity of any of `Login`'s principal types. So the schema declares
`OAuthUser` as the only principal type of `Login` and `Transfer`, and `pr:
Drupe::OAuthUser` accepts every value either field can hold. With the Drupe
template's three principal types (`IamEntity`, `OAuthUser`,
`UnauthenticatedUser`), validation rejects the binding. `Alert` applies to
`OAuthUser` principals only too: the default event schema pins
`callerPrincipal` to the request's principal, so an `Alert` by another type of
principal could never match a `Login` of an `OAuthUser`, and validation rejects
the pin.

Schema lifted from the `temporal_only` corpus case
`ea_0012_exists_correlation` (declares `Login`, `Transfer`, `Alert`, and the
`OAuthUser` entity), with `Alert`, `Login` and `Transfer` applying to
`OAuthUser` principals only. Uses the default event schema.

Referenced by `guide/04-temporal-expressions`.
