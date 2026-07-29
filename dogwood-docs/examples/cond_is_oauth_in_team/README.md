# cond_is_oauth_in_team

The expression-level counterpart of the `is` / `is-in` scope constraint: an
entity-type + hierarchy membership test written inside a `when { ... }` body
rather than in the policy scope. The condition
`principal is Drupe::OAuthUser in Drupe::Team::"traders"` succeeds only
when the principal is an `OAuthUser` that also belongs to the `traders` team.

This reuses the bespoke schema (`schema.cedarschema`) from
`traders_is_in_group_scope`, which adds `entity Team;` and
`entity OAuthUser in [Team] = { id: String } tags String;` so the membership
target `Drupe::Team::"traders"` type-checks — the stock `GetStockInfo`
schema has no `Team` type.

Referenced by `guide/02-policy-language.md` — The Policy Language.
