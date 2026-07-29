# traders_is_in_group_scope

The `is Type in Group` scope constraint: the `principal` slot both tests the
entity type (`is Drupe::OAuthUser`) AND requires hierarchy membership
(`in Drupe::Team::"traders"`). The policy permits `GetStockInfo` only for
principals that are `OAuthUser`s belonging to the `traders` team.

This uses a bespoke schema (`schema.cedarschema`) that adds `entity Team;` and
`entity OAuthUser in [Team] = { id: String } tags String;` so the membership
target `Drupe::Team::"traders"` type-checks — the stock `GetStockInfo`
schema has no `Team` type.

Referenced by `guide/02-policy-language.md` — The Policy Language.
