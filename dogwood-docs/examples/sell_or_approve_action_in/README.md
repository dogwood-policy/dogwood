# sell_or_approve_action_in

`action in [ ... ]`: list-membership matching on the action. This rule permits
a request whose action is **either** `Drupe::Action::"SellShares"` **or**
`Drupe::Action::"ApproveSale"` — a compact alternative to writing two
separate `action == ...` rules.

Referenced by `guide/02-policy-language.md` — The Policy Language.
