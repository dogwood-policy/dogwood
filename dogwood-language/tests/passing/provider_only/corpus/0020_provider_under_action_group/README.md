# 0020 — An information provider on an action group

Most provider cases scope a single action (`action == Ns::Action::"X"`).
This one gates a whole **action group** with one provider.

- **`schema.cedarschema`** declares an action hierarchy: `CallTool` is a
  parent group, and `Read` and `Post` are both members
  (`in [Action::"CallTool"]`).
- **`policy_1.dw`** scopes the rule `action in [Drupe::Action::"CallTool"]`
  — the group — and gates it with the `Strings::Matches` provider. The hoisted
  field lives in the shared `DogwoodProviders` common type referenced by the
  group's requestable descendants. Provider evaluation still occurs for every
  decision event; the group scope decides which requests the rule itself fires
  for (`Read`, `Post`).
- **`trace_1.log`** hits both descendants with an uppercase document
  (permit) and a non-uppercase one (deny):
  - `@0`  `Read`  document `"ABC"` → allow
  - `@10` `Post`  document `"XYZ"` → allow
  - `@20` `Read`  document `"abc"` → deny
  - `@30` `Post`  document `"xy9"` → deny

This is the end-to-end proof that a provider works under a non-`==` action
scope: the group is expanded to its descendants at lowering (recorded as
concrete target metadata), those actions reference the shared provider type,
and the rule fires for exactly the group's descendant actions.
