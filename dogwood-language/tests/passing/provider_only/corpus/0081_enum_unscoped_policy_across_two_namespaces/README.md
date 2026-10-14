# 0081_enum_unscoped_policy_across_two_namespaces

Two namespaces declare actions, `App` and `Audit`. The provider enum is exported once, as `App::MyGuardrails_Score`, and both namespaces' provider fields refer to that one type. So an **unscoped** `forbid … == MyGuardrails::Score::"HIGH"` fires on both namespaces' actions.

With a copy of the enum per namespace, the literal could name only one copy, and the forbid would silently never fire on the other namespace's actions (Cedar validates that without a warning).

- `@0` `App::Read` `hello` (LOW): allowed.
- `@10` `App::Read` `attack` (HIGH): denied.
- `@20` `Audit::Inspect` `hello` (LOW): allowed.
- `@30` `Audit::Inspect` `attack` (HIGH): denied.
