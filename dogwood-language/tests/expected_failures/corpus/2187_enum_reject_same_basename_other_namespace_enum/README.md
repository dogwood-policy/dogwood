# 2187_enum_reject_same_basename_other_namespace_enum

A field typed `Drupe::Score` cannot feed a `MyGuardrails::Score` parameter, although both are named `Score`.

Must be rejected with:
- `has type `entity:Drupe::Score``
- `provider declares argument type `MyGuardrails::Score``

Types are compared by their fully-qualified name: comparing only the basename would accept this call and hand the script ids of the wrong enum.
