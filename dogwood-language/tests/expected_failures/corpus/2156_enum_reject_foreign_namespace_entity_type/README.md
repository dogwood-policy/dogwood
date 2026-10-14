# 2156_enum_reject_foreign_namespace_entity_type

A providers file may only declare entity types in its own providers' namespaces.

Must be rejected with:
- `entity type `Other::Score` is not in a provider namespace declared by this file`

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
