# 2150_enum_reject_unknown_param_type

A misspelled paramType carrying an `entityType` is rejected instead of silently becoming String (unknown kinds without an entity type are still accepted; see case `0053_enum_accept_unknown_param_type_without_entity_type`).

Must be rejected with:
- `unknown paramType `entiy``

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
