# 2166_enum_reject_duplicate_entity_type_key

The same entity type declared twice is rejected (plain serde maps keep the last silently).

Must be rejected with:
- `entity type `MyGuardrails::Score` is declared more than once`

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
