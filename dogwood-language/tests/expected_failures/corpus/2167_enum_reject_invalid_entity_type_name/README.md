# 2167_enum_reject_invalid_entity_type_name

An `entityTypes` key must be a valid Cedar name.

Must be rejected with:
- ``MyGuardrails::Sco re` is not a valid Cedar entity type name`

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
