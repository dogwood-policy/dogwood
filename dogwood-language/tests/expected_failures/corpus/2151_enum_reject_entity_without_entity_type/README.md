# 2151_enum_reject_entity_without_entity_type

An `entity` paramType must name its entity type.

Must be rejected with:
- ``entity` paramType requires `entityType``

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
