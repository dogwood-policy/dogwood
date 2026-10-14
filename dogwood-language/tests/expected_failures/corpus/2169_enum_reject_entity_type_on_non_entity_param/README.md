# 2169_enum_reject_entity_type_on_non_entity_param

`entityType` only makes sense with `paramType: "entity"`.

Must be rejected with:
- ``entityType` is only valid with `paramType: "entity"``

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
