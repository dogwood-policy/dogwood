# 2170_enum_reject_fields_on_entity_param

An `entity` paramType takes no `fields` / `items` / `required`.

Must be rejected with:
- ``entity` paramType does not take `fields``

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
