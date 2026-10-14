# 2157_enum_reject_unknown_entity_type_key

An entry accepts only `enum` and `annotations`, like Cedar's. Any other key is rejected the same way, including Cedar's standard-entity keys (`shape`, `memberOfTypes`, `tags`): v1 declares enums only.

Must be rejected with:
- `unknown field `map``

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
