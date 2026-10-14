# 2164_enum_reject_nested_value

Nested arrays/objects are not enum ids.

Must be rejected with:
- `expected a string`

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
