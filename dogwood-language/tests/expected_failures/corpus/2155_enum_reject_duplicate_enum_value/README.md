# 2155_enum_reject_duplicate_enum_value

Enum values are unique.

Must be rejected with:
- `enum `MyGuardrails::Score` lists `LOW` more than once`

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
