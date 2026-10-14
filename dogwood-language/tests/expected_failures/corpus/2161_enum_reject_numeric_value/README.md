# 2161_enum_reject_numeric_value

Enum ids are strings; a number is rejected, not coerced.

Must be rejected with:
- `expected a string`

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
