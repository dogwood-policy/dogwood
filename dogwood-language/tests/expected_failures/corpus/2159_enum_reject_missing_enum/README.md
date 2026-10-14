# 2159_enum_reject_missing_enum

An entry must declare `enum` (an entry without it would be a standard entity type in Cedar).

Must be rejected with:
- `missing field `enum``

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
