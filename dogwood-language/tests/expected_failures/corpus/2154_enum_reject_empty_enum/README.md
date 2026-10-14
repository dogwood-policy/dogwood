# 2154_enum_reject_empty_enum

An enum must list at least one value.

Must be rejected with:
- `enum `MyGuardrails::Score` has no values`

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
