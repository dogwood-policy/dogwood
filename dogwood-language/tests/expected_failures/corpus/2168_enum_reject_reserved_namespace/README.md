# 2168_enum_reject_reserved_namespace

Cedar reserves the `__cedar` namespace.

Must be rejected with:
- `reserved`

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
