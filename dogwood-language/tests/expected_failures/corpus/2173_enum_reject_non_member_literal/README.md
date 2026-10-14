# 2173_enum_reject_non_member_literal

A literal outside the enum is rejected by Cedar's validator.

Must be rejected with:
- `is of an enumerated entity type`
- `not declared as a valid eid`

Must NOT contain (the pre-feature error shares the wording above):
- `the types String`
