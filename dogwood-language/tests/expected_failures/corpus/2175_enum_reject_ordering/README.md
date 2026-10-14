# 2175_enum_reject_ordering

Enum entities are unordered; `>` is a type error.

Must be rejected with:
- `but saw MyGuardrails::Score`

Must NOT contain (the pre-feature error shares the wording above):
- `but saw String`
