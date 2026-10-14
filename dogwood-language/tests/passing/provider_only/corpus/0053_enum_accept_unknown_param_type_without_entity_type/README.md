# 0053_enum_accept_unknown_param_type_without_entity_type

An unknown paramType that involves no entity type is deprecated but still accepted (typed `String`), so `"note": { "paramType": "strng" }` works next to an enum-typed field.

The script returns `note` (the input text) and the policy compares it with a String, so the fallback is pinned at validation (a non-String `note` would be a type error) and at runtime:

- `@0` `hello`: LOW, but `note` isn't `"maybe"` → not permitted.
- `@10` `maybe`: MEDIUM and `note == "maybe"` → permitted.
- `@20` `attack`: HIGH → not permitted.
