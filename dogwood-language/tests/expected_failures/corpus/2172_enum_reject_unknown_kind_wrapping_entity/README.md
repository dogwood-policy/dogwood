# 2172_enum_reject_unknown_kind_wrapping_entity

A misspelled paramType (`recrod`) wrapping an
entity-typed field is rejected: falling back to `String` would hide the enum,
switching off literal checking and fail-closed conversion.

Must be rejected with:
- ``outputType: unknown paramType `recrod` ``
