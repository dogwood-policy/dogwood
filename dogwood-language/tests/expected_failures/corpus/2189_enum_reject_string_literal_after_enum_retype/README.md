# 2189_enum_reject_string_literal_after_enum_retype

Migration hazard. The providers file is the one from
`0076_enum_guardrails_enums_in_both_vendor_namespaces`, where `threatSeverity` became a `GuardDuty::Severity` enum. An existing
policy still compares it with a String (`== "HIGH"`, as in `0075_enum_guardrails_legacy_providers_unchanged`),
and that is now a type error.

Changing an existing field from `string` to `entity` breaks policies already
written against it. Adding a new enum field (like `confidence`) does not.
