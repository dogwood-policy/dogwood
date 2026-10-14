# 2192_enum_reject_guardrails_misspelled_severity

**After enums.** The typo from `0079_enum_guardrails_misspelled_severity_string_never_fires`
(`"HIHG"`), but `threatSeverity` is declared as the `GuardDuty::Severity`
enum (`LOW`, `MEDIUM`, `HIGH`, `CRITICAL`). Validation rejects the policy
because `"HIHG"` is not a member, so the mistake is caught before deployment
instead of letting HIGH threats through.
