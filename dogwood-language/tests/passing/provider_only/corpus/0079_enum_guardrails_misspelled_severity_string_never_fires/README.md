# 0079_enum_guardrails_misspelled_severity_string_never_fires

**Before enums.** The guardrail declarations from `0075`, where
`GuardDuty::ThreatDetector` returns `threatSeverity` as a String. The policy
misspells the severity (`"HIHG"`). It validates without an error or warning,
because any String literal is a valid String. The forbid can never fire:

- `@0` `hello` → LOW → allowed.
- `@10` `malware here` → HIGH → **still allowed**. The guardrail silently does nothing.

Compare `2192_enum_reject_guardrails_misspelled_severity`, where the same typo
is rejected once `threatSeverity` is a `GuardDuty::Severity` enum.
