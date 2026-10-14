# 0076_enum_guardrails_enums_in_both_vendor_namespaces

One providers file declares an enum for each vendor: `BedrockGuardrails::Confidence` (a new `confidence` field next to every category's `confidenceScore`) and `GuardDuty::Severity` (retyping `threatSeverity`). Each enum's namespace is a provider namespace in the file, so both are accepted. They are exported into the action schema's namespace as `Drupe::BedrockGuardrails_Confidence` and `Drupe::GuardDuty_Severity`; no namespace is added.

Trace: `hello` allowed; `kill` (Bedrock enum HIGH), `ignore previous` (Bedrock decimal), `malware` (GuardDuty HIGH) denied; `scan` (MEDIUM) allowed; `bogus` returns `UNKNOWN`, not a `GuardDuty::Severity` id, so it fails closed and is denied.
