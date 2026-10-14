# 0077_enum_guardrails_same_enum_name_in_each_vendor

Both vendors call their enum `Severity`. `BedrockGuardrails::Severity` and `GuardDuty::Severity` are exported as `Drupe::BedrockGuardrails_Severity` and `Drupe::GuardDuty_Severity`, two distinct types, so there's no collision. The policy uses both.

Trace: `hello` allowed, `kill` (Bedrock HIGH) denied, `malware` (GuardDuty HIGH) denied.
