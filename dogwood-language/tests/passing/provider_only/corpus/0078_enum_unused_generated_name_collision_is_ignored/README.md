# 0078_enum_unused_generated_name_collision_is_ignored

The action schema declares `Drupe::GuardDuty_Severity`, which is the name `GuardDuty::Severity` would be exported as (compare `2193_enum_reject_generated_name_collision`). The policy set calls only Bedrock, so only `BedrockGuardrails::Confidence` is injected and the clash doesn't affect it.
