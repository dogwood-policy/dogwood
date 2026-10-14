permit(principal, action == Drupe::Action::"Read", resource) when { true };
forbid(principal, action == Drupe::Action::"Read", resource) when { ((((context.providers).policy_1_p_0).VIOLENCE).confidence) in [Drupe::BedrockGuardrails_Confidence::"MEDIUM", Drupe::BedrockGuardrails_Confidence::"HIGH"] };
forbid(principal, action == Drupe::Action::"Read", resource) when { ((context.providers).policy_2_p_0).greaterThan(decimal("0.5")) };
forbid(principal, action == Drupe::Action::"Read", resource) when { (((context.providers).policy_3_p_0).threatSeverity) in [Drupe::GuardDuty_Severity::"HIGH", Drupe::GuardDuty_Severity::"CRITICAL"] };
