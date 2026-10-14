permit(principal, action == Drupe::Action::"Read", resource) when { true };
forbid(principal, action == Drupe::Action::"Read", resource) when { ((context.providers).policy_1_p_0).greaterThan(decimal("0.5")) };
forbid(principal, action == Drupe::Action::"Read", resource) when { ((((context.providers).policy_2_p_0).JAILBREAK).confidenceScore).greaterThan(decimal("0.5")) };
forbid(principal, action == Drupe::Action::"Read", resource) when { !(((context.providers).policy_3_p_0) <= 0) };
forbid(principal, action == Drupe::Action::"Read", resource) when { (((context.providers).policy_4_p_0).threatSeverity) == "HIGH" };
