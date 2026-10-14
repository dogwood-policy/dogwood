permit(principal, action, resource) when { true };
forbid(principal, action, resource) when { (((context.providers).policy_1_p_0).result) == App::MyGuardrails_Score::"HIGH" };
