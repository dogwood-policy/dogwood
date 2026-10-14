# 0061_enum_app_declares_same_simple_name

The action schema declares its own `Drupe::Score`. The provider enum `MyGuardrails::Score` is exported as `Drupe::MyGuardrails_Score`, so the two don't collide and the policy's `MyGuardrails::Score::"LOW"` binds to the provider enum.
