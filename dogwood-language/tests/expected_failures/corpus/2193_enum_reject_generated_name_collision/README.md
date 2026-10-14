# 2193_enum_reject_generated_name_collision

The action schema already declares `Drupe::MyGuardrails_Score`, the name `MyGuardrails::Score` is exported as. The name can't get a suffix: policies refer to it, and it must be the same in every schema that gets merged. So lowering fails.

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
