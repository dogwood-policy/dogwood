# 2194_enum_reject_generated_name_collides_with_common_type

The action schema declares a common type `Drupe::MyGuardrails_Score`, the name `MyGuardrails::Score` is exported as. Entity and common type names share one name space in Cedar, so this is the same clash as `2193_enum_reject_generated_name_collision`.

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
