# 2177_enum_reject_shadowing_app_root_name

The root namespace declares `MyGuardrails_Score`. Exporting `MyGuardrails::Score` as `Drupe::MyGuardrails_Score` would shadow it, which Cedar forbids, so Dogwood reports it up front.

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
