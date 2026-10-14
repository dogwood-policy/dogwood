# 2176_enum_reject_declared_name_in_action_schema

The action schema declares `MyGuardrails::Score`, the same name as the provider enum. Policies write provider enum literals by their declared name, so `MyGuardrails::Score::"LOW"` would be ambiguous between the action schema's type and the provider enum. Lowering rejects it.

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
