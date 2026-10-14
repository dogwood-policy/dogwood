# 0055_enum_only_referenced_enums_are_injected

Only the enums referenced by the providers a policy set calls are injected.

One `providers.json` serves two vendors: `Netskope::Scan` (typed by `Netskope::RiskLevel`) and `MyGuardrails::ContentFilter` (typed by `MyGuardrails::Score`). The action schema declares its own `MyGuardrails::Score`, so injecting the provider enum of that name would be an error (compare `2176_enum_reject_declared_name_in_action_schema`).

This policy calls only `Netskope::Scan`, so only `Netskope::RiskLevel` is injected (as `Drupe::Netskope_RiskLevel`) and the policy lowers, validates and evaluates. The unused vendor's enum cannot make it fail. This matches how provider fields are hoisted: only for the provider calls a policy set makes.
