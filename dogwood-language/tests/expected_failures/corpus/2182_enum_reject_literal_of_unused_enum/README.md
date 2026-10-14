# 2182_enum_reject_literal_of_unused_enum

Only the enums referenced by the providers a policy set calls are injected, so a literal of any other declared enum is unknown to Cedar.

`MyGuardrails::Category` is declared in `entityTypes`, but the called `MyGuardrails::ContentFilter` refers only to `MyGuardrails::Score`. Comparing its result against `MyGuardrails::Category::"HATE"` is therefore rejected, where it would otherwise validate as an always-true `!=` (compare case `0073_enum_different_enum_comparison_is_accepted`).

Must be rejected with:
- ``unrecognized entity type `MyGuardrails::Category` ``
