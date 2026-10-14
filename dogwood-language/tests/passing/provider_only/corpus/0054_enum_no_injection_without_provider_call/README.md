# 0054_enum_no_injection_without_provider_call

Enums declared in `providers.json` are injected only when the policy set calls a provider.

The action schema itself declares `MyGuardrails::Score`, the same name as the provider enum, which is an error for an injected enum (compare `2176_enum_reject_declared_name_in_action_schema`). This policy calls no provider, so nothing is injected and it lowers, validates and evaluates normally. Unused declarations cannot make a policy set fail.
