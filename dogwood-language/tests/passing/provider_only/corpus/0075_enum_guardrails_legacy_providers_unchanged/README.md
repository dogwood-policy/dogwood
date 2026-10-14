# 0075_enum_guardrails_legacy_providers_unchanged

A multi-vendor guardrail declarations file (`BedrockGuardrails::*` and
`GuardDuty::*`, four providers with every category) with no `entityTypes`. They load, lower and validate with no errors
or warnings, and evaluate exactly as before the enum feature: nothing is
injected, `threatSeverity` stays `String`, scores stay `decimal`.

`providers.json` has an `implementation` per provider.
