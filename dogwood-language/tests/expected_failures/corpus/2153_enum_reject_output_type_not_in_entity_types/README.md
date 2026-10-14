# 2153_enum_reject_output_type_not_in_entity_types

An OUTPUT entity type must be declared by the providers file itself.

Must be rejected with:
- ``MyGuardrails::Nope` is not declared in `entityTypes``

The policy (`… has result`) validates before the feature exists, so only the new check can reject it.
