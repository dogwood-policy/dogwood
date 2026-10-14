# 2185_enum_reject_method_input_enum_mismatch

A method whose inputType is a different enum than the previous stage's output is rejected.

Must be rejected with:
- `expects an input of type `MyGuardrails::Category` but the preceding stage produces `MyGuardrails::Score``
