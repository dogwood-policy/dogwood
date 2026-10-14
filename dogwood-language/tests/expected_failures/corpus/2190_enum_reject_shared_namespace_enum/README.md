# 2190_enum_reject_shared_namespace_enum

A single shared `Shared::Severity` for both vendors
is rejected: an enum must be in the namespace of a provider declared in the
same file, and no provider here is in `Shared`, so nothing owns it. Each vendor must declare its own enum (`0076_enum_guardrails_enums_in_both_vendor_namespaces`, `0077_enum_guardrails_same_enum_name_in_each_vendor`). Enums
shared across vendors are not supported.
