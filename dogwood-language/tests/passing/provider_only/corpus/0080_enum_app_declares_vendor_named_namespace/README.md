# 0080_enum_app_declares_vendor_named_namespace

The action schema declares `namespace GuardDuty` (e.g. an MCP gateway named after the vendor), with no actions. Provider enums go into the first namespace that declares actions, so `GuardDuty::Severity` is exported as `Drupe::GuardDuty_Severity` and doesn't touch the action schema's `GuardDuty` namespace. `hello` (LOW) is allowed, `malware here` (HIGH) is denied.
