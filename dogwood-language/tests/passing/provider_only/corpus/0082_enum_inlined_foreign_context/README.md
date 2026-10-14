# 0082_enum_inlined_foreign_context

The action's context is a type from another namespace (`context: Shared::Ctx`), which Dogwood inlines into the action before adding the provider field. `Shared` declares no actions, so the enum is exported into `Drupe` (`Drupe::MyGuardrails_Score`), and the inlined field refers to it by its full name.
