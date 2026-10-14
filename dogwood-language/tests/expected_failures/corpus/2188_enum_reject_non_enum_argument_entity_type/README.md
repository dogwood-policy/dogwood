# 2188_enum_reject_non_enum_argument_entity_type

An argument type must be an enum: a provider sees an entity only as its bare id.

Must be rejected with:
- `entityType `Drupe::Gateway` is not an enum entity type`

`Drupe::Gateway` is a standard (non-enum) app entity type.
