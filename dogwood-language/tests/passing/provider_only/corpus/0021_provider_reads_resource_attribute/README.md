# 0021 — provider reads a resource entity attribute

Symmetric to `0020_provider_reads_principal_attribute`, but the provider
argument is a **resource** entity attribute (`resource.tier`) rather than a
principal one — exercising the `resource` scope path of provider-argument
resolution.

`Access::ByTier(resource.tier).allowed == true` gates `Read`. The provider
returns `{ allowed: bool }`, true iff `tier == "prod"`. The `tier` attribute is
carried in the per-event `entities(...)` envelope, parsed into the decision's
entity store, and resolved from there before the provider runs.

Two timepoints on the same policy, differing only in the resource and its
supplied attribute:

- `@0` `gw_prod`, `tier: "prod"` -> provider returns `allowed: true` -> **Allow**.
- `@10` `gw_test`, `tier: "test"` -> provider returns `allowed: false` -> **Deny**.
