# call_cedar_macro_as_argument

A Cedar macro call passed as an **argument** to another macro call:
`semverGT(semver(2, 1, 1), semver(2, 1, 0))`. The inner `semver(...)` calls
expand into record literals first, then splice into the outer `semverGT(...)`
call, which expands into the nested `if`/comparison. The result is a
constant-true guard (2.1.1 > 2.1.0), so the permit fires for every
`Drupe::Action::"GetStockInfo"` request.

The two macros (`semver`, `semverGT`) are lifted verbatim from macros corpus
`0036_semver_rfc0061` (Cedar RFC-0061, translated to Dogwood) and live in
`macros.dw`, passed via `--macros`.

Validate (run from this directory):

```
dogwood validate policy.dw --policy-schema schema.cedarschema --macros macros.dw
```

Referenced by `guide/09-calling-macros.md`.
