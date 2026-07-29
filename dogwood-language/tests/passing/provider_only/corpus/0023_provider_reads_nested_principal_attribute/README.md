# 0023 — forbid gated by a nested-path provider argument

A `forbid` whose guardrails clause invokes a provider with a **nested**
principal entity attribute (`principal.address.zone`, two segments deep). An
unconditional `permit` allows `Read`; the `forbid` blocks it when the provider
reports the principal's zone is restricted.

The forbid shape makes this a security-relevant case. If a nested provider
argument failed to resolve — the pre-fix behaviour, where a provider-argument
path deeper than one segment silently resolved to `Null` — the provider would
not see `"restricted"`, `blocked` would be false, the forbid would not fire,
and the request would be **allowed**: a fail-open hole. With nested paths
resolving (matching how pure Cedar descends the same path), the forbid fires
and the request is denied.

Two timepoints:

- `@0` alice, `address.zone: "restricted"` -> forbid fires -> **Deny**.
- `@10` bob, `address.zone: "open"` -> forbid does not fire, permit stands -> **Allow**.

The attribute is a nested record supplied per event in the `entities(...)`
envelope. Contrast `0020` / `0021`, which use single-segment attribute paths.
