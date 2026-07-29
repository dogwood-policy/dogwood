# 0022 — multiple entities in one envelope, including empty attributes

Focuses on the `.log` `entities(...)` envelope *shape* rather than a new
resolution path. Each line's envelope carries **two** entities:

- the principal with attributes — `Drupe::OAuthUser::"…": { dept: "…" }`,
  read by the provider;
- the resource with **empty** attributes — `Drupe::Gateway::"gw1": {}`.

The empty-attrs form (`{}`) makes an entity *present* in the store without
supplying attributes. Here it is the resource — which a scope entity would
otherwise be auto-added bare — so this also exercises the build path where a
scope uid is caller-supplied (and therefore not synthesized bare).

`Access::ByDept(principal.dept).allowed == true` gates `Read`; the provider
returns `{ allowed: bool }`, true iff `dept == "eng"`.

- `@0` alice, `dept: "eng"` (+ `gw1: {}`) -> **Allow**.
- `@10` bob, `dept: "sales"` (+ `gw1: {}`) -> **Deny**.
