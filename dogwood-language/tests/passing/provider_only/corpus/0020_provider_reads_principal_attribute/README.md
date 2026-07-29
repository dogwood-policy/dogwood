# 0020 — provider reads a principal entity attribute

A provider whose argument is a **principal entity attribute** (`principal.dept`),
supplied per event via the `.log` `entities(...)` envelope.

`Access::ByDept(principal.dept).allowed == true` gates `Read`. The provider
returns `{ allowed: bool }`, true iff `dept == "eng"`.

The point of this case is the argument and how it is supplied. `principal.dept`
is a genuine entity attribute — not `.id`/`.type` (which project from the uid,
see `0015_principal_id_arg`) and not a context field. It is carried in the
per-event `entities(...)` envelope, parsed into the decision's entity store,
and resolved from there before the provider runs. This exercises the whole
entity-attribute path end to end: parse -> per-event store -> schema
conformance -> provider argument resolution -> decision.

Two timepoints on the same policy, differing only in the supplied attribute:

- `@0` alice, `dept: "eng"` -> provider returns `allowed: true` -> **Allow**.
- `@10` bob, `dept: "sales"` -> provider returns `allowed: false` -> **Deny**.

This confirms the parsed store reaches evaluation and that attribute values are
per-event (they differ between the two lines).
