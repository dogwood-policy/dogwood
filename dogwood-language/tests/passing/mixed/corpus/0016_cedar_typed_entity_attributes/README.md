# 0016 — pure-Cedar reads of typed entity attributes

Exercises entity attributes of **every core Cedar type** — `Long`, `Bool`,
`decimal`, `Set<String>` — read by a plain Cedar `when { … }` clause. The point
is the `Value -> Cedar RestrictedExpression` conversion and Cedar schema
conformance for each type; every other entity-attribute test uses only
`String`.

The attribute values are supplied per event via the `.log` `entities(...)`
envelope. (This is a pure-Cedar case in the mixed corpus because the mixed
harness is the only one that authorizes non-provider `.log` traces.)

```
principal.level >= 3
&& principal.active == true
&& principal.score.greaterThan(decimal("0.5"))
&& principal.roles.contains("admin")
```

Five timepoints, each flipping exactly one conjunct so the verdict stream
isolates whether that type round-tripped correctly:

- `@0`  alice: `level 5, active true, score 0.7, roles [admin]` — all hold -> **Allow**.
- `@10` bob:   `level 1` -> `Long` conjunct false -> **Deny**.
- `@20` carol: `active false` -> `Bool` conjunct false -> **Deny**.
- `@30` dave:  `score 0.2` -> `decimal` conjunct false -> **Deny**.
- `@40` erin:  `roles [viewer]` -> `Set<String>` membership false -> **Deny**.

A broken conversion for a given type would flip its line's verdict.
