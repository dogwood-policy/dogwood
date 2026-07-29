# permit_read_anyone

The simplest useful rule: permit the `Read` action for any principal on any
resource, with no `when` clause (Step 2 of the getting-started tour). A
pure-Cedar rule with no history dependence, checked against the tour's own
minimal `Login`/`Read` Drupe schema (`schema.cedarschema`).

The trace shows both outcomes:

- `@0` — alice's `Login` (a history-only occurrence here; the policy gates
  `Read`, not `Login`, so no `permit` matches → **deny**).
- `@10` — alice's `Read` → **allow** (rule 0 matches; bare `principal`/`resource`
  mean "any").
- `@20` — bob's `Read` → **allow** ("anyone" really means any principal).

Referenced by `guide/01-getting-started.md`.
