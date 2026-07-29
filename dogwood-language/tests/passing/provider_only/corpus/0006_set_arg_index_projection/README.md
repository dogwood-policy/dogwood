# 0006 — Set argument + index projection (the reference flagship shape)

The widest single-atom shape the dialect supports, matching what the reference
guardrails could express:

```
Content::Filter(context.input.document, ["VIOLENCE", "HATE"])["VIOLENCE"].severityScore.lessThan(decimal("0.5"))
```

It exercises, in one atom:

- **A set argument** — `["VIOLENCE", "HATE"]` (declared `paramType: set`).
  It reaches the Rhai script as an array the script iterates over.
- **An index projection** — `["VIOLENCE"]` into the output record, then a
  **field access** — `.severityScore`. Cedar records have no positional
  indexing, so a string index key is exactly a field access; the two
  compose into a nested `GetAttr`.
- **A decimal extension-method comparison** — `.lessThan(decimal("0.5"))`
  (the output field is a Cedar `decimal`).

- **`filter.rhai`** — `Content::Filter(text, categories) -> { <CAT>: { severityScore } }`;
  returns a per-category record so the policy can index into it.
- **`providers.json`** — declares the set argument and the nested-record
  output type (`{ VIOLENCE: { severityScore: decimal }, HATE: {...} }`).

`"violent"` scores VIOLENCE 0.90 → **deny**; `"safe"` scores 0.10 →
**permit**; `"hateful"` scores VIOLENCE 0.10 (only HATE is high) →
**permit**.
