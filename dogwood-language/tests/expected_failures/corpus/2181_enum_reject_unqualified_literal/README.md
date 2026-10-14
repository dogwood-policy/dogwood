# 2181_enum_reject_unqualified_literal

Policies must write the qualified type: `Score::"LOW"` names a root-namespace type that doesn't exist.

Must be rejected with:
- `unrecognized entity type `Score``

Correct before AND after the feature, so this case starts `required` (a regression guard).
