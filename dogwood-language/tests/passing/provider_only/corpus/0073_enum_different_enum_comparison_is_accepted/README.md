# 0073_enum_different_enum_comparison_is_accepted

KNOWN GAP (open question): comparing to a DIFFERENT enum validates in Cedar and is constant. Here `!=` is always true, so every request is permitted, including HIGH. Both enums are used by the called provider (`result: Score`, optional `category: Category`); comparing against an enum no called provider uses is rejected instead (case `2182_enum_reject_literal_of_unused_enum`).

This case pins current Cedar behaviour. If Dogwood adds a lint for cross-enum comparison, turn it into a reject case.
