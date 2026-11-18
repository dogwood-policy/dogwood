import Dogwood.Thm.Frontend.Macros.Order
import Dogwood.Thm.Frontend.Macros.Transport
import Dogwood.Thm.Frontend.Macros.Safety
import Dogwood.Thm.Frontend.Macros.Examples
import Dogwood.Thm.Frontend.Macros.Expand
import Dogwood.Thm.Frontend.Macros.Arrays

/-!
# Theorems about the frontend: macro-library merge, macro expansion, the temporal static checks and the array check (WP1)

About `Dogwood.Frontend.Macros`:

* **The static checks** (`Macros.Safety`). `checkLeaf_iff`: a temporal leaf that projects to the
  formula `φ` passes `checkLeaf` (the crate's `check_condition`, `check_leaf_closed`,
  `check_demands`) iff `φ` is closed, well formed (`WF`) and safe with each `&&` chain read left
  to right (`SafeLR`, `Macros.Order`). `checkLeaf_isSafe`: so it is safe (`Formula.IsSafe`).
* **Incompleteness** (`Macros.Examples`). The converse fails beyond the order of the conjuncts:
  `interleaved_rejected` is a safe leaf that the checks reject in all eight orders of its
  chains; `misordered_rejected` and `ordered_accepted` are the order case.
* **Expansion** (`Macros.Expand`). `expand_expanded`: the output of `expand` has no definition,
  no macro call, no `?p` and no macro syntax in a block, and every block passes `checkLeaf`.
  `expand_macroFree`: on a macro-free set, `expand` is the identity and succeeds exactly when
  every block passes `checkLeaf`.
* **The library merge** (`Macros.Expand`). `mergeLibrary_lookup`: after the merge, a name
  resolves to the policy's own definition when it has one, and to the library's otherwise.
* **Arrays** (`Macros.Arrays`). `rejectArrays_ok`: an accepted set holds no array constant in a
  temporal block. `accepted_safe`: every block of a set that expansion and the array check
  accept projects to a safe formula of the specification (given what the parser guarantees:
  no internal disjunction, rooted scope fields). `rejectArrays_arith`: an array constant inside
  an aggregate under arithmetic is rejected.
-/
