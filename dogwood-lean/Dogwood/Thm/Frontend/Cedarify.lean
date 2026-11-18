import Dogwood.Thm.Frontend.Cedarify.Lowering
import Dogwood.Thm.Frontend.Cedarify.Hoisting
import Dogwood.Thm.Frontend.Cedarify.Rules
import Dogwood.Thm.Frontend.Cedarify.Names
import Dogwood.Thm.Frontend.Cedarify.Context
import Dogwood.Thm.Frontend.Cedarify.Targets
import Dogwood.Thm.Frontend.Cedarify.Rename
import Dogwood.Thm.Frontend.Cedarify.Examples

/-!
# Theorems about the frontend: cedarify (WP3)

What `Dogwood.Frontend.Cedarify.cedarifyFull` (and so `cedarify`) guarantees when it succeeds:

* **Lowering** (`Cedarify.Rules`). The crate's Cedar policies are the rules in the
  specification's form lowered with the crate's references for their leaves
  (`cedarifyFull_lowered`): the specification's lowering `PolicySet.lowered` of those rules, with
  the reference to the `j`-th leaf, `context.leafAttr j`, replaced by the crate's `j`-th
  (`cedarifyFull_lowered_rename`). Each reference is `context.<f>` or `context.providers.<f>` for
  a hoisted field `f` of the leaf's kind, whose leaf it is when the leaves have a form in the
  specification (`cedarifyWithSpec_leaves`). The renaming need not be injective: `e has a.b` and
  `e is T in x` read `e` twice. When the rules read the context only through attributes other
  than the specification's leaf attributes (the `readsContext` clause), the crate's rules are the
  specification's lowering with each `context.leafAttr j` replaced by the crate's `j`-th
  reference (`Cedarify.Rename`, `cedarifyFull_relabel`). `cedarify` is `cedarifyFull` without
  the specification's form (`cedarify_eq_ok`).
* **Names** (`Cedarify.Names`). The `n`-th leaf of rule `i` is named `<ruleKey d i>__temporal_<n>`
  or `<ruleKey d i>_p_<n>`, one numbering for both kinds; no two leaves share a rule and a number
  (`cedarify_tags`); the names are distinct, and so are the context attributes lowering adds
  (`cedarify_names_nodup`). They are fresh in an action schema when no context attribute there
  begins with the rules' key prefix or is `providers` (`cedarify_names_fresh`); lowering does not
  check it.
* **Reading the context** (`Cedarify.Context`). A rule in the specification's form satisfies
  `Expr.ReadsContext R` exactly when its source does (`cedarify_readsContext_iff`); lowering does
  not check it.
* **Target actions** (`Cedarify.Targets`). Each hoisted field carries its rule's scope, and its
  target actions are exactly the actions that scope matches, descendants included, less the
  declared ones that cannot receive a request (`cedarify_targets`, `mem_scopeTargetActions`,
  `mem_closure`), without duplicates.
* **Counterexamples** (`Cedarify.Examples`): sets cedarify lowers that violate the `readsContext`
  clause (with any names, and with the crate's names only) and the `namesFresh` clause for the
  crate's names.
-/
