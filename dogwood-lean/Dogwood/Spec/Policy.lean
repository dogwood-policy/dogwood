import Dogwood.Spec.Expr

/-!
# Policies

A Dogwood rule is a Cedar static policy whose condition clauses may contain
leaves. Its scope constraints are Cedar's, unchanged; its `when` / `unless`
clauses are conjoined in source order exactly as Cedar conjoins a policy's
conditions (`Cedar.Spec.Conditions.toExpr`).

A rule's id is its Cedar policy id after lowering: by default `policy_<i>` for
the `i`-th rule, or `<distincter>_<i>` (guide chapter 8, §4.1); with opt-in
stable ids, the rule's `@id` or caller-supplied id, `<distincter>/<id>` under a
distincter (guide chapter 7, `IdSource`; `Dogwood.Frontend.Ids`). The
specification takes the id as given. Annotations carry no meaning here.
-/

namespace Dogwood.Spec

open Cedar.Spec (PolicyID Effect PrincipalScope ActionScope ResourceScope ConditionKind)

structure Condition where
  kind : ConditionKind
  body : Expr
deriving Repr, Inhabited

abbrev Conditions := List Condition

structure Policy where
  id : PolicyID
  effect : Effect
  principalScope : PrincipalScope
  actionScope : ActionScope
  resourceScope : ResourceScope
  condition : Conditions
deriving Repr, Inhabited

abbrev Policies := List Policy

def Condition.toExpr (c : Condition) : Expr :=
  match c.kind with
  | .when => c.body
  | .unless => .unaryApp .not c.body

/-- Conditions are evaluated top to bottom, and short-circuit. -/
def Conditions.toExpr (cs : Conditions) : Expr :=
  match cs.reverse with
  | [] => .lit (.bool true)
  | c :: cs => cs.foldl (fun expr c => .and c.toExpr expr) c.toExpr

/-- The policy as one expression: its scope constraints, then its
conditions. -/
def Policy.toExpr (p : Policy) : Expr :=
  .and
    (Expr.ofCedar p.principalScope.toExpr)
    (.and
      (Expr.ofCedar p.actionScope.toExpr)
      (.and
        (Expr.ofCedar p.resourceScope.toExpr)
        (Conditions.toExpr p.condition)))

/-- Every Cedar static policy is a Dogwood rule without leaves. -/
def Policy.ofCedar (p : Cedar.Spec.Policy) : Policy where
  id := p.id
  effect := p.effect
  principalScope := p.principalScope
  actionScope := p.actionScope
  resourceScope := p.resourceScope
  condition := p.condition.map fun c => ⟨c.kind, Expr.ofCedar c.body⟩

end Dogwood.Spec
