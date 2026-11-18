import Cedar.Validation
import Cedar.Thm.Data.List

/-!
# Cedar validation of a rule whose condition is one leaf

Cedar's validator (`Cedar.Validation.validate`) is defined by well-founded recursion, so a proof
cannot compute it by reduction. This module proves, once, that the lowered form of a rule
`permit (principal, action == A, resource) when { <leaf> }` validates: its condition is a
`Bool` attribute of the context, which the augmented schema declares on every action
(`validate_leafPermit`). The worked examples are of that form.
-/

namespace Dogwood.Thm

open Cedar.Spec Cedar.Validation Cedar.Data

/-- `permit (principal, action == a, resource) when { context.<attr> }`. -/
def leafPermit (id : PolicyID) (a : EntityUID) (attr : Attr) : Policy :=
  { id, effect := .permit, principalScope := .principalScope .any,
    actionScope := .actionScope (.eq a), resourceScope := .resourceScope .any,
    condition := [⟨.when, .getAttr (.var .context) attr⟩] }

/-- The rule typechecks in an environment whose context declares the attribute, required and
`Bool`: as `Bool` where its action is `a`, and as `false` elsewhere. -/
theorem typecheck_leafPermit (id : PolicyID) (a : EntityUID) (attr : Attr) (env : TypeEnv)
    (hact : env.acts.contains env.reqty.action = true) (ha : env.acts.contains a = true)
    (hctx : env.reqty.context.find? attr = some (.required (.bool .anyBool))) :
    ∃ tx, typecheckPolicy (leafPermit id a attr) env = .ok tx ∧
      tx.typeOf = (if env.reqty.action = a then .bool .anyBool else .bool .ff) := by
  have hsub₁ : (CedarType.bool BoolType.anyBool ⊑ CedarType.bool BoolType.anyBool) = true := by
    decide +kernel
  have hsub₂ : (CedarType.bool BoolType.ff ⊑ CedarType.bool BoolType.anyBool) = true := by
    decide +kernel
  by_cases h : env.reqty.action = a <;>
  simp [h, hsub₁, hsub₂, typecheckPolicy, leafPermit, Policy.toExpr, PrincipalScope.toExpr,
    ActionScope.toExpr, ResourceScope.toExpr, Scope.toExpr, Conditions.toExpr, Condition.toExpr,
    Var.eqEntityUID, substituteAction, mapOnVars, typeOf, typeOfLit, typeOfVar, typeOfAnd,
    typeOfBinaryApp, typeOfEq, typeOfGetAttr, getAttrInRecord, hact, ha, hctx, ok,
    TypedExpr.typeOf]

theorem mapM_ok_of_forall {α β ε : Type} {f : α → Except ε β} {P : α → β → Prop} :
    ∀ (L : List α), (∀ x ∈ L, ∃ y, f x = .ok y ∧ P x y) →
      ∃ ys, L.mapM f = .ok ys ∧ List.Forall₂ P L ys
  | [], _ => ⟨[], rfl, .nil⟩
  | x :: L, h => by
    obtain ⟨y, hy, hP⟩ := h x (List.mem_cons_self ..)
    obtain ⟨ys, hys, hF⟩ := mapM_ok_of_forall L fun z hz => h z (List.mem_cons_of_mem _ hz)
    refine ⟨y :: ys, ?_, .cons hP hF⟩
    simp [List.mapM_cons, hy, hys]

/-- **The lowered single-leaf permit validates.** -/
theorem validate_leafPermit (A : Schema) (id : PolicyID) (a : EntityUID) (attr : Attr)
    (hA : A.acts.contains a = true)
    (henvs : ∀ env ∈ A.environments, env.acts.contains env.reqty.action = true ∧
      env.acts.contains a = true ∧
      env.reqty.context.find? attr = some (.required (.bool .anyBool)))
    (hsome : ∃ env ∈ A.environments, env.reqty.action = a) :
    validate [leafPermit id a attr] A = .ok () := by
  obtain ⟨txs, hmap, hF⟩ := mapM_ok_of_forall (f := typecheckPolicy (leafPermit id a attr))
    (P := fun env tx => tx.typeOf = (if env.reqty.action = a then .bool .anyBool else .bool .ff))
    A.environments fun env h =>
      typecheck_leafPermit id a attr env (henvs env h).1 (henvs env h).2.1 (henvs env h).2.2
  have hnf : allFalse txs = false := by
    obtain ⟨env, henv, hea⟩ := hsome
    obtain ⟨tx, htx, hP⟩ := List.forall₂_implies_all_left hF env henv
    simp only [allFalse, List.all_eq_false]
    refine ⟨tx, htx, ?_⟩
    rw [hP, if_pos hea]
    decide +kernel
  have hce : checkEntities A (leafPermit id a attr).toExpr = .ok () := by
    simp [checkEntities, leafPermit, Policy.toExpr, PrincipalScope.toExpr, ActionScope.toExpr,
      ResourceScope.toExpr, Scope.toExpr, Conditions.toExpr, Condition.toExpr, Var.eqEntityUID,
      hA]
  simp [validate, typecheckPolicyWithEnvironments, hce, hmap, hnf, Except.mapError]

end Dogwood.Thm
