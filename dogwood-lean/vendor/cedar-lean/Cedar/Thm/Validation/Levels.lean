/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/
import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Authorization.Authorizer
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Validator
import Cedar.Thm.Validation.RequestEntityValidation

import Cedar.Thm.Validation.Levels.Basic
import Cedar.Thm.Validation.Levels.CheckLevel
import Cedar.Thm.Validation.Levels.IfThenElse
import Cedar.Thm.Validation.Levels.GetAttr
import Cedar.Thm.Validation.Levels.HasAttr
import Cedar.Thm.Validation.Levels.ExtHasAttr
import Cedar.Thm.Validation.Levels.UnaryApp
import Cedar.Thm.Validation.Levels.BinaryApp
import Cedar.Thm.Validation.Levels.And
import Cedar.Thm.Validation.Levels.Or
import Cedar.Thm.Validation.Levels.Record
import Cedar.Thm.Validation.Levels.Set
import Cedar.Thm.Validation.Levels.Call
import Cedar.Thm.Validation.Levels.NoEntitiesError
import Cedar.Thm.Validation.Levels.ReachableChild
import Cedar.Thm.Validation.Levels.SliceHelpers

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_expr {e : Expr} {n : Nat} {tx : TypedExpr} {c c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf e c env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n) :
  evaluate e request entities = evaluate e request (entities.sliceAtLevel request n)
:= by
  cases e
  case lit => simp [evaluate]
  case var v => cases v <;> simp [evaluate]
  case ite c t e =>
    have ihc := @level_based_slicing_is_sound_expr c
    have iht := @level_based_slicing_is_sound_expr t
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_if hc hr ht hl ihc iht ihe
  case and e₁ e₂ =>
    have ih₁ := @level_based_slicing_is_sound_expr e₁
    have ih₂ := @level_based_slicing_is_sound_expr e₂
    exact level_based_slicing_is_sound_and hc hr ht hl ih₁ ih₂
  case or e₁ e₂ =>
    have ih₁ := @level_based_slicing_is_sound_expr e₁
    have ih₂ := @level_based_slicing_is_sound_expr e₂
    exact level_based_slicing_is_sound_or hc hr ht hl ih₁ ih₂
  case unaryApp op e =>
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_unary_app hc hr ht hl ihe
  case binaryApp op e₁ e₂ =>
    have ihe₁ := @level_based_slicing_is_sound_expr e₁
    have ihe₂ := @level_based_slicing_is_sound_expr e₂
    exact level_based_slicing_is_sound_binary_app hc hr ht hl ihe₁ ihe₂
  case getAttr e _ =>
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_get_attr hc hr ht hl ihe
  case hasAttr e _ =>
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_has_attr hc hr ht hl ihe
  case extHasAttr e _ _ =>
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_ext_has_attr hc hr ht hl ihe
  case set xs =>
    have ih : ∀ x ∈ xs, TypedAtLevelIsSound x := by
      intro x hx
      have _ : sizeOf x < sizeOf (Expr.set xs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        simp only [Expr.set.sizeOf_spec]
        omega
      exact @level_based_slicing_is_sound_expr x
    exact level_based_slicing_is_sound_set hc hr ht hl ih
  case call xfn xs =>
    have ih : ∀ x ∈ xs, TypedAtLevelIsSound x := by
      intro x hx
      have _ : sizeOf x < sizeOf (Expr.set xs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        simp only [Expr.set.sizeOf_spec]
        omega
      exact @level_based_slicing_is_sound_expr x
    exact level_based_slicing_is_sound_call hc hr ht hl ih
  case record rxs =>
    have ih : ∀ x ∈ rxs, TypedAtLevelIsSound x.snd := by
      intro x hx
      have _ : sizeOf x.snd < sizeOf (Expr.record rxs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        rw [Prod.mk.sizeOf_spec] at h₁
        simp only [Expr.record.sizeOf_spec]
        omega
      exact @level_based_slicing_is_sound_expr x.snd
    exact level_based_slicing_is_sound_record hc hr ht hl ih
termination_by e

theorem typecheck_policy_with_level_is_sound {p : Policy} {tx : TypedExpr} {n : Nat} {env : TypeEnv} {request : Request} {entities : Entities}
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (htl : typecheckPolicyWithLevel p n env = .ok tx) :
  evaluate p.toExpr request entities = evaluate p.toExpr request (entities.sliceAtLevel request n)
:= by
  simp only [typecheckPolicyWithLevel, typecheckPolicy] at htl
  split at htl <;> try contradiction
  rename_i tx' _ htx'
  cases htl₁ : tx'.typeOf ⊑ .bool .anyBool  <;> simp only [htl₁, Bool.false_eq_true, ↓reduceIte, Except.bind_err, Except.bind_ok, reduceCtorEq] at htl
  split at htl <;> simp only [reduceCtorEq, Except.ok.injEq] at htl
  subst htl
  rename_i htl'
  have subst_action_preserves_entities := (@substitute_action_preserves_evaluation · · entities)
  have subst_action_preserves_slice := (@substitute_action_preserves_evaluation · · (entities.sliceAtLevel request n))
  rw [←subst_action_preserves_slice, ←subst_action_preserves_entities, action_matches_env hr]
  rw [←level_spec] at htl'
  have hc := empty_capabilities_invariant request entities
  exact level_based_slicing_is_sound_expr hc hr htx' htl'

/--
The sliced variant of `typecheck_policy_with_level_no_dne` (issue #642): evaluating
a level-checked policy against the level-`n` *slice* of a closed store also never
produces `entityDoesNotExist`.  Follows trivially by transporting the full-store
result across the semantic-equivalence soundness theorem.
-/
theorem typecheck_policy_with_level_no_dne_on_slice {p : Policy} {tx : TypedExpr} {n : Nat} {env : TypeEnv} {request : Request} {entities : Entities}
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (htl : typecheckPolicyWithLevel p n env = .ok tx) :
  evaluate p.toExpr request (entities.sliceAtLevel request n) ≠ .error .entityDoesNotExist
:= by
  rw [← typecheck_policy_with_level_is_sound hr htl]
  exact typecheck_policy_with_level_no_dne hr hcl htl

theorem typecheck_policy_at_level_with_environments_is_sound {p : Policy} {schema : Schema} {n : Nat} {request : Request} {entities : Entities}
  (he : ∃ env ∈ schema.environments, InstanceOfWellFormedEnvironment request entities env)
  (htl : typecheckPolicyWithEnvironments (typecheckPolicyWithLevel · n) p schema = .ok ()) :
  evaluate p.toExpr request entities = evaluate p.toExpr request (entities.sliceAtLevel request n)
:= by
  replace htl : ∀ x ∈ schema.environments, ∃ tx, typecheckPolicyWithLevel p n x = .ok tx := by
    simp only [typecheckPolicyWithEnvironments, Except.mapError] at htl
    simp_do_let (checkEntities schema p.toExpr) as hes at htl
    simp_do_let (List.mapM (typecheckPolicyWithLevel p n) schema.environments) as htl₁ at htl
    replace htl₁ := List.forall₂_implies_all_left ∘ List.mapM_ok_iff_forall₂.mp $ htl₁
    intro env he
    specialize htl₁ env he
    simp only [htl₁.imp, and_imp, imp_self, implies_true]
  have ⟨env, ⟨he₁, hr⟩⟩ := he
  specialize htl env he₁
  replace ⟨_, htl⟩ := htl
  exact typecheck_policy_with_level_is_sound hr htl

theorem validate_with_level_is_sound_wf {ps : Policies} {schema : Schema} {n : Nat} {request : Request} {entities : Entities}
  (hwf : InstanceOfWellFormedSchema schema request entities)
  (htl : validateWithLevel ps schema n = .ok ()) :
  isAuthorized request entities ps = isAuthorized request (entities.sliceAtLevel request n) ps
:= by
  have hsound : ∀ p ∈ ps, evaluate p.toExpr request entities = evaluate p.toExpr request (entities.sliceAtLevel request n) := by
    replace htl := List.forM_ok_implies_all_ok _ _ htl
    intro p hp
    exact typecheck_policy_at_level_with_environments_is_sound hwf (htl p hp)
  exact is_authorized_congr_evaluate hsound

/--
The `_no_dne` analogue of `typecheck_policy_at_level_with_environments_is_sound`:
a policy that level-checks against every environment of the schema (and so, in
particular, the one the request inhabits), evaluated against a store closed at
that level, never produces `entityDoesNotExist`.
-/
theorem typecheck_policy_at_level_with_environments_no_dne {p : Policy} {schema : Schema} {n : Nat} {request : Request} {entities : Entities}
  (he : ∃ env ∈ schema.environments, InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (htl : typecheckPolicyWithEnvironments (typecheckPolicyWithLevel · n) p schema = .ok ()) :
  evaluate p.toExpr request entities ≠ .error .entityDoesNotExist
:= by
  replace htl : ∀ x ∈ schema.environments, ∃ tx, typecheckPolicyWithLevel p n x = .ok tx := by
    simp only [typecheckPolicyWithEnvironments, Except.mapError] at htl
    simp_do_let (checkEntities schema p.toExpr) as hes at htl
    simp_do_let (List.mapM (typecheckPolicyWithLevel p n) schema.environments) as htl₁ at htl
    replace htl₁ := List.forall₂_implies_all_left ∘ List.mapM_ok_iff_forall₂.mp $ htl₁
    intro env he
    specialize htl₁ env he
    simp only [htl₁.imp, and_imp, imp_self, implies_true]
  have ⟨env, ⟨he₁, hr⟩⟩ := he
  specialize htl env he₁
  replace ⟨_, htl⟩ := htl
  exact typecheck_policy_with_level_no_dne hr hcl htl

/--
Validator-level statement of issue #642: if every policy in `ps` validates at
level `n` and `entities` is closed at level `n` for the request, then no policy
evaluates to an `entityDoesNotExist` error.  This is exactly the family of
evaluations `isAuthorized` performs, so it is the closure guarantee `isAuthorized`
inherits (the authorizer surfaces evaluation results only through the
kind-agnostic `errorPolicies` / `satisfiedPolicies`, and never introduces a
`entityDoesNotExist` of its own).  Mirrors `validate_with_level_is_sound_wf`.
-/
theorem validate_with_level_no_dne_wf {ps : Policies} {schema : Schema} {n : Nat} {request : Request} {entities : Entities}
  (hwf : InstanceOfWellFormedSchema schema request entities)
  (hcl : EntitiesClosedAtLevel entities request n)
  (htl : validateWithLevel ps schema n = .ok ()) :
  ∀ p ∈ ps, evaluate p.toExpr request entities ≠ .error .entityDoesNotExist
:= by
  replace htl := List.forM_ok_implies_all_ok _ _ htl
  intro p hp
  exact typecheck_policy_at_level_with_environments_no_dne hwf hcl (htl p hp)
