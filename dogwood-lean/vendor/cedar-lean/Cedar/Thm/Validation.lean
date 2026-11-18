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
import Cedar.Thm.Validation.Levels
import Cedar.Thm.Validation.Slice
import Cedar.Thm.Validation.Validator
import Cedar.Thm.Validation.RequestEntityValidation
import Cedar.Thm.Validation.EnvironmentValidation
import Cedar.Thm.Validation.Levels
import Cedar.Thm.Validation.SubstituteAction
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Authorization

/-!
This file contains the top-level correctness properties for the Cedar validator.
We show that if validation succeeds for a set of policies, then for any request
consistent with the schema, evaluating a policy in this set either produces a
boolean value, or throws one of the errors in the set of valid errors.
--/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
If a set of policies is well-typed (valid) with respect to the schema according to the validator,
and the input request and entities are consistent with the schema, then evaluating a policy in this set
either produces a boolean value, or throws an error of type `entityDoesNotExist`, `extensionError`, or
`arithBoundsError`. These errors cannot be protected against at validation time, as they depend on runtime
information.
-/

theorem validation_is_sound (policies : Policies) (schema : Schema) (request : Request) (entities : Entities) :
  schema.validateWellFormed = .ok () →
  validate policies schema = .ok () →
  validateRequest schema request = .ok () →
  validateEntities schema entities = .ok () →
  AllEvaluateToBool policies request entities
:= by
  intro hwf h₀ h₁ h₂
  have h₁ := request_and_entities_validate_implies_instance_of_wf_schema schema request entities hwf h₁ h₂
  unfold validate at h₀
  simp only [AllEvaluateToBool]
  cases h₃ : policies with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons h' t' =>
    intro policy pin
    simp only [EvaluatesToBool]
    apply typecheck_policy_with_environments_is_sound policy schema request entities h₁
    subst h₃
    simp only [List.forM_eq_forM, List.forM_cons] at h₀
    simp_do_let (typecheckPolicyWithEnvironments typecheckPolicy h' schema) as h₄ at h₀
    case ok _ =>
      rw [List.mem_cons] at pin
      cases pin with
      | inl h₅ =>
        subst h₅
        exact h₄
      | inr h₅ =>
        apply List.forM_ok_implies_all_ok t' (typecheckPolicyWithEnvironments _ · schema)
        repeat assumption

/--
If a set of policies is well-typed and validates at a level `n`, then any
authorization request made using a slice of entities obtained by slicing at
level `n` will return the same response as authorizing using the original
entities.
-/
theorem validate_with_level_is_sound {ps : Policies} {schema : Schema} {n : Nat} {request : Request} {entities : Entities}
  (hwf : schema.validateWellFormed = .ok ())
  (hr : validateRequest schema request = .ok ())
  (he : validateEntities schema entities = .ok ())
  (htl : validateWithLevel ps schema n = .ok ()) :
  isAuthorized request entities ps = isAuthorized request (entities.sliceAtLevel request n) ps
:= validate_with_level_is_sound_wf (request_and_entities_validate_implies_instance_of_wf_schema _ _ _ hwf hr he) htl

/--
End-to-end statement of issue #642 for a validated policy set, phrased over the
*executable* closure check `Entities.closedAtLevel`: if `ps` validates at level
`n` and the store passes `entities.closedAtLevel request n`, then no policy
evaluates to `entityDoesNotExist`.  These are exactly the evaluations
`isAuthorized` performs, so this is the per-policy guarantee `isAuthorized`
inherits: the authorizer surfaces evaluation results only through the
kind-agnostic `errorPolicies` / `satisfiedPolicies` and never raises
`entityDoesNotExist` of its own.  Mirrors `validate_with_level_is_sound`, with the
runtime closure obligation discharged by running `Entities.closedAtLevel`
(`closedAtLevel_iff` bridges it to the `EntitiesClosedAtLevel` predicate).
-/
theorem validate_with_level_no_dne {ps : Policies} {schema : Schema} {n : Nat} {request : Request} {entities : Entities}
  (hwf : schema.validateWellFormed = .ok ())
  (hr : validateRequest schema request = .ok ())
  (he : validateEntities schema entities = .ok ())
  (hcl : entities.closedAtLevel request n)
  (htl : validateWithLevel ps schema n = .ok ()) :
  ∀ p ∈ ps, evaluate p.toExpr request entities ≠ .error .entityDoesNotExist
:= validate_with_level_no_dne_wf
    (request_and_entities_validate_implies_instance_of_wf_schema _ _ _ hwf hr he)
    (closedAtLevel_iff.mp hcl) htl

/--
Bridge from `Response.erroringPolicies` membership back to the evaluator: if a
policy id appears in the erroring set produced by `isAuthorized`, then some
policy in `ps` with that id genuinely errored on evaluation.  Because policy ids
need not be unique, this recovers *a* policy with the id, not necessarily a
specific one.
-/
theorem error_of_mem_erroringPolicies {ps : Policies} {request : Request} {entities : Entities} {pid : PolicyID}
  (h : pid ∈ (isAuthorized request entities ps).erroringPolicies) :
  ∃ p ∈ ps, p.id = pid ∧ ∃ e, evaluate p.toExpr request entities = .error e
:= by
  unfold isAuthorized errorPolicies errored at h
  simp only [apply_ite, ite_self, Set.mem_make, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq] at h
  obtain ⟨p, hp, herr, hid⟩ := h
  refine ⟨p, hp, hid, ?_⟩
  cases heq : evaluate p.toExpr request entities with
  | ok v => simp [hasError, heq] at herr
  | error e => exact ⟨e, rfl⟩

/--
`Response`-level form of `validate_with_level_no_dne` (issue #642): for a policy
set that validates at level `n` over a store closed at that level, no policy in
the authorizer's `erroringPolicies` errored with `entityDoesNotExist`.  The
`erroringPolicies` membership premise is not needed for soundness — *no* policy
evaluates to `entityDoesNotExist` at all (`validate_with_level_no_dne`) — but it
phrases the guarantee at the `isAuthorized` `Response` level.
-/
theorem validate_with_level_no_dne_response {ps : Policies} {schema : Schema} {n : Nat} {request : Request} {entities : Entities}
  (hwf : schema.validateWellFormed = .ok ())
  (hr : validateRequest schema request = .ok ())
  (he : validateEntities schema entities = .ok ())
  (hcl : entities.closedAtLevel request n)
  (htl : validateWithLevel ps schema n = .ok ()) :
  ∀ p ∈ ps, p.id ∈ (isAuthorized request entities ps).erroringPolicies →
    evaluate p.toExpr request entities ≠ .error .entityDoesNotExist
:= by
  intro p hp _
  exact validate_with_level_no_dne hwf hr he hcl htl p hp

/--
`Response`-level form of `validation_is_sound`: for a validated policy set with
unique policy ids, every policy in the authorizer's `erroringPolicies` errored
with one of the three errors validation cannot rule out (`entityDoesNotExist`,
`extensionError`, `arithBoundsError`).  Uniqueness of ids (`PolicyIdsUnique`, as
in `determining_erroring_disjoint_when_unique_ids`) is required: an id in
`erroringPolicies` only witnesses that *some* policy with that id errored, so
without uniqueness it need not be the policy `p` quantified over.
-/
theorem validation_is_sound_response (policies : Policies) (schema : Schema) (request : Request) (entities : Entities)
  (huniq : PolicyIdsUnique policies)
  (hwf : schema.validateWellFormed = .ok ())
  (hv : validate policies schema = .ok ())
  (hr : validateRequest schema request = .ok ())
  (he : validateEntities schema entities = .ok ()) :
  ∀ p ∈ policies, p.id ∈ (isAuthorized request entities policies).erroringPolicies →
    evaluate p.toExpr request entities = .error .entityDoesNotExist ∨
    evaluate p.toExpr request entities = .error .extensionError ∨
    evaluate p.toExpr request entities = .error .arithBoundsError
:= by
  intro p hp hmem
  obtain ⟨p', hp', hid, e, herr⟩ := error_of_mem_erroringPolicies hmem
  have hpeq : p' = p := huniq p' hp' p hp hid
  rw [hpeq] at herr
  have hsound : AllEvaluateToBool policies request entities :=
    validation_is_sound policies schema request entities hwf hv hr he
  have hev : EvaluatesToBool p.toExpr request entities := hsound p hp
  obtain ⟨b, hev⟩ := hev
  unfold EvaluatesTo at hev
  rcases hev with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · rw [herr] at h; exact absurd h (by simp)

end Cedar.Thm
