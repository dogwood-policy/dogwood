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

import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.binaryApp .contains` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_contains_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .contains x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty.typeOf = .bool .anyBool ∧
  ∃ ty₁ ty₂,
    (ty₁ ⊔ ty₂).isSome ∧
    (∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.set ty₁, c₁)) ∧
    (∃ c₂, (typeOf x₂ c env).typeOf = Except.ok (ty₂, c₂))
:= by
  simp [typeOf] at *
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env <;> simp [h₃] at h₁
  simp [typeOfBinaryApp, err, ok] at h₁
  split at h₁ <;> try contradiction
  simp only [ifLubThenBool, ok, List.empty_eq, err] at h₁
  split at h₁ <;> simp only [Except.ok.injEq, Except.bind_ok, Except.bind_err, Prod.mk.injEq, reduceCtorEq] at h₁
  simp [←h₁, TypedExpr.typeOf]
  rename_i tc₁ tc₂ _ ty₁ ty₂ ty₃ _ h₄ _ _ h₅
  exists ty₃, tc₂.fst.typeOf
  rw [lub_comm] at h₅
  simp [h₅, ←h₄]
  constructor
  · exists tc₁.snd
  · exists tc₂.snd

theorem type_of_contains_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.binaryApp .contains x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .contains x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .contains x₁ x₂) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨hc, hty, ty₁, ty₂, _, ht₁, ht₂⟩ := type_of_contains_inversion h₃
  subst hc ; rw [hty]
  apply And.intro empty_guarded_capabilities_invariant
  replace ⟨c₁', ht₁⟩ := ht₁
  replace ⟨c₂', ht₂⟩ := ht₂
  split_type_of ht₁ ; rename_i ht₁ htl₁ htr₁
  split_type_of ht₂ ; rename_i ht₂ htl₂ htr₂
  specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
  specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
  simp [EvaluatesTo, evaluate] at *
  cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
  cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
  try { simp [ih₁, ih₂] ; apply type_is_inhabited_bool }
  replace ⟨ihl₁, ih₃⟩ := ih₁
  replace ⟨ihl₂, ih₄⟩ := ih₂
  rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
  rw [htl₁] at ih₃
  have ⟨s₁, ih₁, _⟩ := instance_of_set_type_is_set ih₃
  subst ih₁
  simp [apply₂]
  apply bool_is_instance_of_anyBool

end Cedar.Thm
