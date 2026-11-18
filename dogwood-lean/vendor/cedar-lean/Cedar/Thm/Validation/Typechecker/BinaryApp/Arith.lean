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
This file proves that typechecking of `.binaryApp .add`, `binaryApp .sub`, and `binaryApp .mul` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_int_arith_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : op₂ = .add ∨ op₂ = .sub ∨ op₂ = .mul)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty.typeOf = .int ∧
  (∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.int, c₁)) ∧
  (∃ c₂, (typeOf x₂ c env).typeOf = Except.ok (.int, c₂))
:= by
  simp [typeOf] at *
  cases h₃ : typeOf x₁ c env <;> simp [h₃] at h₂
  cases h₄ : typeOf x₂ c env <;> simp [h₄] at h₂
  rcases h₁ with h₁ | h₁ | h₁
  all_goals {
    subst h₁
    simp [typeOfBinaryApp, err, ok] at h₂
    split at h₂ <;> try contradiction
    simp at h₂ ; simp [h₂]
    rename_i tc₁ tc₂ _ _ _ _ h₅ h₆
    replace ⟨h₂, _⟩ := h₂
    rw [←h₂]
    simp only [TypedExpr.typeOf, true_and]
    constructor
    · exists tc₁.snd ; simp only [ResultType.typeOf, Except.map, ← h₅]
    · exists tc₂.snd ; simp only [ResultType.typeOf, Except.map, ← h₆]
  }

theorem type_of_int_arith_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : op₂ = .add ∨ op₂ = .sub ∨ op₂ = .mul)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨hc, hty, ht₁, ht₂⟩ := type_of_int_arith_inversion h₀ h₃
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
  try { simp [ih₁, ih₂] ; exact type_is_inhabited_int }
  replace ⟨ihl₁, ih₃⟩ := ih₁
  replace ⟨ihl₂, ih₄⟩ := ih₂
  rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
  rw [htl₁] at ih₃
  have ⟨i₁, ih₁⟩ := instance_of_int_is_int ih₃
  rw [htl₂] at ih₄
  have ⟨i₂, ih₂⟩ := instance_of_int_is_int ih₄
  subst ih₁ ih₂
  rcases h₀ with h₀ | h₀ | h₀ <;> subst h₀ <;> simp [apply₂, intOrErr]
  case inl =>
    cases h₄ : Int64.add? i₁ i₂ <;> simp
    case none => exact type_is_inhabited_int
    case some => simp [InstanceOfType.instance_of_int]
  case inr.inl =>
    cases h₄ : Int64.sub? i₁ i₂ <;> simp
    case none => exact type_is_inhabited_int
    case some => simp [InstanceOfType.instance_of_int]
  case inr.inr =>
    cases h₄ : Int64.mul? i₁ i₂ <;> simp
    case none => exact type_is_inhabited_int
    case some => simp [InstanceOfType.instance_of_int]

end Cedar.Thm
