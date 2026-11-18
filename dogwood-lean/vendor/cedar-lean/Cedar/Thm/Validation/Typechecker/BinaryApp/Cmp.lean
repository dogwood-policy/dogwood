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

import Cedar.Thm.Data.LT
import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.binaryApp .less` and `binaryApp .lessEq` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_int_cmp_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : op₂ = .less ∨ op₂ = .lessEq)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty.typeOf = .bool .anyBool ∧
  (((∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.int, c₁)) ∧
   (∃ c₂, (typeOf x₂ c env).typeOf = Except.ok (.int, c₂))) ∨
  ((∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.ext .datetime, c₁)) ∧
   (∃ c₂, (typeOf x₂ c env).typeOf = Except.ok (.ext .datetime, c₂))) ∨
  ((∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.ext .duration, c₁)) ∧
   (∃ c₂, (typeOf x₂ c env).typeOf = Except.ok (.ext .duration, c₂))))
:= by
  simp [typeOf] at *
  cases h₃ : typeOf x₁ c env <;> simp [h₃] at h₂
  cases h₄ : typeOf x₂ c env <;> simp [h₄] at h₂
  rcases h₁ with h₁ | h₁
  all_goals (
    subst h₁
    simp only [typeOfBinaryApp, ok, List.empty_eq, err] at h₂
    split at h₂ <;> try {contradiction}
    all_goals (
      simp only [Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₂
      simp only [← h₂, TypedExpr.typeOf, true_and]
      rename_i tc₁ tc₂ _ _ _ _ h₅ h₆
    )
  )
  -- cases with `CedarType.int`
  case' h_6 | h_9 =>
    apply Or.inl
  -- cases with `CedarType.ext ExtType.datetime`
  case' h_7 | h_10 =>
    apply Or.inr
    apply Or.inl
  -- cases with `CedarType.ext ExtType.duration`
  case' h_8 | h_11 =>
    apply Or.inr
    apply Or.inr
  all_goals (
    constructor
    · exists tc₁.snd ; simp [←h₅, ResultType.typeOf, Except.map]
    · exists tc₂.snd ; simp [←h₆, ResultType.typeOf, Except.map]
  )

theorem type_of_int_cmp_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : op₂ = .less ∨ op₂ = .lessEq)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨hc, hty, ht⟩ := type_of_int_cmp_inversion h₀ h₃
  rcases ht with ⟨ht₁, ht₂⟩ | ⟨ht₁, ht₂⟩ | ⟨ht₁, ht₂⟩
  all_goals (
    subst hc ; rw [hty]
    apply And.intro empty_guarded_capabilities_invariant
    replace ⟨c₁', ht₁⟩ := ht₁
    replace ⟨c₂', ht₂⟩ := ht₂
    split_type_of ht₁ ; rename_i ht₁ htl₁ htr₁
    split_type_of ht₂ ; rename_i ht₂ htl₂ htr₂
    specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
    specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
    simp only [List.empty_eq, EvaluatesTo, evaluate] at *
    cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
    cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
    try { simp only [ih₁, ih₂, true_and] ; exact type_is_inhabited_bool }
    replace ⟨ihl₁, ih₃⟩ := ih₁
    replace ⟨ihl₂, ih₄⟩ := ih₂
    rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
    rw [htl₁] at ih₃
    rw [htl₂] at ih₄
  )
  have ⟨i₁, ih₁⟩ := instance_of_int_is_int ih₃
  have ⟨i₂, ih₂⟩ := instance_of_int_is_int ih₄
  rotate_left
  have ⟨i₁, ih₁⟩ := instance_of_datetime_type_is_datetime ih₃
  have ⟨i₂, ih₂⟩ := instance_of_datetime_type_is_datetime ih₄
  rotate_left
  have ⟨i₁, ih₁⟩ := instance_of_duration_type_is_duration ih₃
  have ⟨i₂, ih₂⟩ := instance_of_duration_type_is_duration ih₄
  rotate_left
  all_goals (
    subst ih₁ ih₂
    rcases h₀ with h₀ | h₀
  )
  all_goals {
    subst h₀
    simp only [apply₂, reduceCtorEq, Except.ok.injEq, false_or, exists_eq_left']
    apply bool_is_instance_of_anyBool
  }

end Cedar.Thm
