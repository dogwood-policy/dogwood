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
This file proves that typechecking of `.binaryApp .eq` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_eq_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .eq x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  match x₁, x₂ with
  | .lit p₁, .lit p₂ =>
    if p₁ = p₂ then ty.typeOf = (.bool .tt) else ty.typeOf = (.bool .ff)
  | _, _ =>
    ∃ ty₁ c₁ ty₂ c₂,
      typeOf x₁ c env = Except.ok (ty₁, c₁) ∧
      typeOf x₂ c env = Except.ok (ty₂, c₂) ∧
      match ty₁.typeOf ⊔ ty₂.typeOf with
      | .some _ => ty.typeOf = (.bool .anyBool)
      | .none   =>
        ty.typeOf = (.bool .ff) ∧
        ∃ ety₁ ety₂, ty₁.typeOf = .entity ety₁ ∧ ty₂.typeOf = .entity ety₂
:= by
  simp [typeOf] at h₁ ; rename_i h₁'
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env <;> simp [h₃] at h₁
  simp only [typeOfBinaryApp, typeOfEq, beq_iff_eq, ok, List.empty_eq, err] at h₁
  rename_i tc₁ tc₂
  split at h₁
  case h_1 p₁ p₂ =>
    split at h₁ <;> simp at h₁ <;> simp [←h₁] <;>
    rename_i h₄ <;> simp [h₄, TypedExpr.typeOf]
  case h_2 h₄ =>
    split at h₁
    case h_1 h₅ =>
      simp only [Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₁
      replace ⟨h₁, h₁''⟩ := h₁ ; subst ty c'
      simp only [List.empty_eq, Except.ok.injEq,
        exists_and_left, exists_and_right, true_and]
      split
      case h_1 p₁ p₂ _ =>
        specialize h₄ p₁ p₂ ; simp at h₄
      case h_2 =>
        exists tc₁.fst
        constructor
        · exists tc₁.snd
        · exists tc₂.fst
          constructor
          · exists tc₂.snd
          · rw [h₅]
            simp [TypedExpr.typeOf]
    case h_2 h₅ =>
      split at h₁ <;> simp only [Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq, reduceCtorEq] at h₁
      replace ⟨h₁, h₁''⟩ := h₁ ; subst ty c'
      simp only [List.empty_eq,
        Except.ok.injEq, exists_and_left, exists_and_right, true_and]
      split
      case h_1 p₁ p₂ _ =>
        specialize h₄ p₁ p₂ ; simp at h₄
      case h_2 ety₁ ety₂ _ true_is_instance_of_tt _ _ _ _ =>
        exists tc₁.fst
        constructor
        · exists tc₁.snd
        · exists tc₂.fst
          constructor
          · exists tc₂.snd
          · rw [h₅]; simp [TypedExpr.typeOf]
            constructor
            · exists ety₁
            · exists ety₂

theorem no_entity_type_lub_implies_not_eq {env : TypeEnv} {v₁ v₂ : Value} {ety₁ ety₂ : EntityType}
  (h₁ : InstanceOfType env v₁ (CedarType.entity ety₁))
  (h₂ : InstanceOfType env v₂ (CedarType.entity ety₂))
  (h₃ : (CedarType.entity ety₁ ⊔ CedarType.entity ety₂) = none) :
  ¬ v₁ = v₂
:= by
  by_contra h₄ ; subst h₄
  simp [lub?] at h₃
  apply h₃
  cases h₁ ; cases h₂
  rename_i h₄ h₅
  simp [InstanceOfEntityType] at h₄ h₅
  simp only [h₄.1, h₅.1] at h₃
  contradiction

theorem type_of_eq_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.binaryApp .eq x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .eq x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .eq x₁ x₂) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨hc, hty⟩ := type_of_eq_inversion h₃
  subst hc
  apply And.intro empty_guarded_capabilities_invariant
  split at hty
  case h_1 =>
    split at hty <;> rw [hty]
    case isTrue heq _ _ =>
      subst heq
      simp [EvaluatesTo, evaluate, apply₂]
      exact true_is_instance_of_tt
    case isFalse p₁ p₂ heq _ =>
      simp [EvaluatesTo, evaluate, apply₂]
      cases h₃ : Value.prim p₁ == Value.prim p₂ <;>
      simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Value.prim.injEq] at h₃
      case false => exact false_is_instance_of_ff
      case true  => contradiction
  case h_2 =>
    replace ⟨ty₁, c₁', ty₂, c₂', ht₁, ht₂, hty⟩ := hty
    specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
    specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
    simp [EvaluatesTo, evaluate] at *
    cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
    cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
    try { simp [ih₁, ih₂] ; apply type_of_is_inhabited h₂.wf_env h₃ }
    replace ⟨ihl₁, ih₃⟩ := ih₁
    replace ⟨ihl₂, ih₄⟩ := ih₂
    rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
    simp [apply₂]
    split at hty
    case h_1 =>
      rw [hty]
      apply bool_is_instance_of_anyBool
    case h_2 heq =>
      have ⟨hty₀, ⟨ety₁, hty₁⟩, ⟨ety₂, hty₂⟩⟩ := hty ; clear hty
      rw [hty₁] at ih₃ heq
      rw [hty₂] at ih₄ heq
      have h₆ := no_entity_type_lub_implies_not_eq ih₃ ih₄ heq
      cases h₇ : v₁ == v₂ <;>
      simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at h₇
      case false => rw [hty₀]; exact false_is_instance_of_ff
      case true  => contradiction

end Cedar.Thm
