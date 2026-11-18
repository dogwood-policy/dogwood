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
This file proves that typechecking of `.or` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_or_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (h₁ : typeOf (Expr.or x₁ x₂) c env = Except.ok (tx, c')) :
  ∃ tx₁ bty₁ c₁,
    typeOf x₁ c env = .ok (tx₁, c₁) ∧
    tx₁.typeOf = .bool bty₁ ∧
    if bty₁ = BoolType.tt
    then tx = tx₁ ∧ c' = ∅
    else ∃ bty tx₂ bty₂ c₂,
      tx = (.or tx₁ tx₂ (.bool bty)) ∧
      typeOf x₂ c env = .ok (tx₂, c₂) ∧
      tx₂.typeOf = .bool bty₂ ∧
      if bty₁ = BoolType.ff
      then bty = bty₂ ∧ c' = c₂
      else if bty₂ = BoolType.tt
      then bty = BoolType.tt ∧ c' = ∅
      else if bty₂ = BoolType.ff
      then bty = BoolType.anyBool ∧ c' = c₁
      else bty = BoolType.anyBool ∧ c' = c₁ ∩ c₂
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at *
  rename_i res₁
  simp [typeOfOr] at h₁
  split at h₁ <;> simp [ok, err] at h₁ <;>
  rename_i hr₁
  case h_1 c₁  =>
    exists res₁.fst, BoolType.tt, res₁.snd
    simp [←h₁, hr₁]
  case h_2 c₁ =>
    cases h₃ : typeOf x₂ c env <;> simp [h₃] at h₁
    rename_i res₂
    split at h₁ <;> simp at h₁
    rename_i bty₂ hr₂
    have ⟨ht, hc⟩ := h₁
    subst ht hc
    exists res₁.fst, BoolType.ff, res₁.snd
    simp only [hr₁, hr₂, true_and]
    exists bty₂, res₂.fst
    simp only [true_and]
    exists bty₂, res₂.snd
  case h_3 bty₁ hneq₁ hneq₂ =>
    cases bty₁ <;> simp at hneq₁ hneq₂
    exists res₁.fst, BoolType.anyBool, res₁.snd
    simp [hr₁]
    cases h₃ : typeOf x₂ c env <;> simp [h₃] at *
    rename_i res₂
    split at h₁ <;> simp at h₁ <;>
    rename_i hr₂ <;>
    have ⟨ht, hc⟩ := h₁ <;> subst ht hc <;> simp
    case h_1 =>
      exists BoolType.tt, res₂.fst
      simp only [hr₂, true_and]
      exists BoolType.tt, res₂.snd
    case h_2 =>
      exists BoolType.anyBool, res₂.fst
      simp only [true_and]
      exists BoolType.ff, res₂.snd
    case h_3 bty₂ hneq₁ hneq₂ =>
      exists BoolType.anyBool, res₂.fst
      simp
      exists bty₂, res₂.snd
      simp [←hr₂]
      constructor
      · intro heq
        specialize hneq₁ heq
        contradiction
      · intro heq
        specialize hneq₂ heq
        contradiction

theorem type_of_or_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.or x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.or x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.or x₁ x₂) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨tx₁, bty₁, rc₁, h₄, h₅, h₆⟩ := type_of_or_inversion h₃
  specialize ih₁ h₁ h₂ h₄
  have ⟨ih₁₁, v₁, ih₁₂, ih₁₃⟩ := ih₁
  rw [h₅] at ih₁₃
  have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool ih₁₃ ; subst hb₁
  split at h₆
  case isTrue h₇ =>
    subst h₇
    have ⟨hty, hc⟩ := h₆ ; rw [hty] at * ; subst hc
    apply And.intro empty_guarded_capabilities_invariant
    have h₇ := instance_of_tt_is_true ih₁₃
    simp at h₇ ; subst h₇
    simp [EvaluatesTo] at ih₁₂
    rw [h₅]
    exists (.prim (.bool true))
    rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
    simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool] <;>
    exact true_is_instance_of_tt
  case isFalse =>
    have ⟨bty, tx₂, bty₂, rc₂, h₅', h₇, h₈, h₉⟩ := h₆
    subst ty
    specialize ih₂ h₁ h₂ h₇
    have ⟨ih₂₁, v₂, ih₂₂, ih₂₃⟩ := ih₂
    rw [h₈] at ih₂₃
    have ⟨b₂, hb₂⟩ := instance_of_bool_is_bool ih₂₃
    subst hb₂
    simp [EvaluatesTo]
    cases b₁ <;>
    rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
    rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;>
    simp [evaluate, Result.as, Coe.coe, Value.asBool, ih₁₂, ih₂₂, GuardedCapabilitiesInvariant, pure, Except.pure] <;>
    try { simp only [TypedExpr.typeOf]; apply type_is_inhabited_bool }
    case false.inr.inr.inr.inr.inr.inr =>
      cases b₂ <;>
      simp
      case false h₉ =>
        cases bty₁ <;> simp at h₉ h₈
        case anyBool =>
          cases bty₂ <;> simp at h₉ <;>
          replace ⟨h₉, _⟩ := h₉ <;> rw [h₉] <;>
          try exact bool_is_instance_of_anyBool false
          exact ih₂₃
        case ff =>
          rw [h₉.left]
          exact ih₂₃
        case tt =>
          contradiction
      case true h₉ =>
        cases bty₁ <;> cases bty₂ <;> simp at h₉ h₈ <;>
        have ⟨hty, hc⟩ := h₉ <;> simp [hty, hc] at *
        case ff.ff =>
          rcases ih₂₃ with ⟨_, _, ih₂₃⟩
          simp [InstanceOfBoolType] at ih₂₃
        case anyBool.ff =>
          rcases ih₂₃ with ⟨_, _, ih₂₃⟩
          simp [InstanceOfBoolType] at ih₂₃
        case anyBool.tt =>
          apply And.intro
          · apply empty_capabilities_invariant
          · exact true_is_instance_of_tt
        case anyBool.anyBool =>
          apply And.intro
          · simp [GuardedCapabilitiesInvariant, ih₂₂] at ih₂₁
            apply capability_intersection_invariant
            simp [ih₂₁]
          · apply bool_is_instance_of_anyBool
        all_goals {
          simp [GuardedCapabilitiesInvariant, ih₂₂] at ih₂₁
          simp [ih₂₁]
          first
            | apply true_is_instance_of_tt
            | apply bool_is_instance_of_anyBool
        }
    all_goals {
      simp [GuardedCapabilitiesInvariant] at ih₁₁ ih₂₁
      simp [ih₁₂] at ih₁₁ ; simp [ih₂₂] at ih₂₁
      rename_i h₁₀
      rcases ih₁₃ with ⟨_, _, ih₁₃⟩
      simp [InstanceOfBoolType] at ih₁₃
      cases bty₁ <;> simp at h₁₀ ih₁₃ h₈
      cases bty₂ <;> simp at h₉ <;>
      have ⟨ht, hc⟩ := h₉ <;> simp [ht, hc] at * <;>
      simp [TypedExpr.typeOf, true_is_instance_of_tt, bool_is_instance_of_anyBool] <;>
      try { apply empty_capabilities_invariant } <;>
      try { assumption }
      apply capability_intersection_invariant
      simp [ih₁₁]
    }

end Cedar.Thm
