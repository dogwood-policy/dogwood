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
This file proves that typechecking of `.and` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_and_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (h₁ : typeOf (Expr.and x₁ x₂) c env = Except.ok (tx, c')) :
  ∃ tx₁ bty₁ c₁,
    typeOf x₁ c env = .ok (tx₁, c₁) ∧
    tx₁.typeOf = .bool bty₁ ∧
    if bty₁ = BoolType.ff
    then tx = tx₁ ∧ c' = ∅
    else ∃ bty tx₂ bty₂ c₂,
      tx = (.and tx₁ tx₂ (.bool bty)) ∧
      typeOf x₂ (c ∪ c₁) env = .ok (tx₂, c₂) ∧
      tx₂.typeOf = .bool bty₂ ∧
      if bty₂ = BoolType.ff
      then bty = BoolType.ff ∧ c' = ∅
      else bty = lubBool bty₁ bty₂ ∧ c' = c₁ ∪ c₂
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at *
  rename_i res₁
  simp only [typeOfAnd, List.empty_eq] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  case h_1 h₃ =>
    have ⟨ hl₁, hr₁ ⟩ := h₁
    subst hl₁ hr₁
    exists res₁.fst, BoolType.ff, res₁.snd
  case h_2 bty₁ h₃ h₄ =>
    exists res₁.fst, bty₁, res₁.snd
    simp only [h₄, true_and]
    split ; contradiction
    cases h₄ : typeOf x₂ (c ∪ res₁.snd) env <;> simp [h₄] at *
    rename_i res₂
    split at h₁ <;> simp at h₁ <;>
    have ⟨hty, hc⟩ := h₁ <;> subst hty hc
    case h_1 hty₂ =>
      exists .ff, res₂.fst
      apply And.intro (by simp)
      exists .ff, res₂.snd
    case h_2 hty₂ =>
      exists bty₁, res₂.fst
      apply And.intro (by simp)
      exists BoolType.tt, res₂.snd
      cases bty₁
      case ff => contradiction
      all_goals
        simp [hty₂, lubBool]
    case h_3 bty₂ h₄ h₅ hty₂ =>
      exists .anyBool, res₂.fst
      apply And.intro (by simp)
      exists BoolType.anyBool, res₂.snd
      have _ : bty₂ = .anyBool := by
        cases bty₂ <;> simp at h₄ h₅ ⊢
      subst bty₂
      cases bty₁ <;> simp [hty₂, lubBool]

theorem type_of_and_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.and x₁ x₂) c₁ env = Except.ok (tx, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.and x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.and x₁ x₂) request entities v ∧ InstanceOfType env v tx.typeOf
:= by
  have ⟨tx₁, bty₁, rc₁, h₄, h₅, h₆⟩ := type_of_and_inversion h₃
  specialize ih₁ h₁ h₂ h₄
  have ⟨ih₁₁, v₁, ih₁₂, ih₁₃⟩ := ih₁
  rw [h₅] at ih₁₃
  have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool ih₁₃
  subst hb₁
  split at h₆
  case isTrue h₇ =>
    subst h₇
    have ⟨hty, hc⟩ := h₆
    rw [hty, hc, h₅]
    apply And.intro empty_guarded_capabilities_invariant
    have h₇ := instance_of_ff_is_false ih₁₃
    simp at h₇ ; subst h₇
    simp [EvaluatesTo] at ih₁₂
    rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
    simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool] <;>
    try exact type_is_inhabited_bool
    exact false_is_instance_of_ff
  case isFalse h₇ =>
    replace ⟨bty, tx₂, bty₂, rc₂, htx, htx₂, hty₂, h₆⟩ := h₆
    split at h₆ <;> have ⟨hbty, hc⟩ := h₆ <;> subst bty c₂ tx
    case isTrue hbty₂ =>
      subst bty₂
      apply And.intro empty_guarded_capabilities_invariant
      exists false ; simp [TypedExpr.typeOf, false_is_instance_of_ff]
      cases b₁
      case false =>
        rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool]
      case true =>
        rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool]
        simp [GuardedCapabilitiesInvariant] at ih₁₁
        specialize ih₁₁ ih₁₂
        have h₇ := capability_union_invariant h₁ ih₁₁
        specialize ih₂ h₇ h₂ htx₂
        have ⟨_, v₂, ih₂₂, ih₂₃⟩ := ih₂
        simp [EvaluatesTo] at ih₂₂
        rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;>
        simp [ih₂₂]
        rw [hty₂] at ih₂₃
        have h₈ := instance_of_ff_is_false ih₂₃
        subst h₈
        simp only [Except.map_ok, reduceCtorEq, or_true]
    case isFalse hbty₂ =>
      cases b₁
      case false =>
        rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool, GuardedCapabilitiesInvariant, TypedExpr.typeOf] <;>
        try exact type_is_inhabited_bool
        apply instance_of_lubBool
        simp [ih₁₃]
      case true =>
        rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool, GuardedCapabilitiesInvariant] <;>
        try exact type_is_inhabited_bool
        simp [GuardedCapabilitiesInvariant] at ih₁₁
        specialize ih₁₁ ih₁₂
        have h₇ := capability_union_invariant h₁ ih₁₁
        specialize ih₂ h₇ h₂ htx₂
        have ⟨ih₂₁, v₂, ih₂₂, ih₂₃⟩ := ih₂
        simp [EvaluatesTo] at ih₂₂
        rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;>
        simp [ih₂₂] <;>
        try exact type_is_inhabited_bool
        rw [hty₂] at ih₂₃
        have ⟨b₂, hb₂⟩ := instance_of_bool_is_bool ih₂₃
        subst hb₂
        cases b₂ <;> simp [TypedExpr.typeOf]
        case false =>
          apply instance_of_lubBool ; simp [ih₂₃]
        case true =>
          apply And.intro
          · simp [GuardedCapabilitiesInvariant] at ih₂₁
            specialize ih₂₁ ih₂₂
            exact capability_union_invariant ih₁₁ ih₂₁
          · apply instance_of_lubBool ; simp [ih₁₃]

end Cedar.Thm
