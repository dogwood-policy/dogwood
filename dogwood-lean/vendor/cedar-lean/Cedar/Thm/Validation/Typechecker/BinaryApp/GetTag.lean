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
This file proves that typechecking of `.binaryApp .getTag` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_getTag_inversion {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .getTag x₁ x₂) c₁ env = .ok (tx, c₂)) :
  c₂ = [] ∧
  ∃ ety ty tx₁ tx₂ c₁' c₂',
    typeOf x₁ c₁ env = .ok (tx₁, c₁') ∧
    tx₁.typeOf = .entity ety ∧
    typeOf x₂ c₁ env = .ok (tx₂, c₂') ∧
    tx₂.typeOf = .string ∧
    env.ets.tags? ety = some (some ty) ∧
    tx = .binaryApp .getTag tx₁ tx₂ ty ∧
    (x₁, .tag x₂) ∈ c₁
:= by
  simp only [typeOf] at h₁
  simp_do_let (typeOf x₁ c₁ env) as h₂ at h₁
  simp_do_let (typeOf x₂ c₁ env) as h₃ at h₁
  rename_i tyc₁ tyc₂
  cases tyc₁
  cases tyc₂
  rename_i tx₁ c₁' tx₂ c₂'
  simp only at h₁
  cases h₄ : tx₁.typeOf <;> simp [typeOfBinaryApp, err, reduceCtorEq, h₄] at h₁
  cases h₅ : tx₂.typeOf <;> simp [reduceCtorEq, h₅] at h₁
  rename_i ety
  simp only [typeOfGetTag, List.empty_eq] at h₁
  split at h₁ <;> simp only [ok, err, Except.bind_err, reduceCtorEq] at h₁
  split at h₁ <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Prod.mk.injEq, List.nil_eq, reduceCtorEq] at h₁
  rename_i ty _ _
  rename_i h₆ h₇
  replace ⟨h₁, h₁'⟩ := h₁
  subst h₁ h₁'
  simp only [true_and]
  exists ety, ty, tx₁, tx₂
  simp only [h₄, h₅, h₆, h₇]
  simp

theorem type_of_getTag_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.binaryApp .getTag x₁ x₂) c₁ env = Except.ok (tx, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .getTag x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .getTag x₁ x₂) request entities v ∧ InstanceOfType env v tx.typeOf
:= by
  have hok := h₃
  replace ⟨hc, ety, ty, tx₁, tx₂, c₁', c₂', h₃, h₄, h₅, h₆, ht, htx, hc₁⟩ := type_of_getTag_inversion h₃
  subst hc
  replace ⟨_, v₁, ih₁, hty₁⟩ := ih₁ h₁ h₂ h₃
  replace ⟨_, v₂, ih₂, hty₂⟩ := ih₂ h₁ h₂ h₅
  simp only [EvaluatesTo] at *
  simp only [GuardedCapabilitiesInvariant, evaluate]
  rcases ih₁ with ih₁ | ih₁ | ih₁ | ih₁ <;>
  simp only [ih₁, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_false, or_true, true_and, reduceCtorEq]
  any_goals (apply type_of_is_inhabited h₂.wf_env hok)
  rcases ih₂ with ih₂ | ih₂ | ih₂ | ih₂ <;>
  simp only [ih₂, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_false, or_true, true_and, reduceCtorEq]
  any_goals (apply type_of_is_inhabited h₂.wf_env hok)
  rw [h₄] at hty₁
  replace ⟨uid, hty₁, hv₁⟩ := instance_of_entity_type_is_entity hty₁
  rw [h₆] at hty₂
  replace ⟨s, hv₂⟩ := instance_of_string_is_string hty₂
  subst hv₁ hv₂ hty₁
  simp only [apply₂]
  simp only [getTag, Entities.tags]
  have hf₁ := Map.findOrErr_returns entities uid Error.entityDoesNotExist
  rcases hf₁ with ⟨d, hf₁⟩ | hf₁ <;>
  simp only [hf₁, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_self, or_false, true_and,
    type_of_is_inhabited h₂.wf_env hok, and_self, reduceCtorEq]
  rw [Map.findOrErr_ok_iff_find?_some] at hf₁
  cases h₂.instance_of_schema_entry hf₁ with
  | inl h =>
    replace ⟨entry, hf₂, _, _, _, h₂⟩  := h
    simp only [InstanceOfEntityTags] at h₂
    simp [EntitySchema.tags?, Option.map_eq_some_iff] at ht
    replace ⟨_, ht₁, ht₂⟩ := ht
    simp only [hf₂, Option.some.injEq] at ht₁
    subst ht₁
    simp only [EntitySchemaEntry.tags?] at h₂ ht₂
    split at ht₂
    simp only [ht₂] at h₂
    have hf₃ := Map.findOrErr_returns d.tags s Error.tagDoesNotExist
    rcases hf₃ with ⟨v, hf₃⟩ | hf₃ <;>
    simp only [hf₃, false_implies, Except.error.injEq, or_self, false_and, exists_const, and_false,
      Except.ok.injEq, false_or, exists_eq_left', reduceCtorEq]
    · simp only [htx, TypedExpr.typeOf, ← List.empty_eq, empty_capabilities_invariant request entities, implies_true, true_and]
      apply h₂
      exact Map.findOrErr_ok_implies_in_values hf₃
    · replace h₁ := h₁.right x₁ x₂ hc₁
      simp only [EvaluatesTo, evaluate, ih₁, ih₂, apply₂, hasTag, Except.bind_ok, Except.ok.injEq,
        Value.prim.injEq, Prim.bool.injEq, false_or, reduceCtorEq] at h₁
      simp only [Entities.tagsOrEmpty, hf₁, Map.contains_iff_some_find?] at h₁
      replace ⟨_, h₁⟩ := h₁
      simp only [Map.findOrErr_err_iff_find?_none, h₁, reduceCtorEq] at hf₃
    · cases ht₂
  | inr h =>
    replace ⟨h₃, _, ⟨_, hacts, _⟩⟩ := h
    simp only [EntitySchema.tags?, Option.map] at ht
    split at ht
    · apply False.elim
      apply wf_env_disjoint_ets_acts h₂.wf_env
      all_goals assumption
    · contradiction

end Cedar.Thm
