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
This file proves that typechecking of `.getAttr` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem getAttrInRecord_has_empty_capabilities {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {rty : RecordType} {ty ty₁ : CedarType} :
  getAttrInRecord ty rty x₁ a c₁ = Except.ok (ty₁, c₂) →
  c₂ = ∅
:= by
  intro h₁
  simp [getAttrInRecord] at h₁
  split at h₁ <;>
  (try split at h₁) <;>
  simp [ok, err] at h₁ <;>
  simp [h₁]

theorem type_of_getAttr_inversion {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (h₁ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (tx, c₂)) :
  c₂ = ∅ ∧
  ∃ tx₁ c₁',
    typeOf x₁ c₁ env = .ok (tx₁, c₁') ∧
    tx = .getAttr tx₁ a tx.typeOf ∧
      ((∃ ety, tx₁.typeOf = .entity ety) ∨
       (∃ rty, tx₁.typeOf = .record rty))
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfGetAttr, bind, Except.bind] at h₁
    split at h₁ <;> try contradiction
    · simp only [List.empty_eq, Except.ok.injEq, Prod.mk.injEq, exists_and_right, exists_and_left,
      exists_eq', and_true, exists_eq_left']
      split at h₁ <;> simp [ok] at h₁
      rename_i heq₁ _ _ heq₂
      simp [heq₁, ←h₁]
      simp [TypedExpr.typeOf]
      apply getAttrInRecord_has_empty_capabilities heq₂
    · simp only [List.empty_eq, Except.ok.injEq, Prod.mk.injEq, exists_and_right]
      split at h₁ <;> try simp [err] at h₁
      split at h₁ <;> simp [ok] at h₁
      rename_i heq₁ _ _ _ _ _ heq₃
      simp [heq₁, ←h₁]
      simp [TypedExpr.typeOf]
      apply getAttrInRecord_has_empty_capabilities heq₃

theorem type_of_getAttr_is_sound_for_records {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : TypeEnv} {rty : RecordType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, ∅))
  (h₃ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.record rty, c₁'))
  (h₄ : evaluate x₁ request entities = Except.ok v₁)
  (h₅ : InstanceOfType env v₁ (CedarType.record rty)) :
  ∃ v,
  (getAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   getAttr v₁ a entities = Except.error Error.extensionError ∨
   getAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   getAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType env v ty.typeOf
:= by
  have ⟨r, h₆⟩ := instance_of_record_type_is_record h₅
  subst h₆
  simp [getAttr, attrsOf, Map.findOrErr]
  split_type_of h₃ ; rename_i h₃ hl₃ hr₃
  simp only [typeOf, typeOfGetAttr, getAttrInRecord, List.empty_eq, bind, Except.bind] at h₂
  cases h₈ : Map.find? r a
  case none =>
    simp only [Except.error.injEq, reduceCtorEq, or_self, false_and, exists_const]
    split at h₂ <;> simp [ok, err] at h₂
    rename_i heq
    rw [h₃] at heq
    simp at heq
    subst heq
    simp only [hl₃] at h₂
    split at h₂ <;> simp at h₂
    rename_i h₆
    split at h₆ <;> try simp at h₆
    case h_1 _ _ h₉ =>
      subst h₆
      have ⟨_, h₁₀⟩ := required_attribute_is_present h₅ h₉
      simp [h₈] at h₁₀
    case h_2 =>
      split at h₆ <;> simp at h₆
      subst h₆
      rename_i h₁₀
      have ⟨_, h₁₁⟩ := capability_implies_record_attribute h₁ h₄ h₁₀
      simp [h₈] at h₁₁
  case some vₐ =>
    simp only [Except.ok.injEq, false_or, exists_eq_left', reduceCtorEq]
    split at h₂ <;> simp [ok, err] at h₂
    rename_i h₆
    rw [h₆] at h₃
    simp at h₃
    subst h₃
    simp only [hl₃] at h₂
    split at h₂ <;> simp at h₂
    rename_i h₃
    split at h₃ <;> try simp at h₃
    case h_1 _ _ h₉ =>
      subst h₃
      simp at h₂
      subst h₂
      apply instance_of_attribute_type h₅ h₉ (by simp [Qualified.getType, TypedExpr.typeOf]) h₈
    case h_2 _ _ h₉ =>
      split at h₃ <;> simp at h₃
      subst h₃
      simp at h₂
      subst h₂
      apply instance_of_attribute_type h₅ h₉ (by simp [Qualified.getType, TypedExpr.typeOf]) h₈

theorem type_of_getAttr_is_sound_for_entities {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : TypeEnv} {ety : EntityType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, ∅))
  (h₄ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.entity ety, c₁'))
  (h₅ : evaluate x₁ request entities = Except.ok v₁)
  (h₆ : InstanceOfType env v₁ (CedarType.entity ety)) :
  ∃ v,
  (getAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   getAttr v₁ a entities = Except.error Error.extensionError ∨
   getAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   getAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType env v ty.typeOf
:= by
  have ⟨uid, h₇, h₈⟩ := instance_of_entity_type_is_entity h₆
  subst h₈
  simp [getAttr, attrsOf, Entities.attrs, Map.findOrErr]
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  cases h₈ : Map.find? entities uid
  case none =>
    simp only [Except.bind_err, Except.error.injEq, or_self, or_false, true_and, reduceCtorEq]
    exact type_of_is_inhabited h₂.wf_env h₃
  case some d =>
    subst h₇
    simp only [Except.bind_ok]
    cases h₉ : Map.find? d.attrs a
    case none =>
      simp only [Except.error.injEq]
      simp only [typeOf, h₄, hl₄, typeOfGetAttr, getAttrInRecord, List.empty_eq, bind, Except.bind] at h₃
      split at h₃ <;> simp [ok, err] at h₃
      rename_i h₃₁
      split at h₃ <;> try simp at h₃
      rename_i h₃₂
      split at h₃₂ <;> try simp at h₃₂
      case h_1 _ _ _ _ _ h₁₁ =>
        subst h₃₂
        have h₁₂ := well_typed_entity_attributes h₂ h₈ h₃₁
        have ⟨aᵥ, h₁₃⟩ := required_attribute_is_present h₁₂ h₁₁
        simp [h₉] at h₁₃
      case h_2 =>
        split at h₃₂ <;> simp at h₃₂
        subst h₃₂ ; rename_i h₁₃
        have ⟨_, h₁₄⟩ := capability_implies_entity_attribute h₁ h₅ h₈ h₁₃
        simp [h₉] at h₁₄
    case some vₐ =>
      simp only [Except.ok.injEq, false_or, exists_eq_left', reduceCtorEq]
      simp [typeOf, h₄, hl₄, typeOfGetAttr, getAttrInRecord, bind, Except.bind] at h₃
      split at h₃ <;> simp [ok, err] at h₃
      rename_i h₃₁
      split at h₃ <;> try simp at h₃
      rename_i h₃₂
      split at h₃₂ <;> try simp at h₃₂
      case h_1 _ _ h₁₀ _ _ h₁₁ =>
        subst h₃₂
        cases h₃ ; subst ty
        apply instance_of_attribute_type _ h₁₁ (by simp [Qualified.getType, TypedExpr.typeOf]) h₉
        apply well_typed_entity_attributes h₂ h₈ h₃₁
      case h_2 _ _ h₁₀ _ _ h₁₁ =>
        split at h₃₂ <;> simp at h₃₂
        subst h₃₂
        cases h₃ ; subst ty
        apply instance_of_attribute_type _ h₁₁ (by simp [Qualified.getType, TypedExpr.typeOf]) h₉
        apply well_typed_entity_attributes h₂ h₈ h₃₁

theorem type_of_getAttr_is_sound {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.getAttr x₁ a) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.getAttr x₁ a) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₅, tx, c₁', h₄, h₆, h₇⟩ := type_of_getAttr_inversion h₃
  subst h₅
  apply And.intro empty_guarded_capabilities_invariant
  rcases h₇ with ⟨ety, h₇⟩ | ⟨rty, h₇⟩ <;>
  have ⟨_, v₁, h₆, h₈⟩ := ih h₁ h₂ h₄  <;>
  simp [EvaluatesTo] at h₆ <;>
  simp [EvaluatesTo, evaluate] <;>
  rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
  <;> try exact type_of_is_inhabited h₂.wf_env h₃
  · have h₉ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.entity ety, c₁') := by simp [h₄, ResultType.typeOf, Except.map]; exact h₇
    rw [h₇] at h₈
    exact type_of_getAttr_is_sound_for_entities h₁ h₂ h₃ h₉ h₆ h₈
  · have h₉ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.record rty, c₁') := by simp [h₄, ResultType.typeOf, Except.map]; exact h₇
    rw [h₇] at h₈
    exact type_of_getAttr_is_sound_for_records h₁ h₃ h₉ h₆ h₈

end Cedar.Thm
