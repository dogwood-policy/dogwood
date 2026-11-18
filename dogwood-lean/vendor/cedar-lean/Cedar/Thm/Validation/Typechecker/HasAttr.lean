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
This file proves that typechecking of `.hasAttr` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem hasAttrInRecord_has_empty_or_singleton_capabilities {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {rty : RecordType} {ty₁ : CedarType} :
  hasAttrInRecord rty x₁ a c₁ b = Except.ok (ty₁, c₂) →
  c₂ = ∅ ∨ c₂ = Capabilities.singleton x₁ (.attr a)
:= by
  intro h₁
  simp [hasAttrInRecord] at h₁
  split at h₁ <;>
  (try split at h₁) <;>
  simp [ok] at h₁ <;>
  simp [h₁]

theorem type_of_hasAttr_inversion {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (h₁ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (tx, c₂)) :
  (c₂ = ∅ ∨ c₂ = Capabilities.singleton x₁ (.attr a)) ∧
  ∃ tx₁ c₁',
    typeOf x₁ c₁ env = .ok (tx₁, c₁') ∧
    tx = .hasAttr tx₁ a tx.typeOf ∧
    ((∃ ety, tx₁.typeOf = .entity ety) ∨
     (∃ rty, tx₁.typeOf = .record rty))
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfHasAttr, bind, Except.bind] at h₁
    split at h₁ <;> try contradiction
    · simp
      split at h₁ <;> simp [ok] at h₁
      rename_i heq₁ _ _ heq₂
      simp [heq₁, ←h₁]
      simp [TypedExpr.typeOf]
      apply hasAttrInRecord_has_empty_or_singleton_capabilities heq₂
    · split at h₁
      · split at h₁ <;> simp [ok] at h₁
        rename_i heq₁ _ _ _ _ _ heq₃
        simp [heq₁, ←h₁]
        simp [TypedExpr.typeOf]
        apply hasAttrInRecord_has_empty_or_singleton_capabilities heq₃
      · split at h₁ <;> simp [ok, err] at h₁
        rename_i heq₁ _ _ heq₃
        simp [heq₁, ←h₁]
        simp [TypedExpr.typeOf]

theorem type_of_hasAttr_is_sound_for_records {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : TypeEnv} {rty : RecordType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (h₃ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.record rty, c₁'))
  (h₄ : evaluate x₁ request entities = Except.ok v₁)
  (h₅ : InstanceOfType env v₁ (CedarType.record rty)) :
  ∃ v,
  (hasAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   hasAttr v₁ a entities = Except.error Error.extensionError ∨
   hasAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   hasAttr v₁ a entities = Except.ok v) ∧
  InstanceOfType env v ty.typeOf
:= by
  have ⟨r, h₅⟩ := instance_of_record_type_is_record h₅
  subst h₅
  simp [hasAttr, attrsOf]
  split_type_of h₃ ; rename_i h₃ hl₃ _
  simp [typeOf, hl₃, h₃, typeOfHasAttr, hasAttrInRecord] at h₂
  split at h₂
  case h_1 =>
    split at h₂ <;> simp [ok] at h₂ <;> simp [←h₂.left]
    case isFalse => exact bool_is_instance_of_anyBool _
    cases h₆ : (Map.contains r a)
    case true => exact true_is_instance_of_tt
    rename_i h₇
    cases h₇
    case inl _ h₇ =>
      simp [CapabilitiesInvariant] at h₁
      replace h₁ := h₁.left x₁ a h₇
      simp [EvaluatesTo, evaluate, h₄, hasAttr, attrsOf, h₆] at h₁
    case inr h₇ h₈ =>
      simp [Qualified.isRequired] at h₈
      split at h₈ <;> simp at h₈
      have h₉ := required_attribute_is_present h₅ h₇
      simp [←Map.contains_iff_some_find?, h₆] at h₉
  case h_2 =>
    simp [ok] at h₂
    have ⟨h₂, _⟩ := h₂
    simp [←h₂]
    cases h₆ : (Map.contains r a)
    case false => exact false_is_instance_of_ff
    rename_i _ h₇ _ _
    have h₇ := absent_attribute_is_absent h₅ h₇
    simp [Map.contains_iff_some_find?, h₇] at h₆


theorem type_of_hasAttr_is_sound_for_entities {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : TypeEnv} {ety : EntityType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (h₄ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.entity ety, c₁'))
  (h₅ : evaluate x₁ request entities = Except.ok v₁)
  (h₆ : InstanceOfType env v₁ (CedarType.entity ety)) :
  ∃ v,
  (hasAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   hasAttr v₁ a entities = Except.error Error.extensionError ∨
   hasAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   hasAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType env v ty.typeOf
:= by
  have ⟨uid, h₆, h₇⟩ := instance_of_entity_type_is_entity h₆
  subst h₆ h₇
  simp [hasAttr, attrsOf]
  split_type_of h₄ ; rename_i h₄ hl₄ _
  simp [typeOf, h₄, hl₄, typeOfHasAttr] at h₃
  split at h₃ <;> try simp [err, hasAttrInRecord] at h₃
  rename_i _ rty h₇
  split at h₃
  case h_1 =>
    split at h₃ <;> rcases h₃ with ⟨h₃, _⟩
    case isFalse => exact bool_is_instance_of_anyBool _
    cases h₈ : Map.contains (Entities.attrsOrEmpty entities uid) a
    case true => exact true_is_instance_of_tt
    rename_i _ _ _ _  h₉
    simp [CapabilitiesInvariant] at h₁
    replace h₁ := h₁.left x₁ a h₉
    simp [EvaluatesTo, evaluate, h₅, hasAttr, attrsOf, h₈] at h₁
  case h_2 =>
    simp [ok] at h₃
    have ⟨h₃, _⟩ := h₃
    simp [←h₃]
    cases h₈ : Map.contains (Entities.attrsOrEmpty entities uid) a
    case false => exact false_is_instance_of_ff
    rename_i _ _ h₉ _ _
    simp [Entities.attrsOrEmpty] at h₈
    split at h₈
    case h_1 _ _ _ _ _ h₁₀ =>
      have h₁₁ := well_typed_entity_attributes h₂ h₁₀ h₇
      have h₁₂ := absent_attribute_is_absent h₁₁ h₉
      simp [Map.contains_iff_some_find?, h₁₂] at h₈
    case h_2 =>
      rcases (Map.not_contains_of_empty a) with _
      contradiction
  case h_2 =>
    simp [ok] at h₃
    split at h₃ <;> try simp at h₃
    replace ⟨h₃, _⟩ := h₃
    simp [←h₃]
    unfold Entities.attrsOrEmpty
    rename_i _ h₇ _ _
    simp [EntitySchema.attrs?] at h₇
    replace ⟨_, _, h₂⟩ := h₂
    cases h₈ : Map.find? entities uid
    case none => exact false_is_instance_of_ff
    cases h₂.1 uid _ h₈ with
    | inl h₂ =>
      replace ⟨_, h₈, _⟩ := h₂
      rw [h₇] at h₈
      contradiction
    | inr h₂ =>
      -- Action entity always have empty attributes
      simp only [h₂.left]
      exact false_is_instance_of_ff

theorem type_of_hasAttr_is_sound {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.hasAttr x₁ a) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.hasAttr x₁ a) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₅, ty₁, c₁', hty₁, hty, h₄⟩ := type_of_hasAttr_inversion h₃
  apply And.intro
  case left =>
    simp [GuardedCapabilitiesInvariant, CapabilitiesInvariant]
    intro h₆
    constructor <;>
    intro x aₓ h₇ <;>
    cases h₅ <;> rename_i h₈ <;> subst h₈ <;> simp [Capabilities.singleton] at h₇
    have ⟨h₇, h₈⟩ := h₇
    subst h₇; subst h₈
    simp [EvaluatesTo, h₆]
  case right =>
    rcases h₄ with ⟨ety, h₄⟩ | ⟨rty, h₄⟩ <;>
    have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ hty₁  <;>
    simp [EvaluatesTo] at h₆ <;>
    simp [EvaluatesTo, evaluate] <;>
    rw [h₄] at h₇ <;>
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    <;> try exact type_of_is_inhabited h₂.wf_env h₃
    · have h₈ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.entity ety, c₁') := by simp [h₄, hty₁, ResultType.typeOf, Except.map]
      exact type_of_hasAttr_is_sound_for_entities h₁ h₂ h₃ h₈ h₆ h₇
    · have h₈ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.record rty, c₁') := by simp [h₄, hty₁, ResultType.typeOf, Except.map]
      exact type_of_hasAttr_is_sound_for_records h₁ h₃ h₈ h₆ h₇


end Cedar.Thm
