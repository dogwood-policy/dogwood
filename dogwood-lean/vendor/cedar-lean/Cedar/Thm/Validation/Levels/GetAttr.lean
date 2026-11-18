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
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Slice
import Cedar.Thm.Validation.Levels.Basic
import Cedar.Thm.Validation.Levels.CheckLevel

/-!
This file proves that level checking for `.getAttr` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_get_attr_entity {e : Expr} {tx₁: TypedExpr} {ty : CedarType} {a : Attr} {n : Nat} {c₀ c₁: Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hl : (tx₁.getAttr a ty).AtLevel env n)
  (ht : typeOf e c₀ env = Except.ok (tx₁, c₁))
  (hety : tx₁.typeOf = CedarType.entity ety)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.getAttr e a) request entities = evaluate (.getAttr e a) request (entities.sliceAtLevel request n)
:= by
  have ⟨ hgc, v, he, hv ⟩ := type_of_is_sound hc hr ht
  rw [hety] at hv
  replace ⟨ euid, hety', hv⟩ := instance_of_entity_type_is_entity hv
  subst hety' hv
  cases hl
  case getAttrRecord hnety _ =>
    specialize hnety euid.ty
    contradiction
  rename_i n hel₁ hl₁ _
  simp only [evaluate]
  have hl₁' := entity_access_at_level_then_at_level hl₁
  specialize ihe hc hr ht hl₁'
  rw [←ihe]
  unfold EvaluatesTo at he
  rcases he with he | he | he | he <;> simp only [he, Except.bind_err]
  have hfeq := checked_eval_entity_find_entities_eq_find_slice hc hr ht hl₁ he
  simp [hfeq, getAttr, attrsOf, Entities.attrs, Map.findOrErr]

theorem level_based_slicing_is_sound_get_attr_record {e : Expr} {tx : TypedExpr} {ty : CedarType} {a : Attr} {n : Nat} {c₀: Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hl : (tx.getAttr a ty).AtLevel env n)
  (htx : typeOf e c₀ env = Except.ok (tx, c₁'))
  (hrty : tx.typeOf = CedarType.record rty)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.getAttr e a) request entities = evaluate (.getAttr e a) request (entities.sliceAtLevel request n)
:= by
  cases hl
  case getAttr hety =>
    simp [hety] at hrty
  rename_i hl
  have ih := ihe hc hr htx hl
  simp only [evaluate, ←ih]
  simp_do_let (evaluate e request entities) as he₁
  rename_i v
  have ⟨avs, he⟩ : ∃ avs, v = .record avs := by
    have ⟨ _, _, he, hty⟩ := type_of_is_sound hc hr htx
    rw [hrty] at hty
    have ⟨avs, hv⟩ := instance_of_record_type_is_record hty
    exists avs
    simpa [EvaluatesTo, hv, he₁] using he
  simp [he, getAttr, attrsOf]

theorem level_based_slicing_is_sound_get_attr {e : Expr} {tx : TypedExpr} {a : Attr} {n : Nat} {c₀ c₁: Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (e.getAttr a) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.getAttr e a) request entities = evaluate (.getAttr e a) request (entities.sliceAtLevel request n)
:= by
  have ⟨ h₇, ty₁, _, ht, h₅, h₆ ⟩ := type_of_getAttr_inversion ht
  rw [h₅] at hl
  cases h₆
  case _ hety =>
    replace ⟨ ety, hety ⟩ := hety
    exact level_based_slicing_is_sound_get_attr_entity hc hr hl ht hety ihe
  case _ hrty =>
    replace ⟨ rty, hrty ⟩ := hrty
    exact level_based_slicing_is_sound_get_attr_record hc hr hl ht hrty ihe
