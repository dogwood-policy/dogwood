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
This file proves that typechecking of `.binaryApp .hasTag` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_hasTag_inversion {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .hasTag x₁ x₂) c₁ env = .ok (ty, c₂)) :
  ∃ ety c₁' c₂',
    (typeOf x₁ c₁ env).typeOf = .ok (.entity ety, c₁') ∧
    (typeOf x₂ c₁ env).typeOf = .ok (.string, c₂') ∧
    typeOfHasTag ety x₁ x₂ c₁ env = .ok (ty.typeOf, c₂)
:= by
  simp only [typeOf] at h₁
  simp_do_let (typeOf x₁ c₁ env) as h₂ at h₁
  simp_do_let (typeOf x₂ c₁ env) as h₃ at h₁
  rename_i tyc₁ tyc₂
  cases tyc₁
  cases tyc₂
  rename_i ty₁ c₁' ty₂ c₂'
  simp only at h₁
  cases h₄ : ty₁.typeOf <;> simp only [h₄, typeOfBinaryApp, err, reduceCtorEq] at h₁
  cases h₅ : ty₂.typeOf <;> simp only [h₅, reduceCtorEq] at h₁
  rename_i ety
  cases h₆ : typeOfHasTag ety x₁ x₂ c₁ env <;>
  simp only [h₆, Except.bind_err, Except.bind_ok, ok, reduceCtorEq, Except.ok.injEq, Prod.mk.injEq] at h₁
  exists ety, c₁', c₂'
  simp only [h₄, h₅, ResultType.typeOf, Except.map]
  simp [←h₁, h₆, TypedExpr.typeOf]

private theorem map_empty_contains_instance_of_ff [DecidableEq α] [DecidableEq β] {k : α} {env : TypeEnv} :
  InstanceOfType env (Value.prim (Prim.bool ((Map.empty : Map α β).contains k))) (CedarType.bool BoolType.ff)
:= by
  simp only [Map.not_contains_of_empty, false_is_instance_of_ff]

private theorem no_tags_type_implies_no_tags {uid : EntityUID} {env : TypeEnv} {entities : Entities}
  (h₁ : InstanceOfSchema entities env)
  (h₂ : env.ets.tags? uid.ty = .some .none) :
  InstanceOfType env (Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s))) (CedarType.bool BoolType.ff)
:= by
  simp only [Entities.tagsOrEmpty]
  split
  · rename_i d hf
    cases h₁.1 uid d hf with
    | inl h₁ =>
      replace ⟨e, hf', _, _, h₁⟩ := h₁
      simp only [InstanceOfEntityTags] at h₁
      simp only [EntitySchema.tags?, Option.map_eq_some_iff] at h₂
      replace ⟨e', h₂, h₃⟩ := h₂
      simp only [hf', Option.some.injEq] at h₂
      subst h₂
      simp only [EntitySchemaEntry.tags?] at h₁ h₃
      split at h₃
      · simp only [h₃] at h₁
        simp only [h₁, map_empty_contains_instance_of_ff]
      · simp only [h₁, map_empty_contains_instance_of_ff]
    | inr h₁ =>
      replace ⟨_, h₁, ⟨e, _⟩⟩ := h₁
      simp only [h₁, Map.empty, Map.contains, Map.find?, Map.toList, List.find?, Option.isSome]
      constructor
      constructor
  · exact map_empty_contains_instance_of_ff

private theorem no_type_implies_no_tags {uid : EntityUID} {env : TypeEnv} {entities : Entities}
  (h₁ : InstanceOfSchema entities env)
  (h₂ : env.ets.tags? uid.ty = .none) :
  InstanceOfType env (Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s))) (CedarType.bool BoolType.ff)
:= by
  simp only [Entities.tagsOrEmpty]
  split
  · rename_i d hf
    cases h₁.1 uid d hf with
    | inl h₁ =>
      replace ⟨e, h₁, _, _, _⟩ := h₁
      simp only [EntitySchema.tags?, Option.map_eq_none_iff] at h₂
      simp only [h₁, reduceCtorEq] at h₂
    | inr h₁ =>
      replace ⟨_, h₁, ⟨e, _⟩⟩ := h₁
      simp only [h₁, Map.empty, Map.contains, Map.find?, Map.toList, List.find?, Option.isSome]
      constructor
      constructor
  · exact map_empty_contains_instance_of_ff

private theorem mem_capabilities_implies_mem_tags {env : TypeEnv} {x₁ x₂ : Expr} {c₁ : Capabilities} {request : Request} {entities : Entities} {uid : EntityUID} {s : String}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (ih₁ : evaluate x₁ request entities = Except.ok (Value.prim (Prim.entityUID uid)))
  (ih₂ : evaluate x₂ request entities = Except.ok (Value.prim (Prim.string s)))
  (hin : (x₁, Key.tag x₂) ∈ c₁) :
  InstanceOfType env (Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s))) (CedarType.bool BoolType.tt)
:= by
  replace h₁ := h₁.right x₁ x₂ hin
  simp only [EvaluatesTo, evaluate, ih₁, ih₂, apply₂, hasTag, Except.bind_ok, Except.ok.injEq,
    Value.prim.injEq, Prim.bool.injEq, false_or, reduceCtorEq] at h₁
  simp only [h₁, true_is_instance_of_tt]

private theorem hasTag_true_implies_cap_inv {x₁ x₂ : Expr} {request : Request} {entities : Entities} {uid : EntityUID} {s : String}
  (ih₁ : evaluate x₁ request entities = Except.ok (Value.prim (Prim.entityUID uid)))
  (ih₂ : evaluate x₂ request entities = Except.ok (Value.prim (Prim.string s)))
  (ht : (entities.tagsOrEmpty uid).contains s = true) :
  CapabilitiesInvariant (Capabilities.singleton x₁ (Key.tag x₂)) request entities
:= by
  constructor <;>
  intro e k hin <;>
  simp only [Capabilities.singleton, List.mem_singleton, Prod.mk.injEq, and_false, Key.tag.injEq, reduceCtorEq] at hin
  replace ⟨hin, hin'⟩ := hin
  subst hin hin'
  simp only [EvaluatesTo, evaluate, ih₁, ih₂, apply₂, hasTag, Except.bind_ok, ht, or_true]

theorem type_of_hasTag_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.binaryApp .hasTag x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .hasTag x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .hasTag x₁ x₂) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have hok := h₃
  replace ⟨ety, c₁', c₂', h₄, h₅, h₃⟩ := type_of_hasTag_inversion h₃
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  split_type_of h₅ ; rename_i h₅ hl₅ hr₅
  replace ⟨_, v₁, ih₁, hty₁⟩ := ih₁ h₁ h₂ h₄
  replace ⟨_, v₂, ih₂, hty₂⟩ := ih₂ h₁ h₂ h₅
  simp only [EvaluatesTo] at *
  simp only [GuardedCapabilitiesInvariant, evaluate]
  rcases ih₁ with ih₁ | ih₁ | ih₁ | ih₁ <;>
  simp only [ih₁, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_false, or_true, true_and, reduceCtorEq]
  any_goals (apply type_of_is_inhabited h₂.wf_env hok)
  rcases ih₂ with ih₂ | ih₂ | ih₂ | ih₂ <;>
  simp only [ih₂, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_false, or_true, true_and, reduceCtorEq]
  any_goals (apply type_of_is_inhabited h₂.wf_env hok)
  rw [hl₄] at hty₁
  replace ⟨uid, hty₁, hv₁⟩ := instance_of_entity_type_is_entity hty₁
  rw [hl₅] at hty₂
  replace ⟨s, hv₂⟩ := instance_of_string_is_string hty₂
  subst hv₁ hv₂ hty₁
  simp only [apply₂, hasTag, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq]
  simp only [typeOfHasTag, List.empty_eq] at h₃
  have hempty := empty_capabilities_invariant request entities
  simp only [List.empty_eq] at hempty
  split at h₃
  case h_1 heq =>
    simp [ok] at h₃
    have ⟨ hl₃, hr₃ ⟩ := h₃
    simp only [implies_true, reduceCtorEq, false_or, exists_eq_left', true_and, hr₃, ←hl₃, hempty]
    apply no_tags_type_implies_no_tags h₂.instance_of_schema heq
  case h_2 =>
    split at h₃ <;> simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h₃ <;>
    replace ⟨h₃, h₆⟩ := h₃ <;>
    rw [←h₆, ←h₃]
    case isTrue hin =>
      simp only [hempty, implies_true, reduceCtorEq, false_or, exists_eq_left', true_and]
      exact mem_capabilities_implies_mem_tags h₁ ih₁ ih₂ hin
    case isFalse =>
      simp only [reduceCtorEq, false_or, exists_eq_left', bool_is_instance_of_anyBool, and_true]
      intro ht
      exact hasTag_true_implies_cap_inv ih₁ ih₂ ht
  case h_3 heq =>
    split at h₃ <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h₃
    rename_i hact
    simp only [←h₃, hempty, implies_true, reduceCtorEq, false_or, exists_eq_left', true_and]
    exact no_type_implies_no_tags h₂.instance_of_schema heq


end Cedar.Thm
