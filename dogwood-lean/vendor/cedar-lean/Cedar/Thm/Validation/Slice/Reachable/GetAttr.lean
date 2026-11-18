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
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.Validation.Levels.CheckLevel

import Cedar.Thm.Validation.Slice.Reachable.Basic

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem reachable_attr_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {path : List Attr}
  (hr : ReachableIn entities start euid n)
  (he₁: entities.find? euid = some ed)
  (he₂ : Value.EuidViaPath (.record ed.attrs) path euid' ) :
  ReachableIn entities start euid' (n + 1)
:= by
  cases n <;> cases hr
  case in_start n' hi =>
    have he₄ : euid' ∈ ed.sliceEUIDs := by
      suffices h : ∃ v ∈ ed.attrs.values, euid' ∈ v.sliceEUIDs by
        simp [h, EntityData.sliceEUIDs, Set.mem_union, List.mem_mapUnion_iff_mem_exists]
      cases he₂
      rename_i v a path ha hv
      exists v
      constructor
      · exact Map.find?_some_implies_in_values ha
      · exact in_val_then_val_slice hv
    have hr' : ReachableIn entities ed.sliceEUIDs euid' (n' + 1) :=
      ReachableIn.in_start he₄
    exact ReachableIn.step euid hi he₁ hr'
  case step n' ed' euid'' he₁' hi hr' =>
    have ih := reachable_attr_step hr' he₁ he₂
    exact ReachableIn.step euid'' hi he₁' ih

theorem checked_eval_entity_reachable_get_attr {e : Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : TypeEnv} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (e.getAttr a) c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax path)
  (he : evaluate (e.getAttr a) request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (ih : CheckedEvalEntityReachable e) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  simp only [evaluate] at he
  simp_do_let (evaluate e request entities) as he₁ at he
  have ⟨ hc', tx', c₁', ht', htx, h₂ ⟩ := type_of_getAttr_inversion ht
  rw [htx] at hl
  have ⟨ hgc, v, he', hi ⟩ := type_of_is_sound hc hr ht'
  cases hl
  case getAttr v₁' ety n hety hl =>
    have ⟨euid', hv⟩ : ∃ euid', v = Value.prim (Prim.entityUID euid') := by
      rw [hety] at hi
      have ⟨ euid', hety, hv⟩ := instance_of_entity_type_is_entity hi
      simp [hv]
    subst hv

    have hv : v₁' = Value.prim (Prim.entityUID euid') := by
      unfold EvaluatesTo at he'
      rw [he₁] at he'
      cases he' <;> rename_i he' <;> simp only [reduceCtorEq, Except.ok.injEq, false_or] at he'
      exact he'
    subst hv

    simp only [getAttr, attrsOf] at he
    simp_do_let (entities.attrs euid') as he₂ at he
    rename_i attrs
    simp only [Map.findOrErr] at he
    split at he <;> simp only [reduceCtorEq, Except.ok.injEq] at he
    subst he
    rename_i v hv

    have ⟨ ed, hed, hed' ⟩ := entities_attrs_then_find? he₂
    subst attrs
    have ih := ih hc hr ht' hl he₁ (.euid euid')
    have ha' : Value.EuidViaPath (Value.record ed.attrs) (a :: path) euid := .record hv ha
    apply reachable_attr_step ih hed ha'

  case getAttrRecord hty hl =>
    cases h₂ <;> rename_i h₂
    · replace ⟨ ety, h₂ ⟩ := h₂
      specialize hty ety h₂
      contradiction
    · replace ⟨ rty, h₂ ⟩ := h₂
      rw [h₂] at hi
      have ⟨ attrs, hv⟩ := instance_of_record_type_is_record hi ; clear hi
      subst hv
      unfold EvaluatesTo at he'
      rw [he₁] at he'
      cases he' <;> rename_i he' <;> simp only [reduceCtorEq, Except.ok.injEq, false_or] at he'
      subst he'
      simp only [getAttr, attrsOf, Map.findOrErr, Except.bind_ok] at he
      split at he <;> simp only [reduceCtorEq, Except.ok.injEq] at he
      rename_i v hv
      subst he
      have ha' : Value.EuidViaPath (Value.record attrs) (a :: path) euid := .record hv ha
      exact ih hc hr ht' hl he₁ ha'
