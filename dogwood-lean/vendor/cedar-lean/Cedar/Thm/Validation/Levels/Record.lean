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
import Cedar.Thm.Validation.Levels.Basic

/-!
This file proves that level checking for `.record` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_record_attrs {rxs : List (Attr × Expr)} {n : Nat} {c : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : List.Forall₂ (AttrExprHasAttrType c env) rxs atxs)
  (hl : ∀ atx ∈ atxs, atx.snd.AtLevel env n)
  (ih : ∀ x ∈ rxs, TypedAtLevelIsSound x.snd)
  :
  (rxs.mapM₂ λ x => do
    let v ← (evaluate x.1.snd request entities)
    Except.ok (x.1.fst, v)) =
  (rxs.mapM₂ λ x => do
    let v ← (evaluate x.1.snd request (entities.sliceAtLevel request n))
    Except.ok (x.1.fst, v))
:= by
  simp only [List.mapM₂_eq_mapM (λ x : (Attr × Expr) => do let v ← evaluate x.snd request entities; .ok (x.fst, v))]
  simp only [List.mapM₂_eq_mapM (λ x : (Attr × Expr) => do let v ← evaluate x.snd request (entities.sliceAtLevel request n); .ok (x.fst, v))]
  cases ht
  case nil => simp
  case cons rx tx rxtl txtl htx htl =>
    simp only [List.mem_cons, forall_eq_or_imp] at ih hl
    replace ⟨ ihx, ih ⟩ := ih
    replace ⟨ hlx, hl ⟩ := hl
    replace ⟨ _, _, htx ⟩ := htx
    specialize ihx hc hr htx hlx
    simp only [List.mapM_cons, ←ihx]
    have ih' := level_based_slicing_is_sound_record_attrs hc hr htl hl ih
    simp_do_let (evaluate rx.snd request entities) as he₁
    simp only [List.mapM₂_eq_mapM (λ x : (Attr × Expr) => do let v ← evaluate x.snd request entities; .ok (x.fst, v))] at ih'
    simp only [List.mapM₂_eq_mapM (λ x : (Attr × Expr) => do let v ← evaluate x.snd request (entities.sliceAtLevel request n); .ok (x.fst, v))] at ih'
    rw [ih']

theorem level_based_slicing_is_sound_record {rxs : List (Attr × Expr)} {n : Nat} {c₀ c₁: Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (.record rxs) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ih : ∀ x ∈ rxs, TypedAtLevelIsSound x.snd) :
  evaluate (.record rxs) request entities = evaluate (.record rxs) request (entities.sliceAtLevel request n)
:= by
  replace ⟨ hc₁, atxs, htx, hatxs ⟩ := type_of_record_inversion ht
  subst htx
  cases hl
  rename_i hlatxs
  have h := level_based_slicing_is_sound_record_attrs hc hr hatxs hlatxs ih
  simp only [h, evaluate, bindAttr, pure, Except.pure]
