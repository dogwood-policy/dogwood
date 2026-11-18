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

import Cedar.Thm.Authorization.Evaluator
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Slice.Reachable.Basic

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem typed_record_contains_typed_attrs {rxs : List (Attr × Expr)} {a : Attr} {x : Expr} {c c' : Capabilities} {env : TypeEnv}
  (ht : typeOf (Expr.record rxs) c env = Except.ok (tx, c'))
  (hx : (Map.make rxs).find? a = some x) :
  ∃ rtxs ty atx,
    tx = .record rtxs ty ∧
    (Map.make rtxs).find? a = some atx ∧
    ∃ c', typeOf x c env = .ok (atx, c')
:= by
  have ⟨_, _, htx, hfat⟩ := type_of_record_inversion ht
  have ⟨_, _, hatx, ht''⟩ := find_make_xs_find_make_txs hfat hx
  simp [htx, hatx, ht'']

theorem record_entity_access_implies_attr_entity_access {atx : TypedExpr} {rtxs : List (Attr × TypedExpr)} {ty : CedarType} {n nmax : Nat} {a : Attr} {path : List Attr}
  (hl : (TypedExpr.record rtxs ty).EntityAccessAtLevel env n nmax (a :: path))
  (hatx : (Map.make rtxs).find? a = some atx) :
  atx.EntityAccessAtLevel env n nmax path
:= by
  cases hl
  rename_i atx' _ hfatx' hl
  have hatx : atx' = atx := by
    simpa [hfatx'] using hatx
  simpa [hatx] using hl

theorem checked_eval_entity_reachable_record {rxs : List (Attr × Expr)} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : TypeEnv} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (.record rxs) c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax path)
  (he : evaluate (.record rxs) request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (ih : ∀ a x, (Map.make rxs).find? a = some x → CheckedEvalEntityReachable x) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have ⟨ rvs, hv ⟩ := record_produces_record_value he
  subst hv
  cases ha
  rename_i v a path' hfv hv
  have ⟨ x, hfx, hex ⟩ := record_value_contains_evaluated_attrs he hfv
  have ⟨ rtxs, _, atx, htx, hfatx, _, het⟩ := typed_record_contains_typed_attrs ht hfx
  rw [htx] at hl
  have hl' := record_entity_access_implies_attr_entity_access hl hfatx
  exact ih a x hfx hc hr het hl' hex hv
