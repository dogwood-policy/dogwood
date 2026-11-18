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
import Cedar.Thm.Validation.Validator

import Cedar.Thm.Validation.Slice.Reachable

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem slice_at_level_inner_well_formed {entities : Entities} {work : Set EntityUID} {n : Nat} :
  (Entities.sliceAtLevel.sliceAtLevel entities work n).WellFormed
:= by
  unfold Entities.sliceAtLevel.sliceAtLevel
  split
  · exact Set.empty_wf
  · simp only [Set.union_wf]

theorem checked_eval_entity_in_slice  {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : TypeEnv} {entities : Entities} {ed : EntityData}
  (hc : CapabilitiesInvariant c request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax [])
  (he : evaluate e request entities = .ok (Value.prim (Prim.entityUID euid)))
  (hf : entities.find? euid = some ed) :
  (Entities.sliceAtLevel entities request (n + 1)).find? euid = some ed
:= by
  simp only [Entities.sliceAtLevel]
  have hw : ReachableIn entities request.sliceEUIDs euid (n + 1) :=
    checked_eval_entity_reachable hc hr ht hl he (.euid euid)
  have hi := slice_contains_reachable hw
  rw [←hf]
  let eids := Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs (n + 1)
  let eds := eids.elts.filterMap (λ e => do some (e, ← Map.find? entities e))
  replace hmake : Map.mk eds = Map.make eds := by
    have hsorted := eids.wf_iff_sorted.mp slice_at_level_inner_well_formed
    have hsbfst : eds.SortedBy Prod.fst := List.filterMap_key_id_sortedBy_key hsorted
    have hwf : (Map.mk eds).WellFormed := by
      simpa [Map.wf_iff_sorted] using hsbfst
    simpa [Map.WellFormed] using hwf
  rw [←hmake]
  exact Map.find?_filterMap_key_id hi

theorem not_entities_then_not_slice {n: Nat} {request : Request} {uid : EntityUID} {entities : Entities}
  (hse : entities.find? uid = none) :
  (Entities.sliceAtLevel entities request n).find? uid = none
:= by
  simp only [Entities.sliceAtLevel]
  exact Map.filterMap_key_id_key_none_implies_find?_none hse

/--
If an expression checks at level `n` and then evaluates to an entity, then the
data for that entity in the slice will be the same as in the original entities.
-/
theorem checked_eval_entity_find_entities_eq_find_slice  {n nmax : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : TypeEnv} {entities : Entities}
  (hc : CapabilitiesInvariant c request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax [])
  (he : evaluate e request entities = .ok (Value.prim (Prim.entityUID euid))) :
  (Entities.sliceAtLevel entities request (n + 1)).find? euid = entities.find? euid
:= by
  cases hfe : Map.find? entities euid
  case none =>
    exact not_entities_then_not_slice hfe
  case some =>
    exact checked_eval_entity_in_slice hc hr ht hl he hfe
