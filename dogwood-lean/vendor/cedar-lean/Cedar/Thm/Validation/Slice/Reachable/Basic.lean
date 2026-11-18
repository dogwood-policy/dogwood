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

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

inductive ReachableIn : Entities → Set EntityUID → EntityUID → Nat → Prop where
  | in_start {es : Entities} {start : Set EntityUID} {finish : EntityUID} {level : Nat}
    (hs : finish ∈ start) :
    ReachableIn es start finish (level + 1)
  | step {es : Entities} {start : Set EntityUID} {finish : EntityUID} {level : Nat} {ed : EntityData}
    (i : EntityUID)
    (hi : i ∈ start)
    (he : es.find? i = some ed)
    (hr : ReachableIn es ed.sliceEUIDs finish level) :
    ReachableIn es start finish (level + 1)

inductive Value.EuidViaPath : Value → List Attr → EntityUID → Prop where
  | euid (euid : EntityUID) :
    EuidViaPath (.prim (.entityUID euid)) [] euid
  | record {v euid} {a : Attr} {path : List Attr} {attrs : Map Attr Value}
    (ha : attrs.find? a = some v)
    (hv : EuidViaPath v path euid) :
    EuidViaPath (.record attrs)  (a :: path) euid

theorem in_val_then_val_slice {v path euid}
  (hv : Value.EuidViaPath v path euid)
  : euid ∈ v.sliceEUIDs
:= by
  cases v
  case prim p =>
    cases hv
    simp [Value.sliceEUIDs, Set.mem_singleton]
  case record attrs =>
    suffices h : ∃ kv ∈ attrs.toList, euid ∈ kv.snd.sliceEUIDs by
      unfold Value.sliceEUIDs
      simp only [Prod.exists] at h
      simp only [List.mapUnion₃_eq_mapUnion (λ e : (Attr × Value) => e.snd.sliceEUIDs), List.mem_mapUnion_iff_mem_exists, Prod.exists]
      exact h
    cases path <;> cases hv
    rename_i a _ v ha hv
    exists (a, v)
    and_intros
    · exact Map.find?_mem_toList ha
    · exact in_val_then_val_slice hv
  case set | ext => cases hv

def CheckedEvalEntityReachable (e : Expr) :=
  ∀ {n nmax: Nat} {c c' : Capabilities} {tx : TypedExpr} {env : TypeEnv} {request : Request} {entities : Entities} {v: Value} {path : List Attr} {euid : EntityUID},
    CapabilitiesInvariant c request entities →
    InstanceOfWellFormedEnvironment request entities env →
    typeOf e c env = .ok (tx, c') →
    tx.EntityAccessAtLevel env n nmax path →
    evaluate e request entities = .ok v →
    Value.EuidViaPath v path euid →
    ReachableIn entities request.sliceEUIDs euid (n + 1)

theorem reachable_succ {n : Nat} {euid : EntityUID} {start : Set EntityUID} {entities : Entities}
  (hr : ReachableIn entities start euid n)
  : ReachableIn entities start euid (n + 1)
:= by
  cases n <;> cases hr
  case in_start hi =>
    exact ReachableIn.in_start hi
  case step euid' hf hi hr =>
    exact ReachableIn.step euid' hi hf (reachable_succ hr)

theorem entities_attrs_then_find? {entities: Entities} {attrs : Map Attr Value} {uid : EntityUID}
  (he : entities.attrs uid = .ok attrs)
  : ∃ ed, entities.find? uid = some ed ∧ ed.attrs = attrs
:= by
  simp only [Entities.attrs, Map.findOrErr] at he
  split at he <;> simp only [Except.bind_err, Except.bind_ok, reduceCtorEq, Except.ok.injEq] at he
  rename_i ed h₁
  exists ed

theorem entities_tags_then_find? {entities: Entities} {tags : Map Tag Value} {uid : EntityUID}
  (he : entities.tags uid = .ok tags)
  : ∃ ed, entities.find? uid = some ed ∧ ed.tags = tags
:= by
  simp only [Entities.tags, Map.findOrErr] at he
  split at he <;> simp only [Except.bind_err, Except.bind_ok, reduceCtorEq, Except.ok.injEq] at he
  rename_i ed h₁
  exists ed
