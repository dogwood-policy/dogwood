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

module

public import Cedar.Data.List
public import Cedar.Data.Set

/-!

This file defines a simple map data types, backed by a sorted duplicate-free
list of key-value. Functions maps assume but don't require that their inputs are
well-formed (sorted and duplicate-free). Separate theorems show that these
functions produce well-formed outputs when given well-formed inputs.

Use `Map.make` to construct well-formed maps from lists of key-value pairs.
-/

namespace Cedar.Data

public inductive Map (α : Type u) (β : Type v) where
| mk : List (α × β) -> Map α β
deriving Repr, DecidableEq, Inhabited

namespace Map

----- Definitions -----

/-- Creates a well-formed map from the given list of pairs. -/
public def make {α β} [LT α] [DecidableLT α] (kvs : List (α × β)) : Map α β :=
  Map.mk (kvs.canonicalize Prod.fst)

/-- Empty map -/
public def empty {α β} : Map α β := .mk []

/-- Returns an ordered and duplicate free list provided the given map is well-formed. -/
public def toList {α : Type u} {β : Type v} (m : Map α β) : List (Prod α β) := m.1

/-- Returns the keys of `m` as a set. -/
public def keys {α β} (m : Map α β) : Set α :=
  Set.mk (m.toList.map Prod.fst) -- well-formed by construction

/-- Returns the values of `m` as a list. -/
public def values {α β} (m : Map α β) : List β :=
  m.toList.map Prod.snd

/-- Returns the binding for `k` in `m`, if any. -/
@[expose]
public def find? {α β} [BEq α] (m : Map α β) (k : α) : Option β :=
  match m.toList.find? (λ ⟨k', _⟩ => k' == k) with
  | some (_, v) => some v
  | _           => none

/-- Returns true if `m` contains a mapping for the key `k`. -/
public def contains {α β} [BEq α] (m : Map α β) (k : α) : Bool :=
  (m.find? k).isSome

/-- Returns the binding for `k` in `m` or `err` if none is found. -/
public def findOrErr {α β ε} [BEq α] (m : Map α β) (k : α) (err: ε) : Except ε β :=
  match m.find? k with
  | some v => .ok v
  | _      => .error err

/-- Returns the binding for `k` in `m`, or panics if none is found. -/
public def find! {α β} [Repr α] [BEq α] [Inhabited β] (m : Map α β) (k : α) : β :=
  match m.find? k with
  | some v => v
  | _      => panic! s!"find!: key {repr k} not found"

/-- Filters `m` using `f`. -/
public def filter {α β} (f : α → β → Bool) (m : Map α β) : Map α β :=
  Map.mk (m.toList.filter (λ ⟨k, v⟩ => f k v))

public def size {α β} (m : Map α β) : Nat :=
  m.toList.length

public def mapOnValues {α β γ} (f : β → γ) (m : Map α β) : Map α γ :=
  Map.mk (m.toList.map (λ (k, v) => (k, f v)))

public def mapOnKeys {α β γ} [LT γ] [DecidableLT γ] (f : α → γ) (m : Map α β) : Map γ β :=
  Map.make (m.toList.map (λ (k, v) => (f k, v)))

public def mapMOnValues {α β γ} [LT α] [DecidableLT α] [Monad m] (f : β → m γ) (map : Map α β) : m (Map α γ) := do
  let kvs ← map.toList.mapM (λ (k, v) => f v >>= λ v' => pure (k, v'))
  pure (Map.mk kvs)

public def mapMOnKeys {α β γ} [LT γ] [DecidableLT γ] [Monad m] (f : α → m γ) (map : Map α β) : m (Map γ β) := do
  let kvs ← map.toList.mapM (λ (k, v) => f k >>= λ k' => pure (k', v))
  pure (Map.make kvs)

private theorem sizeOf_toList_lt_map {α β} [SizeOf α] [SizeOf β] (m : Map α β) :
  sizeOf m.toList < sizeOf m
:= by
  unfold toList
  conv => rhs ; unfold sizeOf _sizeOf_inst _sizeOf_1 ; simp only
  omega

public def mapOnValues₂ {α β γ} [SizeOf α] [SizeOf β] (m : Map α β) (f : {x : β // sizeOf x < sizeOf m} → γ) : Map α γ :=
  Map.mk (m.toList.map₂ (λ ⟨(k, v), h⟩ => (k, f ⟨v, by
    have := sizeOf_toList_lt_map m
    simp only at *
    omega⟩)))

public def mapMOnValues₂ {α β γ} [SizeOf α] [SizeOf β] [Monad m] (map : Map α β) (f : {x : β // sizeOf x < sizeOf map} → m γ) : m (Map α γ) := do
  let kvs ← map.toList.mapM₂ (λ ⟨(k, v), h⟩ => do pure (k, ← f ⟨v, by
    have := sizeOf_toList_lt_map map
    simp only at *
    omega⟩))
  pure (Map.mk kvs)

public def wellFormed {α β} [LT α] [DecidableLT α] (m : Map α β) : Bool :=
  m.toList.isSortedBy Prod.fst

----- Instances -----

public instance [LT (Prod α β)] : LT (Map α β) where
  lt a b := a.1 < b.1

public instance decLt [LT (Prod α β)] [DecidableEq (Prod α β)] [DecidableLT (Prod α β)] : (n m : Map α β) → Decidable (n < m)
  | .mk nkvs, .mk mkvs => List.decidableLT nkvs mkvs

-- enables ∈ notation for map keys
public instance : Membership α (Map α β) where
  mem m a := List.Mem a (m.toList.map Prod.fst)

public instance [LT α] [DecidableLT α] : HAppend (Map α β) (Map α β) (Map α β) where
  hAppend a b := Map.make (a.toList ++ b.toList)

end Map

end Cedar.Data
