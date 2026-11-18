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
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas
public import Lean.Data.Json.FromToJson.Basic

/-!
# Canonical list-based sets

This file defines a simple set data type, backed by a sorted duplicate-free
list. Functions on sets assume but don't require their inputs to be well-formed
(sorted and duplicate-free). Separate theorems show that these functions produce
well-formed outputs when given well-formed inputs.

Use `Set.make` to construct well-formed sets from lists.
-/

namespace Cedar.Data

public inductive Set (α : Type u) where
| mk (l : List α)
deriving Repr, DecidableEq, Inhabited, Lean.ToJson

namespace Set

public abbrev elts {α : Type u} (s : Set α) := s.1

----- Definitions -----

/--
  Creates an ordered/duplicate free list from a set provided the underlying
  set is well formed.
-/
@[expose]
public def toList {α : Type u} (s : Set α) : List α := s.elts

/-- Creates a well-formed set from the given list. -/
public def make [LT α] [DecidableLT α] (elts : List α) : Set α :=
  Set.mk (elts.canonicalize (·))

/-- Empty set ∅ -/
public def empty {α} : Set α := .mk []

/-- s == ∅ -/
public def isEmpty {α} [DecidableEq α] (s : Set α) : Bool :=
  s == empty

/-- elt ∈ s -/
public def contains {α} [DecidableEq α] (s : Set α) (elt : α) : Bool :=
  s.elts.elem elt                    -- can use binary search instead

/-- s₁ ⊆ s₂ -/
public def subset {α} [DecidableEq α] (s₁ s₂ : Set α) : Bool :=
  s₁.elts.all s₂.contains

/-- s₁ ∩ s₂ ≠ ∅ -/
public def intersects {α} [DecidableEq α] (s₁ s₂ : Set α) : Bool :=
  s₁.elts.any s₂.contains

/-- s₁ ∩ s₂ -/
public def intersect {α} [DecidableEq α] (s₁ s₂ : Set α) : Set α :=
  Set.mk (s₁.elts.inter s₂.elts)      -- well-formed by construction

/-- s₁ ∪ s₂ -/
public def union {α} [LT α] [DecidableLT α] (s₁ s₂ : Set α) : Set α :=
  make (s₁.elts ++ s₂.elts)           -- enforce well-formedness

public instance [LT α] [DecidableLT α] : HAppend (Set α) (Set α) (Set α) where
  hAppend := Set.union

/-- Filters `s` using `f`. -/
public def filter {α} (f : α → Bool) (s : Set α) : Set α :=
  Set.mk (s.elts.filter f)            -- well-formed by construction

/-- s₁ \ s₂. -/
public def difference {α} [LT α] [DecidableLT α] [DecidableEq α] (s₁ s₂ : Set α) : Set α :=
  s₁.filter (!s₂.contains ·)

/-- Maps `f` to `s`.-/
public def map {α β} [LT β] [DecidableLT β] (f : α → β) (s : Set α) : Set β :=
  make (s.elts.map f)                 -- enforce well-formedness

/-- Maps `f` to `s` and returns the result of `err` if any error is encountered. -/
public def mapOrErr {α β ε} [DecidableEq β] [LT β] [DecidableRel (α := β) (· < ·)] (f : α → Except ε β) (s : Set α) (err : ε) : Except ε (Set β) :=
  match s.elts.mapM f with
  | .ok elts => .ok (make elts)    -- enforce well-formedness
  | .error _ => .error err         -- return fixed error to be order-independent

/-- Returns true if all elements of `s` satisfy `f`. -/
public def all {α} (f : α → Bool) (s : Set α) : Bool :=
  s.elts.all f

/-- Returns true if some element of `s` satisfies `f`. -/
public def any {α} (f : α → Bool) (s : Set α) : Bool :=
  s.elts.any f

public def size {α} (s : Set α) : Nat :=
  s.elts.length

public def singleton {α} (a : α) : Set α :=
  Set.mk [a]

/-- Checks if a set if well-formed -/
public def wellFormed {α} [LT α] [DecidableLT α] (s : Set α) : Bool :=
  s.elts.isSorted

/-- If `s` is a singleton set, returns the single element -/
public def singleton? [Inhabited α] (s : Set α) : Option α :=
  match s.elts with
  | [] => none
  | [x] => x
  | _ => none

public def foldl {α β} (f : α → β → α) (init : α) (s : Set β) : α :=
  s.elts.foldl f init

public def product {α β} (s₁ : Set α) (s₂ : Set β) : Set (α × β) :=
  Set.mk $ s₁.elts.product s₂.elts

----- Instances -----

public instance [LT α] : LT (Set α) where
  lt a b := a.elts < b.elts

public instance decLt [LT α] [DecidableEq α] [DecidableLT α] : (n m : Set α) → Decidable (n < m)
  | .mk nelts, .mk melts => List.decidableLT nelts melts

-- enables ∅
public instance : EmptyCollection (Set α) where
  emptyCollection := Set.empty

-- enables ∈
public instance : Membership α (Set α) where
  mem s v := v ∈ s.elts

-- enables ⊆
public instance [DecidableEq α] : HasSubset (Set α) where
  Subset s₁ s₂ := s₁.subset s₂

-- enables ∩
public instance [DecidableEq α] : Inter (Set α) := ⟨Set.intersect⟩

-- enables ∪
public instance [LT α] [DecidableLT α] : Union (Set α) := ⟨Set.union⟩

----- Termination-friendly iterators -----

public def map₁ {α} [LT β] [DecidableLT β] (s : Set α) (f : {a : α // a ∈ s} → β) : Set β :=
  Set.make (s.elts.attach.map f)

public def all₁ {α} (s : Set α) (f : {a : α // a ∈ s} → Bool) : Bool :=
  s.elts.attach.all f

public def any₁ {α} (s : Set α) (f : {a : α // a ∈ s} → Bool) : Bool :=
  s.elts.attach.any f

end Set

end Cedar.Data
