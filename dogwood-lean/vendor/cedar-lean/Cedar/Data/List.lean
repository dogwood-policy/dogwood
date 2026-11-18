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

public import Cedar.Data.LT
import Batteries.Data.List

/-!
This file contains utilities for working with lists that are canonical or
equivalent modulo ordering and duplicates.  A canonical list is sorted and
duplicate-free according to a strict total order <.
-/

namespace List

open Cedar.Data

----- Definitions -----

public def insertCanonical [LT β] [DecidableLT β] (f : α → β) (x : α) (xs : List α) : List α :=
  match xs with
  | [] => [x]
  | hd :: tl =>
    let fh := f hd
    let fx := f x
    if fx < fh
    then x :: xs
    else if fx > fh
    then hd :: insertCanonical f x tl
    else x :: tl

/--
If the ordering relation < on β is strict, then `canonicalize` returns a
canonical representation of the input list, which is sorted and free of
duplicates.
-/
public def canonicalize [LT β] [DecidableLT β] (f : α → β) : List α → List α
  | [] => []
  | hd :: tl => insertCanonical f hd (canonicalize f tl)

public theorem sizeOf_snd_lt_sizeOf_list {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {x : α × β} {xs : List (α × β)} :
  x ∈ xs → sizeOf x.snd < 1 + sizeOf xs
:= by
  intro h
  rw [Nat.add_comm]
  apply Nat.lt_add_right
  apply @Nat.lt_trans (sizeOf x.snd) (sizeOf x) (sizeOf xs)
  · simp only [sizeOf, Prod._sizeOf_1]
    rw [Nat.add_comm]
    apply Nat.lt_add_of_pos_right
    apply Nat.add_pos_left
    exact Nat.one_pos
  · exact List.sizeOf_lt_of_mem h

public def attach₂ {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] (xs : List (α × β)) :
List { x : α × β // sizeOf x.snd < 1 + sizeOf xs } :=
  xs.pmap Subtype.mk
  (λ _ => sizeOf_snd_lt_sizeOf_list)

public def attach₃ {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] (xs : List (α × β)) :
List { x : α × β // sizeOf x.snd < 1 + (1 + sizeOf xs) } :=
  xs.pmap Subtype.mk
  (λ x => by
    intro h
    rw [Nat.add_comm]
    apply Nat.lt_add_right
    apply List.sizeOf_snd_lt_sizeOf_list h)

public def map₁ {α : Type w} {β : Type u} (xs : List α) (f : {x : α // x ∈ xs} → β) : List β :=
  xs.attach.map f

public def map₂ {α : Type w} {β : Type u} [SizeOf α] [SizeOf β] (xs : List (α × β)) (f : {x : α × β // sizeOf x.snd < 1 + sizeOf xs} → γ) : List γ :=
  xs.attach₂.map f

public def map₃ {α : Type w} {β : Type u} [SizeOf α] [SizeOf β] (xs : List (α × β)) (f : {x : α × β // sizeOf x.snd < 1 + (1 + sizeOf xs)} → γ) : List γ :=
  xs.attach₃.map f

public def mapM₁ {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
  (xs : List α) (f : {x : α // x ∈ xs} → m β) : m (List β) :=
  xs.attach.mapM f

public def mapM₂ {m : Type u → Type v} [Monad m] {γ : Type u} [SizeOf α] [SizeOf β]
  (xs : List (α × β)) (f : {x : α × β // sizeOf x.snd < 1 + sizeOf xs} → m γ) : m (List γ) :=
  xs.attach₂.mapM f

public def mapM₃ {m : Type u → Type v} [Monad m] {γ : Type u} [SizeOf α] [SizeOf β]
  (xs : List (α × β)) (f : { x : α × β // sizeOf x.snd < 1 + (1 + sizeOf xs) } → m γ) : m (List γ) :=
  xs.attach₃.mapM f

/--
Generalization of `List.flatMap` from the standard library:
works for `f` returning various collection types, not just `List`.

That said, if your `f` does return `List`, you may want to use `flatMap`
instead, as there is a large library of lemmas about it in the standard library.
-/
public def mapUnion {α β} [Union α] [EmptyCollection α] (f : β → α) (bs : List β) : α :=
  bs.foldl (λ a b => a ∪ f b) ∅

public def mapUnion₁ {α β} [Union α] [EmptyCollection α]
  (xs : List β) (f : {x : β // x ∈ xs} → α) : α :=
  xs.attach.mapUnion f

public def mapUnion₂ {α β γ} [Union α] [EmptyCollection α] [SizeOf β] [SizeOf γ]
  (xs : List (β × γ)) (f : {x : β × γ // sizeOf x.snd < 1 + sizeOf xs} → α) : α :=
  xs.attach₂.mapUnion f

public def mapUnion₃ [Union α] [EmptyCollection α] [SizeOf β] [SizeOf γ]
  (xs : List (β × γ)) (f : {x : β × γ // sizeOf x.snd < 1 + (1 + sizeOf xs) } → α) : α :=
  xs.attach₃.mapUnion f

public def isSortedBy {α β} [LT β] [DecidableLT β] (l : List α) (f : α → β) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x₁ :: x₂ :: xs =>
    if f x₁ < f x₂ then
      (x₂ :: xs).isSortedBy f
    else
      false

public def isSorted {α} [LT α] [DecidableLT α] (l : List α) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x₁ :: x₂ :: xs =>
    if x₁ < x₂ then
      (x₂ :: xs).isSorted
    else
      false

public def ternaryAny  {α} (l : List α) (p : α → Option Bool) : Option Bool :=
  if l.map p|>.any (· == some true) then
    some true
  else if l.map p|>.any Option.isNone then
    none
  else
    some false

end List
