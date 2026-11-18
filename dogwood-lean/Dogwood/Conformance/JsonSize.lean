import Lean.Data.Json

/-!
# Sizes of JSON values, for decoders that recurse on what they read

A decoder of a recursive type reads a sub-value of its input (an object's field, an array's
element) and recurses on it. Lean's `Json` keeps an object's fields in a `Std.TreeMap.Raw`, an
`Impl` tree, so this file shows that every value a lookup returns is smaller than the value it
was read from (`sizeOf`), and gives each accessor of `Lean.Json` a form that returns the value
with that fact: `getObjValS`, `getArrValS`, `getArrS`. Each is proved equal to the accessor it
refines (`getObjValS_val`, `getArrValS_val`, `getArrS_val`), so a decoder written with them
reads exactly what the original reads, and is total by well-founded recursion on `sizeOf`.
-/

namespace Dogwood.Conformance

open Lean (Json)
open Std.DTreeMap.Internal

theorem sizeOf_impl_get? {β : Type} [SizeOf β] [Ord String] :
    (t : Impl String (fun _ => β)) → (k : String) → (v : β) →
    Impl.Const.get? t k = some v → sizeOf v < sizeOf t
  | .leaf, _, _, h => by simp [Impl.Const.get?] at h
  | .inner _ k' v' l r, k, v, h => by
    simp only [Impl.Const.get?] at h
    have hl := sizeOf_impl_get? l k v
    have hr := sizeOf_impl_get? r k v
    simp only [Impl.inner.sizeOf_spec]
    split at h
    · have := hl h; omega
    · have := hr h; omega
    · cases h; omega

theorem impl_foldr_inner {β : Type} {δ : Type} (f : String → β → δ → δ) (init : δ) (sz : Nat)
    (k : String) (v : β) (l r : Impl String (fun _ => β)) :
    Impl.foldr f init (.inner sz k v l r) = Impl.foldr f (f k v (Impl.foldr f init r)) l := rfl

theorem impl_foldr_leaf {β : Type} {δ : Type} (f : String → β → δ → δ) (init : δ) :
    Impl.foldr f init (.leaf : Impl String (fun _ => β)) = init := rfl

/-- Every value the in-order fold lists is a node's value. -/
theorem sizeOf_impl_foldr_mem {β : Type} [SizeOf β] :
    (t : Impl String (fun _ => β)) → (init : List (String × β)) → (x : String × β) →
    x ∈ Impl.foldr (fun k v l => (k, v) :: l) init t → x ∈ init ∨ sizeOf x.2 < sizeOf t
  | .leaf, init, x, h => by rw [impl_foldr_leaf] at h; exact .inl h
  | .inner sz k v l r, init, x, h => by
    rw [impl_foldr_inner] at h
    simp only [Impl.inner.sizeOf_spec]
    rcases sizeOf_impl_foldr_mem l _ x h with h' | h'
    · rcases List.mem_cons.mp h' with rfl | h''
      · exact .inr (by simp; omega)
      · rcases sizeOf_impl_foldr_mem r init x h'' with h3 | h3
        · exact .inl h3
        · exact .inr (by omega)
    · exact .inr (by omega)

theorem sizeOf_obj (kvs : Std.TreeMap.Raw String Json compare) :
    sizeOf (Json.obj kvs) = 1 + (1 + (1 + sizeOf kvs.inner.inner)) := by
  obtain ⟨⟨t⟩⟩ := kvs; simp

/-- A field an object lists is smaller than the object. -/
theorem sizeOf_lt_of_mem_toList {kvs : Std.TreeMap.Raw String Json compare} {x : String × Json}
    (h : x ∈ kvs.toList) : sizeOf x.2 < sizeOf (Json.obj kvs) := by
  rw [sizeOf_obj]
  have := sizeOf_impl_foldr_mem kvs.inner.inner [] x h
  simp at this
  omega

/-- A field an object's lookup returns is smaller than the object. -/
theorem sizeOf_lt_of_getObjVal? {j : Json} {k : String} {v : Json} (h : j.getObjVal? k = .ok v) :
    sizeOf v < sizeOf j := by
  cases j with
  | obj kvs =>
    simp only [Json.getObjVal?] at h
    split at h
    · rename_i v' hv
      cases h
      rw [sizeOf_obj]
      have := @sizeOf_impl_get? Json _ ⟨compare⟩ kvs.inner.inner k v hv
      omega
    · cases h
  | _ => simp [Json.getObjVal?] at h

theorem sizeOf_lt_of_mem_arr {a : Array Json} {v : Json} (h : v ∈ a) : sizeOf v < sizeOf (Json.arr a) := by
  have := Array.sizeOf_lt_of_mem h
  simp; omega

/-- An element an array's lookup returns is smaller than the array. -/
theorem sizeOf_lt_of_getArrVal? {j : Json} {i : Nat} {v : Json} (h : j.getArrVal? i = .ok v) :
    sizeOf v < sizeOf j := by
  cases j with
  | arr a =>
    simp only [Json.getArrVal?] at h
    split at h
    · rename_i v' hv
      cases h
      exact sizeOf_lt_of_mem_arr (Array.mem_of_getElem? hv)
    · cases h
  | _ => simp [Json.getArrVal?] at h

/-! ## The accessors, with the size fact -/

/-- `Json.getObjVal?`, with the fact that the field is smaller. -/
def getObjValS (j : Json) (k : String) : Except String {v : Json // sizeOf v < sizeOf j} :=
  match h : j.getObjVal? k with
  | .ok v => .ok ⟨v, sizeOf_lt_of_getObjVal? h⟩
  | .error e => .error e

theorem getObjValS_val (j : Json) (k : String) :
    (getObjValS j k).map Subtype.val = j.getObjVal? k := by
  unfold getObjValS
  split <;> simp_all [Except.map]

/-- `Json.getArrVal?`, with the fact that the element is smaller. -/
def getArrValS (j : Json) (i : Nat) : Except String {v : Json // sizeOf v < sizeOf j} :=
  match h : j.getArrVal? i with
  | .ok v => .ok ⟨v, sizeOf_lt_of_getArrVal? h⟩
  | .error e => .error e

theorem getArrValS_val (j : Json) (i : Nat) :
    (getArrValS j i).map Subtype.val = j.getArrVal? i := by
  unfold getArrValS
  split <;> simp_all [Except.map]

/-- `Json.getArr?`, each element with the fact that it is smaller than the array. -/
def getArrS (j : Json) : Except String (Array {v : Json // sizeOf v < sizeOf j}) :=
  match j with
  | .arr a => .ok (a.attach.map fun ⟨v, h⟩ => ⟨v, sizeOf_lt_of_mem_arr h⟩)
  | _ => .error "array expected"

theorem getArrS_val (j : Json) : (getArrS j).map (·.map Subtype.val) = j.getArr? := by
  cases j <;> simp [getArrS, Json.getArr?, Except.map, Array.map_attach_eq_pmap]
  all_goals rfl

end Dogwood.Conformance
