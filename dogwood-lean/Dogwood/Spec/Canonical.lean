import Cedar.Spec.Value
import Cedar.Thm.Data.Set
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.LT

/-!
# Canonical values

A Cedar value has one form per meaning, except a set and a record: `Value.set` and `Value.record`
wrap a list, and Cedar's operations keep it sorted and free of duplicates (`Set.make`,
`Map.make`), but nothing stops a value from holding an unsorted list. `{"a", "b"}` held as
`["b", "a"]` is then a different value from `["a", "b"]`, and compares unequal to it. A value is
**canonical** when every set and every record in it is well-formed (`Canonical`); on canonical
sets, equality is equality of members (`Dogwood.Thm.canonical_set_eq_iff`).

Runtime conformance requires an event's logged record and its context to be canonical
(`Dogwood.Spec.EventSignature.Admits`). `canonicalB` decides `Canonical` by structural recursion,
which the kernel evaluates (`canonicalB_iff`).

Cedar values have no `null`, and a decimal is its numeric value (`Int64` ten-thousandths), so the
other two ways an implementation's values can have several forms, a logged `null` and a decimal
spelling such as `02.5`, have none here: a `null` field is absent, and `02.5` is `2.5`.
-/

namespace Dogwood.Spec

open Cedar.Spec (Value Attr Prim Ext)
open Cedar.Data (Set Map)

/-- **A canonical value**: every set in it is well-formed (its elements sorted and without
duplicates, as `Set.make` builds a set), and so is every record's attribute map, recursively. -/
inductive Canonical : Value → Prop where
  | prim (p : Prim) : Canonical (.prim p)
  | ext (x : Ext) : Canonical (.ext x)
  | set {s : Set Value} : s.WellFormed → (∀ v ∈ s.elts, Canonical v) → Canonical (.set s)
  | record {m : Map Attr Value} : m.WellFormed → (∀ kv ∈ m.toList, Canonical kv.snd) →
      Canonical (.record m)

/-- Each element is before the next under `f`: the list is strictly sorted by `f`. -/
def strictlySortedB {α β : Type} [LT β] [DecidableLT β] (f : α → β) : List α → Bool
  | x :: y :: ys => decide (f x < f y) && strictlySortedB f (y :: ys)
  | _ => true

mutual

/-- Decides `Canonical`, by structural recursion on the value. -/
def canonicalB : Value → Bool
  | .prim _ => true
  | .ext _ => true
  | .set (.mk vs) => strictlySortedB id vs && canonicalsB vs
  | .record (.mk kvs) => strictlySortedB Prod.fst kvs && fieldsCanonicalB kvs

/-- Every value of the list is canonical. -/
def canonicalsB : List Value → Bool
  | [] => true
  | v :: vs => canonicalB v && canonicalsB vs

/-- Every attribute value of the list is canonical. -/
def fieldsCanonicalB : List (Attr × Value) → Bool
  | [] => true
  | (_, v) :: kvs => canonicalB v && fieldsCanonicalB kvs

end

theorem strictlySortedB_iff {α β : Type} [LT β] [DecidableLT β] (f : α → β) :
    (xs : List α) → strictlySortedB f xs = true ↔ xs.SortedBy f
  | [] => by simp [strictlySortedB, List.SortedBy.nil]
  | [x] => by simp [strictlySortedB, List.SortedBy.cons_nil]
  | x :: y :: ys => by
    simp only [strictlySortedB, Bool.and_eq_true, decide_eq_true_eq, strictlySortedB_iff f (y :: ys)]
    constructor
    · rintro ⟨h₁, h₂⟩; exact List.SortedBy.cons_cons h₁ h₂
    · intro h; cases h with
      | cons_cons h₁ h₂ => exact ⟨h₁, h₂⟩

theorem canonical_set_iff {s : Set Value} :
    Canonical (.set s) ↔ s.WellFormed ∧ ∀ v ∈ s.elts, Canonical v := by
  constructor
  · intro h; cases h with
    | set h₁ h₂ => exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩; exact .set h₁ h₂

theorem canonical_record_iff {m : Map Attr Value} :
    Canonical (.record m) ↔ m.WellFormed ∧ ∀ kv ∈ m.toList, Canonical kv.snd := by
  constructor
  · intro h; cases h with
    | record h₁ h₂ => exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩; exact .record h₁ h₂

mutual

/-- **The decider decides `Canonical`.** -/
theorem canonicalB_iff : (v : Value) → canonicalB v = true ↔ Canonical v
  | .prim p => by simp only [canonicalB, true_iff]; exact .prim p
  | .ext x => by simp only [canonicalB, true_iff]; exact .ext x
  | .set (.mk vs) => by
    rw [canonical_set_iff, Set.wf_iff_sorted]
    simp only [canonicalB, Bool.and_eq_true, strictlySortedB_iff, canonicalsB_iff vs, Set.elts]
  | .record (.mk kvs) => by
    rw [canonical_record_iff, Map.wf_iff_sorted]
    simp only [canonicalB, Bool.and_eq_true, strictlySortedB_iff, fieldsCanonicalB_iff kvs,
      Map.toList]

theorem canonicalsB_iff : (vs : List Value) → canonicalsB vs = true ↔ ∀ v ∈ vs, Canonical v
  | [] => by simp [canonicalsB]
  | v :: vs => by
    simp only [canonicalsB, Bool.and_eq_true, canonicalB_iff v, canonicalsB_iff vs,
      List.forall_mem_cons]

theorem fieldsCanonicalB_iff : (kvs : List (Attr × Value)) →
    fieldsCanonicalB kvs = true ↔ ∀ kv ∈ kvs, Canonical kv.snd
  | [] => by simp [fieldsCanonicalB]
  | (k, v) :: kvs => by
    simp only [fieldsCanonicalB, Bool.and_eq_true, canonicalB_iff v, fieldsCanonicalB_iff kvs,
      List.forall_mem_cons]

end

instance (v : Value) : Decidable (Canonical v) := decidable_of_iff _ (canonicalB_iff v)

end Dogwood.Spec
