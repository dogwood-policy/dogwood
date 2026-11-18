import Dogwood.Spec.Canonical

/-!
# Canonical values compare by their members

On canonical values, a set means its members: two canonical sets are equal exactly when they have
the same members (`canonical_set_eq_iff`), in whatever order and with whatever repetitions an
implementation received them. `Set.make` builds a canonical set from canonical elements
(`canonical_set_make`), and `Map.make` a canonical record from canonical attribute values
(`canonical_record_make`), so an implementation that canonicalizes its input this way produces
values that conform.
-/

namespace Dogwood.Thm

open Dogwood.Spec
open Cedar.Spec (Value Attr)
open Cedar.Data (Set Map)

/-- **Canonical sets compare as sets.** Two canonical sets are equal exactly when they have the
same members. -/
theorem canonical_set_eq_iff {s₁ s₂ : Set Value} (h₁ : Canonical (.set s₁))
    (h₂ : Canonical (.set s₂)) :
    Value.set s₁ = Value.set s₂ ↔ ∀ v, v ∈ s₁ ↔ v ∈ s₂ := by
  obtain ⟨hw₁, _⟩ := canonical_set_iff.mp h₁
  obtain ⟨hw₂, _⟩ := canonical_set_iff.mp h₂
  rw [Value.set.injEq, Set.eq_means_eqv hw₁ hw₂]
  simp only [List.Equiv, List.subset_def, Set.mem_elts_iff_mem_set]
  constructor
  · rintro ⟨h, h'⟩ v; exact ⟨h, h'⟩
  · intro h; exact ⟨fun hv => (h _).mp hv, fun hv => (h _).mpr hv⟩

/-- `Set.make` builds a canonical set from canonical elements. -/
theorem canonical_set_make {xs : List Value} (h : ∀ v ∈ xs, Canonical v) :
    Canonical (.set (Set.make xs)) :=
  .set (Set.make_wf xs) fun v hv =>
    h v ((Set.mem_make v xs).mp ((Set.mem_elts_iff_mem_set v _).mp hv))

/-- `Map.make` builds a canonical record from canonical attribute values. -/
theorem canonical_record_make {kvs : List (Attr × Value)} (h : ∀ kv ∈ kvs, Canonical kv.snd) :
    Canonical (.record (Map.make kvs)) :=
  .record (Map.make_wf kvs) fun kv hkv => h kv (Map.mem_make_mem_list hkv)

end Dogwood.Thm
