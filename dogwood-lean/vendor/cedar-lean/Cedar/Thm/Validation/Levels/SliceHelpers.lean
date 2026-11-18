import Cedar.Spec
import Cedar.Data
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.Validation.Slice.Reachable
import Cedar.Thm.Validation.Levels.ReachableChild

namespace Cedar.Thm

open Cedar.Data Cedar.Spec Cedar.Validation

/-- If `next` is found in record `r` at key `a`, then sliceEUIDs of `next` ⊆ sliceEUIDs of record. -/
theorem sliceEUIDs_record_field {r : Map Attr Value} {a : Attr} {next : Value}
    (hfind : r.find? a = some next) :
    ∀ uid, uid ∈ Value.sliceEUIDs next → uid ∈ Value.sliceEUIDs (.record r) := by
  intro uid hmem
  unfold Value.sliceEUIDs
  simp only [List.mapUnion₃_eq_mapUnion (λ e : (Attr × Value) => e.snd.sliceEUIDs),
             List.mem_mapUnion_iff_mem_exists, Prod.exists]
  exact ⟨a, next, Map.find?_mem_toList hfind, hmem⟩

/-- If `next` is found in entity data attrs at key `a`, then sliceEUIDs of `next` ⊆ entity's sliceEUIDs. -/
theorem sliceEUIDs_entity_attr {ed : EntityData} {a : Attr} {next : Value}
    (hfind : ed.attrs.find? a = some next) :
    ∀ uid, uid ∈ Value.sliceEUIDs next → uid ∈ ed.sliceEUIDs := by
  intro uid hmem
  have hval : next ∈ ed.attrs.values := Map.find?_some_implies_in_values hfind
  simp only [EntityData.sliceEUIDs, Set.mem_union, List.mem_mapUnion_iff_mem_exists]
  left
  exact ⟨next, hval, hmem⟩

end Cedar.Thm
