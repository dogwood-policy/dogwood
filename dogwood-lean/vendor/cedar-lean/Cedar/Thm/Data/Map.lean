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

public import Cedar.Data.Map
public import Cedar.Data.LT
import all Cedar.Data.Map -- inside this module, we're allowed to unfold defs in Cedar.Data.Map that are not normally exposed
import Cedar.Data.SizeOf
import Cedar.Thm.Data.Control
public import Cedar.Thm.Data.List
public import Cedar.Thm.Data.Set

/-!
# Map properties

This file proves useful properties of canonical list-based maps defined in
`Cedar.Data.Map`.
-/

namespace Cedar.Data.Map

/-! ### Well-formed maps -/

public def WellFormed {α β} [LT α] [DecidableLT α] (m : Map α β) :=
  m = Map.make m.toList

public theorem if_wellformed_then_exists_make [LT α] [DecidableLT α] (m : Map α β) :
  WellFormed m → ∃ list, m = Map.make list
:= by
  intro h₁
  exists m.toList

public theorem wf_iff_sorted {α β} [LT α] [DecidableLT α] [StrictLT α] {m : Map α β} :
  m.WellFormed ↔ m.toList.SortedBy Prod.fst
:= by
  constructor
  case mp =>
    intro h
    rw [WellFormed, make] at h
    rw [h, toList]
    simp only [List.canonicalize_sortedBy]
  case mpr =>
    intro h
    rw [toList] at *
    replace h := List.sortedBy_implies_canonicalize_eq h
    rw [WellFormed, toList, make, h]

public theorem wf_implies_tail_wf {α β} [LT α] [DecidableLT α] [StrictLT α]
  {hd : α × β} {tl : List (α × β)}
  (hwf : (mk (hd :: tl)).WellFormed) :
  (mk tl).WellFormed
:= by
  have := wf_iff_sorted.mp hwf
  cases tl with
  | nil =>
    simp [Map.WellFormed, Map.toList, make, List.canonicalize_nil]
  | cons hd2 tl =>
    apply wf_iff_sorted.mpr
    cases this
    simp only [Map.toList]
    assumption

public theorem wf_empty {α β} [LT α] [DecidableLT α] :
  (Map.empty : Map α β).WellFormed
:= by simp [Map.WellFormed, Map.make, Map.empty, List.canonicalize_nil, Map.toList]

public theorem wf_singleton [LT α] [DecidableLT α] (a : α) (b : β) :
  (Map.mk [(a, b)]).WellFormed
:= by
  simp [WellFormed, make, toList, List.canonicalize_singleton]

/--
  In well-formed maps, if there are two pairs with the same key, then they have
  the same value
-/
public theorem key_maps_to_one_value [DecidableEq α] [LT α] [DecidableLT α] [StrictLT α] (k : α) (v₁ v₂ : β) (m : Map α β) :
  m.WellFormed →
  (k, v₁) ∈ m.toList →
  (k, v₂) ∈ m.toList →
  v₁ = v₂
:= by
  simp only [wf_iff_sorted, toList]
  intro wf h₁ h₂
  have h₃ := List.mem_of_sortedBy_unique wf h₁ h₂ (by simp)
  injection h₃

/--
  If two maps have exactly equal (k,v) sets, then the maps are equal

  This doesn't require WellFormed, but we use it in the proof of
  `eq_iff_toList_equiv` below
-/
@[simp]
public theorem eq_iff_toList_eq {m₁ m₂ : Map α β} :
  m₁.toList = m₂.toList ↔ m₁ = m₂
:= by
  cases m₁ with | mk m₁
  cases m₂ with | mk m₂
  simp [Map.toList]

/--
  If two well-formed maps have equivalent (k,v) sets, then the maps are actually
  equal
-/
@[simp]
public theorem eq_iff_toList_equiv [LT α] [DecidableLT α] [StrictLT α] {m₁ m₂ : Map α β}
  (wf₁ : m₁.WellFormed)
  (wf₂ : m₂.WellFormed) :
  m₁.toList ≡ m₂.toList ↔ m₁ = m₂
:= by
  constructor
  case mp =>
    intro h₁
    simp [wf_iff_sorted, toList] at wf₁ wf₂
    have h₂ := List.sortedBy_equiv_implies_eq Prod.fst wf₁ wf₂ h₁
    exact eq_iff_toList_eq.mp h₂
  case mpr =>
    intro h₁
    subst h₁
    exact List.Equiv.refl

/-! ### empty, contains, mem, toList, keys, values -/

public theorem keys_wf [LT α] [DecidableLT α] [StrictLT α] (m : Map α β) :
  m.WellFormed → m.keys.WellFormed
:= by
  unfold keys
  intro wf
  simp only [wf_iff_sorted, toList] at wf
  simp only [Set.wf_iff_sorted]
  simp only [Set.elts]
  apply (List.map_eq_implies_sortedBy _).mp wf
  simp only [List.map_map]
  apply List.map_congr
  simp only [Function.comp_apply, id_eq, implies_true]

@[simp]
public theorem toList_empty {α β} :
  (Map.empty : Map α β).toList = []
:= by simp [empty, toList]

@[simp]
public theorem toList_nil_iff_empty {m : Map α β} :
  m.toList = [] ↔ m = Map.empty
:= by
  unfold toList empty
  constructor <;> intro h
  case mp => match m with
    | mk [] => trivial
    | mk ((k, v) :: kvs) => trivial
  case mpr => simp [h]

@[simp]
public theorem mk_toList_id (m : Map α β) :
  mk m.toList = m
:= by simp only [toList]

@[simp]
public theorem toList_mk_id (kvs : List (α × β)) :
  (mk kvs).toList = kvs
:= by simp only [toList]

/--
As a crutch to accommodate some pre-existing usage, we provide this theorem. But
TODO in the future we should transition users of this theorem to instead use
public theorems about `toList` and not have to expose the internals of
`Data.Map`.
-/
public theorem deprecated_toList_def (m : Map α β) :
  m.toList = m.1
:= by simp [toList]

public theorem in_list_in_map {α : Type u} (k : α) (v : β) (m : Map α β) :
  (k, v) ∈ m.toList → k ∈ m
:= by
  intro h₀
  have h₁ : k ∈ (List.map Prod.fst m.toList) := by simp only [List.mem_map] ; exists (k, v)
  apply h₁

public theorem in_list_in_keys {k : α} {v : β} {m : Map α β} :
  (k, v) ∈ m.toList → k ∈ m.keys
:= by
  intro h₀
  simp [keys, ← Set.mem_set_iff_mem_mk]
  exists v

public theorem in_list_in_values {k : α} {v : β} {m : Map α β} :
  (k, v) ∈ m.toList → v ∈ m.values
:= by
  simp only [values, List.mem_map]
  intro h₁
  exists (k, v)

public theorem in_keys_iff_in_map {k : α} {m : Map α β} :
  k ∈ m.keys ↔ k ∈ m
:= by simp only [Membership.mem, Map.keys]

public theorem in_keys_iff_contains [BEq α] [LawfulBEq α] {k : α} {m : Map α β} :
  (k ∈ m.keys ↔ m.contains k)
:= by
  have h_mem_list := List.mem_map_iff_find? (k := k) (f := Prod.fst) (kvs := m.toList)
  simp only [Membership.mem] at h_mem_list
  simp only [Membership.mem, Map.keys, Map.contains, Map.find?]
  rw [h_mem_list]
  cases h : List.find? (λ x => x.fst == k) m.toList <;> simp

/-- kinda the converse of `in_list_in_values` -/
public theorem in_values_exists_key {m : Map α β} {v : β} :
  v ∈ m.values → ∃ k, (k, v) ∈ m.toList
:= by
  simp only [values, List.mem_map, forall_exists_index, and_imp]
  intro (k, v) h₁ h₂
  subst h₂
  exists k

public theorem in_keys_exists_value {m : Map α β} {k : α} :
  k ∈ m.keys → ∃ v, (k, v) ∈ m.toList
:= by
  simp [keys, ← Set.mem_set_iff_mem_mk]

public theorem values_cons {m : Map α β} :
  m.toList = (k, v) :: tl →
  m.values = v :: (mk tl).values
:= by
  unfold values toList
  intro h₁
  simp [h₁]

public theorem contains_iff_some_find? {α β} [BEq α] {m : Map α β} {k : α} :
  m.contains k ↔ ∃ v, m.find? k = .some v
:= by simp [contains, Option.isSome_iff_exists]

public theorem find?_some_implies_contains {α β} [BEq α] {m : Map α β} {k : α} {v : β} :
  m.find? k = .some v → m.contains k
:= by
  intros h
  apply contains_iff_some_find?.mpr
  simp [h]

@[simp]
public theorem not_find?_of_empty [BEq α] {k : α} :
  (Map.empty : Map α β).find? k = none
:= by simp [empty, find?, toList]

public theorem not_contains_of_empty {α β} [BEq α] (k : α) :
  ¬ (Map.empty : Map α β).contains k
:= by simp [contains, not_find?_of_empty]

/-! ### make and mk -/

public theorem make_wf [LT α] [StrictLT α] [DecidableLT α] (xs : List (α × β)) :
  WellFormed (Map.make xs)
:= by
  simp only [WellFormed, make, toList, List.canonicalize_idempotent]

public theorem mk_wf [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  xs.SortedBy Prod.fst → (Map.mk xs).WellFormed
:= by
  intro h
  replace h := List.sortedBy_implies_canonicalize_eq h
  rw [← h, WellFormed, make, toList]
  simp only [List.canonicalize_idempotent]

public theorem make_eq_mk [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  xs.SortedBy Prod.fst ↔ Map.make xs = Map.mk xs
:= by
  constructor <;> intro h
  case mp =>
    simp only [make, List.sortedBy_implies_canonicalize_eq h]
  case mpr =>
    simp only [make, mk.injEq] at h
    rw [← h]
    exact List.canonicalize_sortedBy _ _

public theorem toList_make_eq_canonicalize [LT α] [StrictLT α] [DecidableLT α] (xs : List (α × β)) :
  (Map.make xs).toList = List.canonicalize Prod.fst xs
:= by simp [make, toList]

public theorem make_singleton [LT α] [DecidableLT α] [StrictLT α] (k : α) (v : β) :
  Map.make [(k, v)] = Map.mk [(k, v)]
:= by
  rw [←make_eq_mk]
  exact List.SortedBy.cons_nil

/--
  Note that the converse of this is not true:
  counterexample `xs = [(1, false), (1, true)]`.
  (The property here would not hold for either `x = (1, false)` or `x = (1, true)`.)

  For a limited converse, see `mem_list_mem_make` below.
-/
public theorem mem_make_mem_list [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  x ∈ (Map.make xs).toList → x ∈ xs
:= by
  simp only [toList, make]
  intro h₁
  have h₂ := List.canonicalize_subseteq Prod.fst xs
  simp only [List.subset_def] at h₂
  exact h₂ h₁

/--
  Very similar to `mem_make_mem_list` above
-/
public theorem mem_values_make [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  v ∈ (Map.make xs).values → v ∈ xs.map Prod.snd
:= by
  -- despite the similarity to `mem_make_mem_list`, the proof does not currently
  -- use `mem_make_mem_list`
  simp only [values, make]
  simp only [List.mem_map, forall_exists_index, and_imp]
  intro (k, v) h₁ h₂
  exists (k, v)
  subst h₂
  simp only [and_true]
  have h₂ := List.canonicalize_subseteq Prod.fst xs
  simp only [List.subset_def] at h₂
  exact h₂ h₁

/--
  This limited converse of `mem_make_mem_list` requires that the input list is
  SortedBy Prod.fst.
-/
public theorem mem_list_mem_make [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  xs.SortedBy Prod.fst →
  x ∈ xs → x ∈ (Map.make xs).toList
:= by
  simp only [toList, make]
  intro h₁ h₂
  have h₃ := List.sortedBy_implies_canonicalize_eq h₁
  rw [← h₃] at h₂
  exact h₂

@[simp]
public theorem make_nil_is_empty {α β} [LT α] [DecidableLT α] :
  (Map.make [] : Map α β) = Map.empty
:= by simp [make, empty, List.canonicalize_nil]

/--
  Note that the converse of this is not true:
  counterexample `xs = [(1, false)]`, `ys = []`, `ab = (1, false)`.
-/
public theorem make_cons [LT α] [DecidableLT α] {xs ys : List (α × β)} {ab : α × β} :
  make xs = make ys → make (ab :: xs) = make (ab :: ys)
:= by
  simp only [make, mk.injEq]
  apply List.canonicalize_cons

@[simp]
public theorem make_of_make_is_id [LT α] [DecidableLT α] [StrictLT α] (xs : List (α × β)) :
  Map.make (Map.toList (Map.make xs)) = Map.make xs
:= by
  simp only [make, mk.injEq]
  have h₁ := List.canonicalize_idempotent Prod.fst xs
  unfold id at h₁
  exact h₁

/-! ### find?, findOrErr, and mapOnValues -/

@[simp]
public theorem find?_empty {α β} [DecidableEq α] (k : α) :
  (Map.empty : Map α β).find? k = none
:= by simp [Map.find?, Map.empty]

@[simp]
public theorem singleton_find? [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] (k : α) (v : β) :
  (Map.make [(k, v)]).find? k = .some v
:= by simp [Map.find?, Map.make_singleton, toList_mk_id]

@[simp]
public theorem singleton_contains  [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] (k k' : α) (v : β) :
  (Map.make [(k', v)]).contains k ↔ k' == k
:= by
  simp only [Map.make_singleton, Map.contains_iff_some_find?, Map.find?, toList_mk_id, List.find?_singleton, beq_iff_eq]
  split <;> rename_i h_eq
  · replace h_eq : k' = k :=
      Option.ite_none_right_eq_some.mp h_eq|>.left
    simp [h_eq]
  · replace h_eq : k' ≠ k := by
      simpa using h_eq
    simp [h_eq]

/-- `Map.find?` returns the value of the first entry with the key. -/
public theorem find?_eq_toList_find? {α β} [BEq α] (m : Map α β) (k : α) :
  m.find? k = (m.toList.find? (·.fst == k)).map Prod.snd
:= by
  cases hf : m.toList.find? (·.fst == k) <;> simp [Map.find?, hf]
/--
  Converse is available at `in_list_iff_find?_some` (requires `wf` though)

  Inverse is available at `find?_notmem_keys` (requires `wf` though)
-/
public theorem find?_mem_toList {α β} [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β}
  (h₁ : m.find? k = .some v) :
  (k, v) ∈ m.toList
:= by
  unfold toList find? at *
  split at h₁ <;> simp only [Option.some.injEq, reduceCtorEq] at h₁
  subst h₁
  rename_i h₂
  have h₃ := List.find?_some h₂
  simp only [beq_iff_eq] at h₃ ; subst h₃
  exact List.mem_of_find?_eq_some h₂

/--
  The `mpr` direction of this does not need the `wf` precondition and, in fact,
  is available separately as `find?_mem_toList` above
-/
public theorem in_list_iff_find?_some [DecidableEq α] [LT α] [DecidableLT α] [StrictLT α] {k : α} {v : β} {m : Map α β}
  (wf : m.WellFormed) :
  (k, v) ∈ m.toList ↔ m.find? k = some v
:= by
  unfold find?
  constructor
  case mp =>
    intro h₁
    cases h₂ : m.toList.find? λ x => match x with | (k', _) => k' == k
    case none =>
      exfalso
      rw [List.find?_eq_none] at h₂
      apply h₂ (k, v) h₁ ; clear h₂
      simp only [beq_self_eq_true]
    case some kv =>
      simp only [Option.some.injEq]
      have h₃ := List.find?_some h₂
      simp only [beq_iff_eq] at h₃
      subst h₃
      replace h₃ := List.mem_of_find?_eq_some h₂
      apply (key_maps_to_one_value kv.fst v kv.snd m wf h₁ _).symm
      trivial
  case mpr => exact find?_mem_toList

/-- Inverse of `find?_mem_toList`, except that this requires `wf` -/
public theorem find?_notmem_keys [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α}
  (wf : m.WellFormed) :
  m.find? k = none ↔ k ∉ m.keys
:= by
  unfold find? at *
  constructor <;> intro h₁
  case mp =>
    split at h₁ <;> simp at h₁
    rename_i h₂
    intro h₃
    replace ⟨v, h₃⟩ := in_keys_exists_value h₃
    apply h₂ k v ; clear h₂
    replace h₃ := (in_list_iff_find?_some wf).mp h₃
    unfold find? at h₃
    split at h₃ <;> simp only [Option.some.injEq, reduceCtorEq] at h₃
    · subst v ; rename_i k' v h₂
      simp only [h₂, Option.some.injEq, Prod.mk.injEq, and_true]
      simpa using List.find?_some h₂
  case mpr =>
    split <;> simp ; rename_i k' v h₂
    · apply h₁ ; clear h₁
      have h₃ := List.find?_some h₂ ; simp at h₃ ; subst k'
      replace h₂ := List.mem_of_find?_eq_some h₂
      exact in_list_in_keys h₂

/--
  Two well-formed maps are equal if they have the same `find?` for every key.
-/
public theorem find?_ext [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m₁ m₂ : Map α β}
  (wf₁ : m₁.WellFormed)
  (wf₂ : m₂.WellFormed)
  (h : ∀ k, m₁.find? k = m₂.find? k) :
  m₁ = m₂
:= by
  apply eq_iff_toList_equiv wf₁ wf₂ |>.mp
  constructor
  · intro ⟨k, v⟩ h₁
    have h₂ := (in_list_iff_find?_some wf₁).mp h₁
    rw [h] at h₂
    exact (in_list_iff_find?_some wf₂).mpr h₂
  · intro ⟨k, v⟩ h₁
    have h₂ := (in_list_iff_find?_some wf₂).mp h₁
    rw [← h] at h₂
    exact (in_list_iff_find?_some wf₁).mpr h₂

public theorem find?_none_all_absent [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} :
  m.find? k = none → ∀ v, ¬ (k, v) ∈ m.toList
:= by
  intro hn v
  false_or_by_contra ; rename_i hc
  simp only [find?] at hn
  cases hf : List.find? (fun x => x.fst == k) m.toList <;>
  simp only [hf, reduceCtorEq] at hn
  simp only [List.find?_eq_none, beq_iff_eq] at hf
  specialize hf (k, v) hc
  simp only [not_true_eq_false] at hf

public theorem in_list_implies_contains {α β}
  [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {m : Map α β} {k : α} {v : β} :
  (k, v) ∈ m.toList → m.contains k
:= by
  intros h
  cases hfind : m.find? k with
  | none =>
    have := find?_none_all_absent hfind v h
    contradiction
  | some =>
    apply contains_iff_some_find?.mpr
    simp [hfind]

public theorem all_absent_find?_none [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} :
  (∀ v, (k, v) ∉ m.toList) → m.find? k = none
:= by
  cases h₁ : m.toList
  case nil =>
    simp only [toList_nil_iff_empty] at h₁
    subst m
    simp
  case cons head tail =>
    intro hi
    have hm : m = Map.mk (head :: tail) := by
      rw [(by simp [Map.toList] : m = Map.mk m.toList), h₁]
    subst m
    simp only [List.mem_cons, not_or, ne_eq] at hi
    simp only [Map.find?, Map.toList, List.find?]
    have hh : head.fst ≠ k := by
      intro hh
      apply (hi head.snd).left
      simp [←hh]
    replace hh : (head.fst == k) = false := by
      simp [hh]
    simp only [hh]
    have hi₂ : ∀ v, (k, v) ∉ tail := by simp [hi]
    have ih := all_absent_find?_none hi₂
    simpa [Map.find?, Map.toList] using ih

public theorem find?_none_iff_all_absent [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} :
  m.find? k = none ↔ ∀ v, ¬ (k, v) ∈ m.toList
:= Iff.intro find?_none_all_absent all_absent_find?_none


public theorem list_find?_some_iff_map_find?_some {α β: Type} [BEq α] [LawfulBEq α] {l: List (α × β)} {k : α} {v : β} :
  l.find? (λ x => x.1 == k) = .some (k, v) ↔
  (Map.mk l).find? k = .some v
:= by
  constructor
  case mp =>
    intro h₁
    simp only [find?, toList_mk_id]
    split
    case h_1 k₂ v₂ h₂ =>
      rw [h₁] at h₂
      simp only [Option.some.injEq, Prod.mk.injEq] at h₂
      rcases h₂ with ⟨h₂, h₃⟩
      rw [h₃]
    case h_2 h₂ =>
      specialize h₂ k v
      simp only [imp_false] at h₂
      rw [h₁] at h₂
      contradiction
  case mpr =>
    intro h₁
    simp only [find?, toList_mk_id] at h₁
    split at h₁
    case h_1 k₂ v₂ h₂ =>
      rw [h₂]
      simp only [Option.some.injEq, Prod.mk.injEq]
      have h₃ := List.find?_some h₂
      simp at h₃
      injection h₁ ; rename_i h₁
      exact And.intro h₃ h₁
    case h_2 =>
      contradiction


public theorem list_find?_mapM_implies_exists_mapped {α β γ : Type} [BEq α] [LawfulBEq α] {ls : List (α × β)} (fn : β → Option γ) {ys: List (α × γ)} {k: α} {x : β} :
  List.mapM (fun x =>
              (fn x.2).bind
                (fun v => some (x.fst, v))) ls = some ys →
  ls.find? (λ x => x.1 == k) = .some (k, x) →
  ∃y, fn x = .some y ∧  ys.find? (λ x => x.1 == k) = .some (k, y)
:= by
  intro h₁ h₂
  rw [List.mapM_some_iff_forall₂] at h₁
  cases h₁
  case nil =>
    simp at h₂
  case cons hd₁ hd₂ tl₁ tl₂ h₃ h₄ =>
    simp [List.find?] at h₂
    split at h₂
    case h_1 x₂ h₅ =>
      injection h₂ ; rename_i h₂
      rw [h₂] at h₃
      simp at h₃
      cases h₆ : (fn x) <;> rw [h₆] at h₃
      case none =>
        simp at h₃
      case some y₂ =>
        simp at h₃
        rcases h₃ with ⟨h₃, h₇⟩
        exists y₂
        simp
    case h_2 x h₅ =>
      rw [← List.mapM_some_iff_forall₂] at h₄
      unfold List.find?
      have h₆ : (hd₂.fst == k) = false := by
        cases h₆ : (fn hd₁.snd) <;> rw [h₆] at h₃
        case none =>
          simp at h₃
        case some =>
          simp at h₃
          cases hd₂
          simp at h₅
          simp
          simp at h₃
          rcases h₃ with ⟨h₃, _⟩
          rw [← h₃]
          exact h₅
      rw [h₆]
      simp
      exact list_find?_mapM_implies_exists_mapped fn h₄ h₂


public theorem list_find?_mapM_implies_exists_unmapped {α β γ : Type} [BEq α] [LawfulBEq α] {ls : List (α × β)} (fn : β → Option γ) {ys: List (α × γ)} {k: α} {y: γ} :
  List.mapM (fun x =>
              (fn x.2).bind
                (fun v => some (x.fst, v))) ls = some ys →
  ys.find? (λ x => x.1 == k) = .some (k, y) →
  ∃ x, fn x = some y ∧ (ls.find? (λ x => x.1 == k) = .some (k, x))
:= by
  intro h₁ h₂
  rw [List.mapM_some_iff_forall₂] at h₁
  cases h₁
  case nil =>
    simp at h₂
  case cons hd₁ hd₂ tl₁ tl₂ h₃ h₄=>
    simp [List.find?] at h₂
    split at h₂
    case h_1 x h₅ =>
      injection h₂ ; rename_i h₂
      rw [h₂] at h₃
      cases h₆ : (fn hd₁.snd) <;> rw [h₆] at h₃
      case none =>
        simp at h₃
      case some y₂ =>
        simp at h₃
        rcases h₃ with ⟨h₃, h₇⟩
        exists hd₁.snd
        rw [h₆, h₇]
        simp
        rw [h₃]
        simp
        cases hd₁
        simp at h₃
        rw [h₃]
    case h_2 x h₅ =>
      rw [← List.mapM_some_iff_forall₂] at h₄
      unfold List.find?
      have h₆ : (hd₁.fst == k) = false := by
        cases h₆ : (fn hd₁.snd) <;> rw [h₆] at h₃
        case none =>
          simp at h₃
        case some =>
          simp at h₃
          cases hd₂
          simp at h₅
          simp
          simp at h₃
          rcases h₃ with ⟨h₃, _⟩
          rw [h₃]
          exact h₅
      rw [h₆]
      simp
      exact list_find?_mapM_implies_exists_unmapped fn h₄ h₂

public theorem find?_mapM_key_id {α β : Type} [BEq α] [LawfulBEq α] {ks : List α} {kvs : List (α × β)} {fn : α → Option β} {k: α}
  (h₁ : ks.mapM (λ k => do (k, ←fn k)) = some kvs)
  (h₂ : k ∈ ks) :
  (Map.mk kvs).find? k = fn k
:= by
  simp only [find?, toList_mk_id]
  cases h₂
  case head l =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h₁
    cases hf : fn k <;> simp only [hf, Option.bind_none, Option.bind_some, reduceCtorEq] at h₁
    cases ht₁ : (l.mapM (λ k => (fn k).bind λ v => some (k, v))) <;> simp [ht₁ , Option.bind_none, Option.bind_some, reduceCtorEq, Option.some.injEq] at h₁
    subst h₁
    simp
  case tail h t h₂  =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h₁
    cases hf : fn h <;> simp only [hf, Option.bind_none, Option.bind_some, reduceCtorEq] at h₁
    cases ht₁ : (t.mapM (λ k => (fn k).bind λ v => some (k, v))) <;> simp only [ht₁, Option.bind_none, Option.bind_some, reduceCtorEq, Option.some.injEq] at h₁
    subst h₁
    simp only [List.find?]
    cases h₃ : (h == k)
    · simp only
      exact find?_mapM_key_id ht₁ h₂
    · simp only [beq_iff_eq] at h₃
      simp [h₃, ←hf]

public theorem find?_filterMap_key_id {α β : Type} [BEq α] [LawfulBEq α] {ks : List α} {fn : α → Option β} {k: α}
  (h₂ : k ∈ ks) :
  (Map.mk (ks.filterMap (λ k => do (k, ←fn k)))).find? k = fn k
:= by
  simp only [find?, toList_mk_id]
  have h₃ := List.find?_filterMap_key_id (fn := fn) h₂
  simp only [Option.map] at h₃
  split at h₃
  all_goals
    rename_i h₄
    rw [h₄]
    exact h₃

public theorem filterMap_key_id_key_none_implies_find?_none {α β : Type} [DecidableEq α] [LT α] [StrictLT α] [DecidableLT α] {ks : List α} {fn : α → Option β} {k: α}
  (h₁ : fn k = none) :
  (Map.make (ks.filterMap (λ k => do some (k, ←fn k)))).find? k = none
:= by
  suffices h : (Map.mk (ks.filterMap (λ k => do some (k, ←fn k)))).find? k = none from by
    simp only [Map.find?_none_iff_all_absent] at ⊢ h
    intro v
    simp only [Map.make]
    exact mt List.in_canonicalize_in_list $ h v

  cases h₂ : decide (k ∈ ks)
  case false =>
    simp only [decide_eq_false_iff_not] at h₂
    simp only [find?, toList_mk_id]
    have h₃ : ∀ x ∈ ks, ¬Option.any (λ x => x.fst == k) (do some (x, ←fn x)) = true := by
      intro x hx₁
      simp only [Option.any, Bool.not_eq_true]
      cases fn x <;> simp only [Option.bind_none_fun, Option.bind_some_fun, beq_eq_false_iff_ne, ne_eq]
      intro hx₂
      rw [hx₂] at hx₁
      simp [hx₁] at h₂
    have h₄ := (@List.find?_eq_none _ (λ a => Option.any (λ x => x.fst == k) (do some (a, ←fn a))) ks).mpr h₃
    simp only [Option.bind_eq_bind] at h₄
    simp [h₄]
  case true =>
    simp only [decide_eq_true_eq] at h₂
    replace h₂ := find?_filterMap_key_id (fn := fn) h₂
    rw [h₂]
    exact h₁



theorem mapM_key_id_key_none_implies_find?_none {α β : Type} [DecidableEq α] [LT α] [StrictLT α] [DecidableLT α] {ks : List α} {kvs : List (α × β)} {fn : α → Option β} {k: α}
  (h₂ : ks.mapM (λ k => do (k, ←fn k)) = some kvs)
  (h₁ : fn k = none) :
  (Map.make kvs).find? k = none
:= by
  by_cases h₃ : k ∈ ks
  case pos =>
    have ⟨ _, _, h₄ ⟩ := List.mapM_some_implies_all_some h₂ k h₃
    simp [h₁] at h₄
  case neg =>
    simp only [Map.find?_none_iff_all_absent, Map.make]
    intro v hl'
    have h₄ := List.in_canonicalize_in_list hl'
    exact List.not_mem_implies_not_mem_mapM_key_id h₂ h₃ v h₄

public theorem mapOnValues_wf [DecidableEq α] [LT α] [DecidableLT α] [StrictLT α] {f : β → γ} {m : Map α β} :
  m.WellFormed ↔ (m.mapOnValues f).WellFormed
:= by
  simp only [wf_iff_sorted, toList]
  apply List.map_eq_implies_sortedBy
  simp only [mapOnValues, List.map_map]
  apply List.map_congr
  simp

@[simp]
public theorem mapOnValues_empty {α β γ} [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} :
  (empty : Map α β).mapOnValues f = empty
:= by
  simp [mapOnValues, empty]

public theorem mapOnValues_tail {f : β → γ} {hd₁ hd₂ : α × β} {tl₁ tl₂ : List (α × β)} :
  Map.mapOnValues f (Map.mk (hd₁ :: tl₁)) = Map.mapOnValues f (Map.mk (hd₂ :: tl₂)) →
  Map.mapOnValues f (Map.mk tl₁) = Map.mapOnValues f (Map.mk tl₂)
:= by
  simp [mapOnValues]

/--
Ideally we wouldn't need this, but it's currently necessary because of the kludgy way
that `EntityTag.mk` uses `Map` without relying on its proper constructors
-/
public theorem mapOnValues_doubleton {f : β → γ} {s₁ s₂ : String} (b₁ b₂ : β) :
  Map.mapOnValues f (Map.mk [(s₁, b₁), (s₂, b₂)]) = Map.mk [(s₁, f b₁), (s₂, f b₂)]
:= by simp [mapOnValues]

@[simp]
public theorem find?_mapOnValues {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) (m : Map α β) (k : α)  :
  (m.mapOnValues f).find? k = (m.find? k).map f
:= by
  simp only [find?, toList, mapOnValues, ← List.find?_pair_map]
  cases m.1.find? (λ x => x.fst == k) <;> simp only [Option.map_none, Option.map_some]

public theorem find?_mapOnValues_some {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} {v : β} :
  m.find? k = .some v →
  (m.mapOnValues f).find? k = .some (f v)
:= by
  intro h₁
  rw [find?_mapOnValues]
  simp [Option.map, h₁]

public theorem find?_mapOnValues_some' {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} {v : γ} :
  (m.mapOnValues f).find? k = .some v →
  (∃ v', m.find? k = .some v' ∧ v = f v')
:= by
  intro h
  simp only [find?, mapOnValues, toList_mk_id, List.find?_map] at h
  split at h <;> simp at h
  case _ heq =>
    subst h
    simp only [Option.map] at heq
    split at heq <;> simp at heq
    case _ y heq₁ =>
      exists y.snd
      have : ∀ x, ((fun x => x.fst == k) ∘ fun (x : α × β) => (x.fst, f x.snd)) x = (fun x => x.fst == k) x := by
        simp only [Function.comp_apply, implies_true]
      simp only [List.find?_compose (fun (x : α × β) => (x.fst, f x.snd)) (fun x => x.fst == k)
          (fun x => x.fst == k) this] at heq₁
      simp only [find?, heq₁, true_and]
      rcases heq with ⟨_, heq⟩
      subst heq
      rfl

@[simp]
public theorem find?_mapOnValues_none {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} :
  (m.mapOnValues f).find? k = .none ↔
  m.find? k = .none
:= by simp [find?_mapOnValues]

public theorem mapOnValues_eq_make_map {α β γ} [LT α] [StrictLT α] [DecidableLT α] (f : β → γ) {m : Map α β}
  (wf : m.WellFormed) :
  m.mapOnValues f = Map.make (m.toList.map λ kv => (kv.fst, f kv.snd))
:= by
  unfold WellFormed at wf
  simp only [make, toList, mapOnValues, mk.injEq] at *
  rw [wf] ; simp only ; rw [eq_comm]
  have h₁ : Prod.map id f = (λ (x : α × β) => (x.fst, f x.snd)) := by unfold Prod.map ; simp only [id_eq]
  simp only [← h₁, ← List.canonicalize_of_map_fst, List.canonicalize_idempotent]

public theorem mem_toList_find? {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β}
  (h₁ : m.WellFormed)
  (h₂ : (k, v) ∈ m.toList) :
  m.find? k = .some v
:= by
  rw [WellFormed, make] at h₁
  generalize hm : toList m = l
  rw [hm] at h₁ h₂
  subst h₁
  simp only [toList] at hm
  rw [hm]
  have hsrt := List.canonicalize_sortedBy Prod.fst l
  rw [hm] at hsrt
  have h := List.mem_of_sortedBy_implies_find? h₂ hsrt
  simp only at h
  simp [find?, h]

@[simp]
public theorem contains_mapOnValues {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} :
  Map.contains (Map.mapOnValues f m) k = Map.contains m k
:= by
  simp only [contains, Option.isSome]
  cases h : m.find? k
  · simp [(find?_mapOnValues_none f).mpr h]
  · simp [find?_mapOnValues_some f h]

@[simp]
public theorem keys_mapOnValues [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (f : β → γ) (m : Map α β) :
  (m.mapOnValues f).keys = m.keys
:= by
  simp [mapOnValues, keys]

@[simp]
public theorem values_mapOnValues [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} :
  (m.mapOnValues f).values = m.values.map f
:= by
  unfold mapOnValues values
  induction m.1 <;> simp

@[simp]
public theorem mapOnValues_mapOnValues [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {g : γ → φ} {m : Map α β} :
  (m.mapOnValues f).mapOnValues g = m.mapOnValues (g ∘ f)
:= by simp [mapOnValues]

/-- Like `List.map_congr`, but lifted to `Map.mapOnValues` -/
public theorem mapOnValues_congr {f g : β → γ} {m : Map α β} :
  (∀ v ∈ m.values, f v = g v) → m.mapOnValues f = m.mapOnValues g
:= by
  simp only [mapOnValues, mk.injEq, List.map_inj_left, Prod.mk.injEq, true_and, Prod.forall]
  intro h₁ a b h₂
  apply h₁ b (in_list_in_values h₂)

public theorem mapOnValues_restricted_id  {f : β → β} {m : Map α β} :
  (∀ b ∈ m.values, f b = b) →
  m.mapOnValues f = m
:= by
  simp only [mapOnValues]
  cases m ; simp only [toList_mk_id, mk.injEq]
  intro h
  apply List.map_restricted_id
  intro pair hpair
  simp [h pair.snd (Map.in_list_in_values hpair)]

@[simp]
public theorem mapOnValues_make [LT α] [DecidableLT α] [StrictLT α] {f : β → γ} {kvs : List (α × β)} :
  (Map.make kvs).mapOnValues f = Map.make (kvs.map (Prod.map id f))
:= by
  simp [make, mapOnValues, List.canonicalize_of_map_fst]

@[simp]
public theorem mapOnValues₂_eq_mapOnValues {α β γ} [SizeOf α] [SizeOf β] (m : Map α β) (f : β → γ) :
  m.mapOnValues₂ (λ x : { x : β // sizeOf x < sizeOf m } => f x.1) = m.mapOnValues f
:= by
  simp only [mapOnValues₂, mapOnValues, List.map₂_eq_map_snd f, toList]

/-- `findOrErr` cannot return any error other than `e` -/
public theorem findOrErr_returns [DecidableEq α] (m : Map α β) (k : α) (e : Error) :
  (∃ v, m.findOrErr k e = .ok v) ∨
  m.findOrErr k e = .error e
:= by
  unfold findOrErr
  cases m.find? k <;> simp

@[simp]
public theorem findOrErr_mapOnValues [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} {e : Error} :
  (m.mapOnValues f).findOrErr k e = (m.findOrErr k e).map f
:= by
  unfold findOrErr
  rw [find?_mapOnValues]
  cases m.find? k <;> simp [Except.map]

@[simp]
public theorem findOrErr_ok_iff_find?_some [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} {e : Error} :
  m.findOrErr k e = .ok v ↔ m.find? k = some v
:= by
  unfold findOrErr
  cases m.find? k <;> simp only [Except.ok.injEq, Option.some.injEq, reduceCtorEq]

@[simp]
public theorem findOrErr_err_iff_find?_none [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {e : Error} :
  m.findOrErr k e = .error e ↔ m.find? k = none
:= by
  unfold findOrErr
  cases m.find? k <;> simp only [reduceCtorEq]

/--
  The converse requires the `wf` precondition, and is available in
  `findOrErr_ok_iff_in_toList` below
-/
public theorem findOrErr_ok_implies_in_toList [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} {e : Error} :
  m.findOrErr k e = .ok v → (k, v) ∈ m.toList
:= by
  simp only [findOrErr_ok_iff_find?_some]
  exact find?_mem_toList

/--
  The `mp` direction of this does not need the `wf` precondition and, in fact,
  is available separately as `findOrErr_ok_implies_in_toList` above
-/
public theorem findOrErr_ok_iff_in_toList [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} {e : Error}
  (wf : m.WellFormed) :
  m.findOrErr k e = .ok v ↔ (k, v) ∈ m.toList
:= by
  constructor
  case mp => exact findOrErr_ok_implies_in_toList
  case mpr =>
    simp only [findOrErr_ok_iff_find?_some]
    exact (in_list_iff_find?_some wf).mp

/--
  The converse requires the `wf` precondition, and is available in
  `find?_some_iff_in_values` below
-/
public theorem find?_some_implies_in_values [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} :
  m.find? k = .some v → v ∈ m.values
:= by
  intro h₁
  simp [values]
  exists k
  exact find?_mem_toList h₁

/--
  The converse requires the `wf` precondition, and is available in
  `findOrErr_ok_iff_in_values` below
-/
public theorem findOrErr_ok_implies_in_values [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} {e : Error} :
  m.findOrErr k e = .ok v → v ∈ m.values
:= by
  simp only [findOrErr_ok_iff_find?_some]
  exact find?_some_implies_in_values

/--
  The `mp` direction of this does not need the `wf` precondition and, in fact,
  is available separately as `find?_some_implies_in_values` above
-/
public theorem find?_some_iff_in_values [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {v : β}
  (wf : m.WellFormed) :
  (∃ k, m.find? k = .some v) ↔ v ∈ m.values
:= by
  constructor
  case mp =>
    intro ⟨k, h₁⟩
    exact find?_some_implies_in_values h₁
  case mpr =>
    simp only [values, List.mem_map]
    intro h₁
    replace ⟨⟨k, v'⟩, ⟨h₁, h₂⟩⟩ := h₁
    simp only at h₂
    subst v'
    exists k
    simp [h₁, ← in_list_iff_find?_some wf]

/--
  The `mp` direction of this does not need the `wf` precondition and, in fact,
  is available separately as `findOrErr_ok_implies_in_values` above
-/
public theorem findOrErr_ok_iff_in_values [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {v : β} {e : Error}
  (wf : m.WellFormed) :
  (∃ k, m.findOrErr k e = .ok v) ↔ v ∈ m.values
:= by
  simp only [findOrErr_ok_iff_find?_some]
  exact find?_some_iff_in_values wf

public theorem findOrErr_err_iff_not_in_keys [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} {e : Error}
  (wf : m.WellFormed) :
  m.findOrErr k e = .error e ↔ k ∉ m.keys
:= by
  simp [findOrErr_err_iff_find?_none]
  exact find?_notmem_keys wf

/--
  The converse requires the extra precondition that `f` is injective, and is
  available as `in_mapOnValues_in_toList`
-/
public theorem in_toList_in_mapOnValues [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} {v : β} :
  (k, v) ∈ m.toList → (k, f v) ∈ (m.mapOnValues f).toList
:= by
  unfold mapOnValues
  intro h₁
  simp only [toList_mk_id, List.mem_map, Prod.mk.injEq, Prod.exists]
  exists k, v

/--
  TODO: This is redundant with `findOrErr_err_iff_find?_none`
-/
public theorem find?_none_iff_findorErr_errors [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} (e : Error) :
  m.find? k = none ↔ m.findOrErr k e = .error e
:= by
  exact findOrErr_err_iff_find?_none.symm

/--
  Converse of `in_toList_in_mapOnValues`; requires the extra precondition that `f` is injective
-/
public theorem in_mapOnValues_in_toList [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} {v : β} :
  (k, f v) ∈ (m.mapOnValues f).toList →
  (∀ v', f v = f v' → v = v') → -- require f to be injective
  (k, v) ∈ m.toList
:= by
  simp only [toList, mapOnValues, List.mem_map, Prod.mk.injEq, Prod.exists, forall_exists_index,
    and_imp]
  intro a b h₁ _ h₂ h_inj ; subst a
  specialize h_inj b h₂.symm
  subst h_inj
  exact h₁

/--
  Slightly different formulation of `in_mapOnValues_in_toList`
-/
public theorem in_mapOnValues_in_toList' [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} {v' : γ} :
  (k, v') ∈ (m.mapOnValues f).toList →
  ∃ v, f v = v' ∧ (k, v) ∈ m.toList
:= by
  simp only [mapOnValues, toList, List.mem_map, Prod.mk.injEq, Prod.exists,
    forall_exists_index, and_imp]
  intro a b h₁ _ _ ; subst a v'
  exists b

/-! ### mapMOnValues -/

public theorem mapMOnValues₂_eq_mapMOnValues {α β γ : Type 0} [LT α] [DecidableLT α] [SizeOf α] [SizeOf β] [Monad m] [LawfulMonad m] (map : Map α β) (f : β → m γ) :
  map.mapMOnValues₂ (λ x : { x : β // sizeOf x < sizeOf map } => f x.1) = map.mapMOnValues f
:= by
  simp only [mapMOnValues₂, mapMOnValues, List.mapM₂_eq_map_snd f, toList]

@[simp]
public theorem mapMOnValues_empty [LT α] [DecidableLT α] [Monad m] [LawfulMonad m] (f : β → m γ) :
  (empty : Map α β).mapMOnValues f = pure empty
:= by simp [mapMOnValues, empty]

@[simp]
public theorem mapMOnValues_mapOnValues [LT α] [DecidableLT α] [Monad m] [LawfulMonad m] (map : Map α β) (f : β → γ) (g : γ → m φ) :
  mapMOnValues g (map.mapOnValues f) = map.mapMOnValues (g ∘ f)
:= by
  simp only [mapMOnValues, mapOnValues, toList]
  congr 1
  rw [show (fun x : α × β => (x.fst, f x.snd)) = Prod.map id f from by ext ⟨a, b⟩ <;> rfl]
  rw [List.mapM_map]
  rfl

/-- Mapping every value to `some` preserves the map. -/
public theorem mapMOnValues_some {α β} [LT α] [DecidableLT α]
    (m : Map α β) :
    m.mapMOnValues some = some m := by
  cases m with
  | mk kvs =>
    simp only [Map.mapMOnValues, Map.toList_mk_id]
    change (kvs.mapM some).bind (fun kvs => some (Map.mk kvs)) = some (Map.mk kvs)
    rw [List.mapM_some]
    rfl

/-- Mapping map values succeeds exactly when every application succeeds. -/
public theorem mapMOnValues_isSome {α β γ} [LT α] [DecidableLT α]
    (m : Map α β) (f : β → Option γ) :
    (m.mapMOnValues f).isSome = m.values.all (fun value => (f value).isSome) := by
  cases m with
  | mk kvs =>
    let g := fun kv : α × β => (f kv.snd).bind fun value => some (kv.fst, value)
    change ((kvs.mapM g).bind fun values => some (Map.mk values)).isSome =
      (kvs.map Prod.snd).all (fun value => (f value).isSome)
    calc
      _ = (kvs.mapM g).isSome := by cases kvs.mapM g <;> rfl
      _ = kvs.all (fun kv => (g kv).isSome) := List.mapM_isSome
      _ = (kvs.map Prod.snd).all (fun value => (f value).isSome) := by
        induction kvs with
        | nil => rfl
        | cons kv rest ih =>
          simp only [List.all_cons, List.map_cons]
          cases hf : f kv.snd <;> simp [g, hf, ih]

/--
  This is not stated in terms of `Map.keys` because `Map.keys` produces a `Set`,
  and we want the even stronger property that it not only preserves the key-set,
  but also the key-order. (We'll use this to prove `mapMOnValues_some_wf`.)
-/
public theorem mapMOnValues_preserves_keys [LT α] [DecidableLT α] [StrictLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  m₁.toList.map Prod.fst = m₂.toList.map Prod.fst
:= by
  intro h₁
  simp only [mapMOnValues, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h₁
  replace ⟨xs, h₁, h₂⟩ := h₁
  subst h₂
  cases h₂ : m₁.toList <;> simp only [h₂, List.mapM_nil, List.mapM_cons, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
  case nil => simp [h₁]
  case cons kv tl =>
    have (k, v) := kv ; clear kv
    replace ⟨(k', y), ⟨y', h₁, h₃⟩, ⟨tl', h₄, h₅⟩⟩ := h₁
    subst h₅
    simp only [Prod.mk.injEq, List.map_cons, toList_mk_id, List.cons.injEq] at *
    replace ⟨h₃, h₃'⟩ := h₃
    subst k' y'
    have ih := mapMOnValues_preserves_keys (m₁ := mk tl) (m₂ := mk tl') (f := f)
    simp only [mapMOnValues, Option.pure_def, Option.bind_eq_bind, toList_mk_id,
      Option.bind_eq_some_iff, Option.some.injEq, mk.injEq, exists_eq_right] at ih
    specialize ih h₄
    simp [ih, and_self]

public theorem mapMOnValues_some_wf [LT α] [DecidableLT α] [StrictLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.WellFormed →
  (m₁.mapMOnValues f = some m₂) →
  m₂.WellFormed
:= by
  simp only [wf_iff_sorted, toList]
  intro wf h₁
  have h₂ := mapMOnValues_preserves_keys h₁
  exact (List.map_eq_implies_sortedBy h₂).mp wf

/--
  Alternate proof of `mapMOnValues_some_wf`, that relies on
  `List.mapM_some_eq_filterMap` instead of `mapMOnValues_preserves_keys`. Which do
  we prefer?
-/
theorem mapMOnValues_some_wf_alt_proof [LT α] [DecidableLT α] [StrictLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.WellFormed →
  (m₁.mapMOnValues f = some m₂) →
  m₂.WellFormed
:= by
  simp only [wf_iff_sorted, toList]
  intro wf h₁
  simp only [mapMOnValues, Option.pure_def, do_some] at h₁
  replace ⟨xs, h₁, h₂⟩ := h₁
  subst h₂
  simp only
  replace h₁ := List.mapM_some_eq_filterMap h₁
  subst h₁
  apply List.filterMap_sortedBy _ wf
  intro (k, v) (k', v') h₁
  simp only at *
  cases h₂ : f v <;> simp [h₂] at h₁
  exact h₁.left

public theorem mapMOnValues_ok_wf [LT α] [DecidableLT α] [StrictLT α] {f : β → Except ε γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.WellFormed →
  (m₁.mapMOnValues f = .ok m₂) →
  m₂.WellFormed
:= by
  simp only [wf_iff_sorted, toList]
  intro wf h₁
  simp [mapMOnValues, pure, Except.pure] at h₁
  cases h₂ : m₁.toList.mapM λ kv => do let v' ← f kv.snd ; .ok (kv.fst, v')
  <;> simp [h₂] at h₁
  case ok kv =>
    subst m₂
    simp only
    replace h₂ := List.mapM_ok_eq_filterMap h₂
    subst h₂
    apply List.filterMap_sortedBy _ wf
    intro (k, v) (k', v') h₁
    simp only at *
    cases h₂ : f v <;> simp [h₂] at h₁
    exact h₁.left

public theorem mapMOnValues_cons {α : Type 0} [LT α] [DecidableLT α] {f : β → Option γ} {m : Map α β} {k : α} {v : β} {tl : List (α × β)}:
  m.toList = (k, v) :: tl →
  (m.mapMOnValues f = do
    let v' ← f v
    let tl' ← (mk tl).mapMOnValues f
    return mk ((k, v') :: tl'.toList))
:= by
  intro h₁
  cases h₂ : f v <;> simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_none_fun, Option.bind_some_fun]
  case none => simp [h₁, h₂, mapMOnValues]
  case some v' =>
    cases h₃ : (mk tl).mapMOnValues f
    <;> simp only [Option.bind_none, Option.bind_some]
    <;> unfold mapMOnValues at *
    <;> simp only [h₁, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff,
          Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, List.mapM_cons]
    case none =>
      simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro kvs' v'' h₄ tl' h₅ h₆
      simp only [h₂, Option.some.injEq] at h₄
      subst v'' kvs'
      cases (tl.mapM λ x => match x with | (k, v) => do let v' ← f v ; pure (k, v'))
      <;> simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff, reduceCtorEq] at h₃
      <;> exact h₃ tl' h₅
    case some mtl' =>
      simp only [Option.pure_def, Option.bind_eq_bind, toList_mk_id, Option.bind_eq_some_iff,
        Option.some.injEq, Prod.exists, Prod.mk.injEq, exists_eq_right_right, mk.injEq,
        exists_eq_right, List.cons.injEq] at *
      exists k, v'
      simp only [h₂, and_self, and_true, true_and]
      replace ⟨tl', h₃, h₄⟩ := h₃
      subst mtl'
      simp [h₃]

theorem mapMOnValues_some_implies_forall₂ [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  List.Forall₂ (λ kv₁ kv₂ => kv₁.fst = kv₂.fst ∧ f kv₁.snd = some kv₂.snd) m₁.toList m₂.toList
:= by
  unfold mapMOnValues
  intro h₁
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
  replace ⟨x, h₁, h₂⟩ := h₁
  subst h₂
  replace h₁ := List.mapM_some_iff_forall₂.mp h₁
  apply List.Forall₂.imp _ h₁
  intro (k, v) (k', v') h₂
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq, exists_eq_right_right] at h₂
  replace ⟨h₂, h₂'⟩ := h₂
  subst k'
  simp only [true_and]
  exact h₂

/--
If a partial map of values succeeds, mapping a corresponding total function
produces the same map.
-/
public theorem mapOnValues_eq_of_mapMOnValues_some
    {α β γ} [LT α] [DecidableLT α]
    {m : Map α β} {out : Map α γ} {f : β → Option γ}
    (g : β → γ)
    (hmap : m.mapMOnValues f = some out)
    (hfg : ∀ input output, f input = some output → g input = output) :
    m.mapOnValues g = out := by
  cases m with
  | mk inputs =>
    change (do
      let values ← inputs.mapM (fun kv =>
        (f kv.snd).bind fun value => some (kv.fst, value))
      some (Map.mk values)) = some out at hmap
    cases hm : inputs.mapM (fun kv =>
        (f kv.snd).bind fun value => some (kv.fst, value)) with
    | none => simp [hm] at hmap
    | some values =>
      simp only [hm, Option.bind_some_fun, Option.some.injEq] at hmap
      subst out
      have hrel := List.mapM_some_iff_forall₂.mp hm
      apply Map.eq_iff_toList_eq.mp
      simp only [Map.mapOnValues, Map.toList_mk_id]
      induction hrel with
      | nil => rfl
      | @cons input output inputs outputs hhead hrest ih =>
        cases input with
        | mk key value =>
          cases output with
          | mk outputKey outputValue =>
            cases hf : f value with
            | none => simp [hf] at hhead
            | some mapped =>
              simp only [hf] at hhead
              obtain ⟨rfl, rfl⟩ := hhead
              simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, true_and]
              constructor
              · exact hfg value outputValue hf
              · apply ih
                exact List.mapM_some_iff_forall₂.mpr hrest

public theorem mapMOnValues_some_implies_all_some {α : Type 0} [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  ∀ kv ∈ m₁.toList, ∃ v, (kv.fst, v) ∈ m₂.toList ∧ f kv.snd = some v
:= by
  intro h₁
  replace h₁ := List.forall₂_implies_all_left (mapMOnValues_some_implies_forall₂ h₁)
  intro (k, v) h₂
  replace ⟨(k', v'), h₁, h₃, h₄⟩ := h₁ (k, v) h₂
  simp only at *
  subst k'
  exists v'

/--
  alternate proof of `mapMOnValues_some_implies_all_some`, which instead of
  relying on `mapMOnValues_some_implies_forall₂`, relies on
  `List.mapM_some_implies_all_some`.  Which do we prefer?
-/
theorem mapMOnValues_some_implies_all_some_alt_proof [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  ∀ kv ∈ m₁.toList, ∃ v, (kv.fst, v) ∈ m₂.toList ∧ f kv.snd = some v
:= by
  unfold mapMOnValues
  intro h₁ kv h₂
  cases h₃ : m₁.toList.mapM (λ x => match x with | (k, v) => do let v' ← f v ; pure (k, v'))
  <;> rw [h₃] at h₁
  <;> simp only [Option.pure_def, Option.bind_some_fun, Option.bind_none_fun, Option.some.injEq, reduceCtorEq] at h₁
  case some ags =>
    subst h₁
    have (a, b) := kv ; clear kv
    simp only
    replace h₃ := List.mapM_some_implies_all_some h₃
    replace ⟨(a', g), h₃, h₄⟩ := h₃ (a, b) h₂
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq, exists_eq_right_right] at h₄
    replace ⟨h₄, h₄'⟩ := h₄
    subst a'
    exists g

public theorem mapMOnValues_some_implies_all_from_some [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  ∀ kv ∈ m₂.toList, ∃ v, (kv.fst, v) ∈ m₁.toList ∧ f v = kv.snd
:= by
  intro h₁
  replace h₁ := List.forall₂_implies_all_right (mapMOnValues_some_implies_forall₂ h₁)
  intro (k, v) h₂
  replace ⟨(k', v'), h₁, h₃, h₄⟩ := h₁ (k, v) h₂
  simp only at *
  subst k'
  exists v'

/--
  alternate proof of `mapMOnValues_some_implies_all_from_some`, which instead of
  relying on `mapMOnValues_some_implies_forall₂`, relies on
  `List.mapM_some_implies_all_from_some`. Which do we prefer?
-/
theorem mapMOnValues_some_implies_all_from_some_alt_proof [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  ∀ kv ∈ m₂.toList, ∃ v, (kv.fst, v) ∈ m₁.toList ∧ f v = kv.snd
:= by
  unfold mapMOnValues
  intro h₁ kv h₂
  cases h₃ : m₁.toList.mapM (λ x => match x with | (k, v) => do let v' ← f v ; pure (k, v'))
  <;> rw [h₃] at h₁
  <;> simp only [Option.pure_def, Option.bind_some_fun, Option.bind_none_fun, Option.some.injEq, reduceCtorEq] at h₁
  case some ags =>
    subst h₁
    have (a, g) := kv ; clear kv
    simp only
    replace h₃ := List.mapM_some_implies_all_from_some h₃
    replace ⟨(a', b), h₃, h₄⟩ := h₃ (a, g) h₂
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq, exists_eq_right_right] at h₄
    replace ⟨h₄, h₄'⟩ := h₄
    subst a'
    exists b

public theorem mapMOnValues_none_iff_exists_none {α : Type 0} [LT α] [DecidableLT α] {f : β → Option γ} {m : Map α β} :
  m.mapMOnValues f = none ↔ ∃ v ∈ m.values, f v = none
:= by
  constructor
  case mp =>
    intro h₁
    cases h₂ : m.toList
    case nil =>
      rw [toList_nil_iff_empty] at h₂ ; subst h₂
      simp at h₁
    case cons hd tl =>
      have (khd, vhd) := hd ; clear hd
      simp only [values_cons h₂, List.mem_cons, exists_eq_or_imp]
      simp only [mapMOnValues_cons h₂, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_none_iff, reduceCtorEq] at h₁
      cases h₃ : f vhd
      case none => simp only [true_or]
      case some yhd =>
        right
        specialize h₁ yhd h₃
        have := sizeOf_lt_of_tl h₂ -- required for Lean to allow the following recursive call
        apply mapMOnValues_none_iff_exists_none.mp
        false_or_by_contra ; rename_i h₄
        rw [← ne_eq] at h₄
        replace ⟨ytl, h₄⟩ := Option.ne_none_iff_exists'.mp h₄
        exact h₁ ytl h₄
  case mpr =>
    intro h₁
    replace ⟨v, h₁, h₂⟩ := h₁
    cases h₃ : m.toList
    case nil =>
      rw [toList_nil_iff_empty] at h₃ ; subst h₃
      simp [values, empty] at h₁
    case cons hd tl =>
      have (khd, vhd) := hd ; clear hd
      simp only [values_cons h₃, List.mem_cons] at h₁
      simp only [mapMOnValues_cons h₃, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff]
      intro yhd h₄ ytl h₅
      rcases h₁ with h₁ | h₁
      · subst h₁ ; simp [h₂] at h₄
      · replace h₅ := mapMOnValues_some_implies_all_some h₅
        replace ⟨k', h₁⟩ := in_values_exists_key h₁
        replace ⟨y, _, h₅⟩ := h₅ (k', v) h₁
        simp [h₂] at h₅
termination_by m

/--
  Note that the converse is not true:
  counterexample `m₁` is `[(1, false)]`, `m₂` is `[(1, false), (2, true)]`, `f` is `Except.ok`

  But for a limited converse, see `all_ok_implies_mapMOnValues_ok`
-/
public theorem mapMOnValues_ok_implies_all_ok [LT α] [DecidableLT α] {f : β → Except ε γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = .ok m₂ →
  ∀ kv ∈ m₁.toList, ∃ v, (kv.fst, v) ∈ m₂.toList ∧ f kv.snd = .ok v
:= by
  unfold mapMOnValues
  intro h₁ kv h₂
  cases h₃ : m₁.toList.mapM λ kv => match kv with | (k, v) => do let v' ← f v ; pure (k, v')
  <;> rw [h₃] at h₁
  <;> simp only [pure, Except.pure, Except.bind_ok, Except.bind_err, Except.ok.injEq, reduceCtorEq] at h₁
  case ok ags =>
    subst h₁
    have (a, b) := kv ; clear kv
    simp only
    replace ⟨(a', g), h₃, h₄⟩ := List.mapM_ok_implies_all_ok h₃ (a, b) h₂
    simp [pure, Except.pure] at h₄
    cases h₅ : f b <;> simp [h₅] at h₄
    replace ⟨h₄, h₄'⟩ := h₄ ; subst a' g ; rename_i g
    exists g

public theorem mapMOnValues_ok_implies_all_from_ok [LT α] [DecidableLT α] {f : β → Except ε γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = .ok m₂ →
  ∀ kv ∈ m₂.toList, ∃ v, (kv.fst, v) ∈ m₁.toList ∧ f v = .ok kv.snd
:= by
  unfold mapMOnValues
  intro h₁ kv h₂
  cases h₃ : m₁.toList.mapM λ kv => match kv with | (k, v) => do let v' ← f v ; pure (k, v')
  <;> rw [h₃] at h₁
  <;> simp only [pure, Except.pure, Except.bind_ok, Except.bind_err, Except.ok.injEq, reduceCtorEq] at h₁
  case ok ags =>
    subst h₁
    have (a, g) := kv ; clear kv
    simp only
    replace ⟨(a', b), h₃, h₄⟩ := List.mapM_ok_implies_all_from_ok h₃ (a, g) h₂
    simp [pure, Except.pure] at h₄
    cases h₅ : f b <;> simp [h₅] at h₄
    replace ⟨h₄, h₄'⟩ := h₄ ; subst a' g ; rename_i g
    exists b

public theorem all_ok_implies_mapMOnValues_ok [LT α] [DecidableLT α] {f : β → Except ε γ} {m₁ : Map α β} :
  (∀ kv ∈ m₁.toList, ∃ v, f kv.snd = .ok v) →
  ∃ m₂, m₁.mapMOnValues f = .ok m₂
:= by
  unfold mapMOnValues
  intro h₁
  cases h₂ : m₁.toList.mapM λ kv => match kv with | (k, v) => do let v' ← f v ; pure (k, v')
  case ok ags => simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq, exists_eq']
  case error e =>
    exfalso
    replace ⟨(k, v), hkv, h₂⟩ := List.mapM_error_implies_exists_error h₂
    split at h₂ ; rename_i h₂' ; simp only [pure, Except.pure] at h₂
    simp only [Prod.mk.injEq] at h₂' ; replace ⟨h₂', h₂''⟩ := h₂' ; subst k v ; rename_i k v
    replace ⟨v', h₁⟩ := h₁ (k, v) hkv
    simp only [h₁, Except.bind_ok, reduceCtorEq] at h₂

public theorem mapMOnValues_error_implies_exists_error [LT α] [DecidableLT α] {f : β → Except ε γ} {m : Map α β} {e : ε} :
  m.mapMOnValues f = .error e → ∃ v ∈ m.values, f v = .error e
:= by
  simp only [mapMOnValues, pure, Except.pure]
  intro h₁
  rw [do_error] at h₁
  replace ⟨(k, v), hkv, h₁⟩ := List.mapM_error_implies_exists_error h₁
  rw [do_error] at h₁
  have h_values := in_list_in_values hkv
  exists v

public theorem wellFormed_correct {α β} [LT α] [StrictLT α] [DecidableLT α] {m : Map α β} :
  m.wellFormed = true ↔ m.WellFormed
:= by
  constructor
  · intros h
    apply wf_iff_sorted.mpr
    apply List.isSortedBy_correct.mpr
    exact h
  · intros h
    apply List.isSortedBy_correct.mp
    apply wf_iff_sorted.mp
    exact h


/--
Helper for make_find?_eq_list_find?
-/
private theorem map_make_find?_in_tail
  [LT α] [StrictLT α] [BEq α] [LawfulBEq α]
  [DecidableLT α]
  [SizeOf α] [SizeOf β]
  {hd : (α × β)} {tl : List (α × β)} {k : α} :
  ¬(hd.1 = k) →
  (Map.make (hd :: tl)).find? k = (Map.make tl).find? k := by
  simp [Map.make]
  intro h
  simp only [Map.find?, Map.toList_mk_id]
  have hp : (Prod.fst hd == k) = false := by simp [h]
  rw [List.list_find?_in_tail (f := Prod.fst) (k := k) hp]


public theorem make_find?_eq_list_find?
  [DecidableEq α] [LT α] [DecidableLT α]
  [Cedar.Data.StrictLT α]
  {l : List (α × β)}
  {k : α} :
  (make l).find? k = (List.find? (λ x => x.fst == k) l).map Prod.snd := by
  simp [Map.make]
  simp only [Map.find?, Map.toList_mk_id]
  induction l
  case nil =>
    simp only [List.canonicalize_nil, List.find?_nil, Option.map_none]
  case cons hd tl ih =>
    cases h : hd.fst == k
    case true =>
      rw [List.list_find?_at_head (f := Prod.fst) (k := k) h]
      simp only [List.find?, h, Option.map_some]
    case false =>
      rw [List.list_find?_in_tail (f := Prod.fst) (k := k) h]
      simp only [List.find?, h]
      exact ih

/-- Rebuilding a map from its entries with key-dependent values. -/
public theorem make_toList_map_find? {α β γ}
  [DecidableEq α] [LT α] [DecidableLT α] [StrictLT α]
  (m : Map α β) (g : α → β → γ) (k : α) :
  (Map.make (m.toList.map fun kv => (kv.fst, g kv.fst kv.snd))).find? k =
    (m.find? k).map (g k)
:= by
  rw [make_find?_eq_list_find?, List.find?_map, find?_eq_toList_find?]
  cases hf : m.toList.find? (·.fst == k) with
  | none => simp [hf, Function.comp_def]
  | some kv =>
    have hk : kv.fst = k := by simpa using List.find?_some hf
    simp [hf, hk, Function.comp_def]


public theorem list_find?_iff_make_find?
  [DecidableEq α] [LT α] [DecidableLT α]
  [Cedar.Data.StrictLT α]
  {l : List (α × β)}
  {k : α} {v : β} :
  List.find? (λ x => x.fst == k) l = some (k, v) ↔
  (make l).find? k = some v := by
  rw [make_find?_eq_list_find?]
  simp
  constructor
  case mp =>
    intro h
    exists k
  case mpr =>
    intro h
    replace ⟨k₂, h⟩ := h
    have h₂ := List.find?_some h
    simp at h₂
    rw [h₂] at h
    exact h

public theorem list_find?_iff_mk_find?
  [DecidableEq α] [LT α] [DecidableLT α]
  [Cedar.Data.StrictLT α]
  {l : List (α × β)}
  {k : α} {v : β} :
  List.find? (λ x => x.fst == k) l = some (k, v) ↔
  (mk l).find? k = some v := by
  constructor
  case mp =>
    intro h₁
    simp only [find?, toList_mk_id]
    rw [h₁]
  case mpr =>
    intro h₁
    simp only [find?, toList_mk_id] at h₁
    split at h₁
    case h_1 k₂ v₂ h₂ =>
      injection h₁ ; rename_i h₁
      have h₃ := List.find?_some h₂
      simp at h₃
      rw [h₁, h₃] at h₂
      exact h₂
    case h_2 =>
      contradiction

/--
If a key exists in `l₂` but not in `l₁`,
then `Map.make (l₁ ++ l₂)` contains that key.
-/
public theorem map_make_append_find_disjoint
  [LT α] [StrictLT α] [DecidableEq α] [DecidableLT α]
  [SizeOf α] [SizeOf β]
  {l₁ : List (α × β)} {l₂ : List (α × β)} {k : α}
  (hfind₁ : l₁.find? (λ ⟨k', _⟩ => k' == k) = none)
  (hfind₂ : (l₂.find? (λ ⟨k', _⟩ => k' == k)).isSome) :
  ∃ v,
    (Map.make (l₁ ++ l₂)).find? k = some v ∧
    (k, v) ∈ l₂
:= by
  have hwf : (Map.make (l₁ ++ l₂)).WellFormed := by
    exact Map.make_wf _
  have hsub :
    (Map.make (l₁ ++ l₂)).toList ⊆ l₁ ++ l₂
  := by
    apply List.canonicalize_subseteq
  simp [Subset, List.Subset] at hsub
  have ⟨v, hv⟩ :
    ∃ v, (Map.make (l₁ ++ l₂)).find? k = some v
  := by
    simp only [Option.isSome] at hfind₂
    split at hfind₂
    rotate_left
    contradiction
    rename_i kv hkv
    exists kv.snd
    rw [make_find?_eq_list_find?]
    rw [List.find?_append]
    rw [hkv, hfind₁]
    simp
  simp only [hv, Option.some.injEq, exists_eq_left']
  have := Map.find?_mem_toList hv
  have := hsub k v this
  cases this with
  | inl hmem₁ =>
    have := List.find?_eq_none.mp hfind₁
    specialize this (k, v) hmem₁
    simp at this
  | inr h => exact h

public theorem make_map_values_find
  [DecidableEq α] [LT α] [DecidableLT α]
  [Cedar.Data.StrictLT α]
  {l : List α}
  {f : α → β}
  {k : α}
  (hfind : k ∈ l) :
  (Map.make (l.map (λ x => (x, f x)))).find? k =
  .some (f k)
:= by
  rw [make_find?_eq_list_find?]
  simp only [List.find?_map, Option.map_eq_some_iff]
  unfold Function.comp
  simp
  exists k
  exists k
  simp
  rw [List.find?_exact_iff_mem.mpr hfind]

public theorem map_toList_findSome?
  [BEq α] [LawfulBEq α]
  {m : Map α β} {k : α} {v : β} {v' : γ}
  {f : α × β → Option γ}
  (hfind : Map.find? m k = .some v)
  (hf : ∀ kv, (∃ v', f kv = .some v') → kv.1 = k)
  (hkv : f (k, v) = .some v') :
  m.toList.findSome? f = .some v'
:= by
  cases m with | mk m =>
  simp only [find?, toList_mk_id] at hfind ⊢
  split at hfind
  · rename_i heq
    simp only [Option.some.injEq] at hfind
    simp [hfind] at heq
    induction m with
    | nil => contradiction
    | cons hd tl ih =>
      simp only [List.findSome?]
      simp only [List.find?] at heq
      split
      · rename_i fhd heq'
        split at heq
        · rename_i heq''
          simp only [Option.some.injEq] at heq
          simp only [beq_iff_eq, heq] at heq''
          simp only [heq''] at heq
          simp only [heq] at heq'
          simp only [heq'] at hkv
          simp [hkv]
        · rename_i heq''
          simp only [beq_eq_false_iff_ne, ne_eq] at heq''
          apply False.elim
          apply heq''
          apply hf
          exists fhd
      · split at heq
        · rename_i h₁ _ h₂
          simp only [beq_iff_eq] at h₂
          simp only [Option.some.injEq] at heq
          simp only [heq] at h₂
          simp only [h₂] at heq
          simp only [heq] at h₁
          simp only [hkv] at h₁
          contradiction
        · exact ih heq
  · contradiction

public theorem map_find?_to_list_find?
  [BEq α] [LawfulBEq α]
  {m : Map α β} {k : α} {v : β}
  (hfind : Map.find? m k = .some v) :
  List.find? (λ x => x.fst == k) (Map.toList m) = .some (k, v)
:= by
  simp only [Map.find?] at hfind
  split at hfind
  · rename_i heq
    simp only [Option.some.injEq] at hfind
    simp only [heq, hfind]
    have := List.find?_some heq
    simp only [beq_iff_eq] at this
    simp [this]
  · contradiction

/-- A variant of `map_make_append_find_disjoint`. -/
public theorem map_make_append_find_disjoint'
  [LT α] [StrictLT α] [DecidableEq α] [DecidableLT α]
  [SizeOf α] [SizeOf β]
  {l₁ : List (α × β)} {l₂ : List (α × β)} {k : α} {v : β}
  (hfind₁ : l₁.find? (λ ⟨k', _⟩ => k' == k) = none)
  (hfind₂ : l₂.find? (λ ⟨k', _⟩ => k' == k) = .some (k, v))
  (heq : ∀ x₁ x₂, x₁ ∈ l₂ → x₂ ∈ l₂ → x₁.fst = x₂.fst → x₁ = x₂) :
  (Map.make (l₁ ++ l₂)).find? k = some v
:= by
  have : (l₂.find? (λ ⟨k', _⟩ => k' == k)).isSome
  := by simp only [hfind₂, Option.isSome]
  have ⟨v', hfind_k, hmem⟩ := map_make_append_find_disjoint hfind₁ this
  have := List.mem_of_find?_eq_some hfind₂
  have := heq _ _ this hmem
  simp only [Prod.mk.injEq, true_and, forall_const] at this
  simp only [this, hfind_k]

public theorem map_find?_implies_find?_weaker_pred
  [BEq α] [LawfulBEq α]
  {m : Map α β} {k : α} {v : β} {f : α × β → Bool}
  (hfind : Map.find? m k = .some v)
  (hf : ∀ kv, f kv → kv.1 = k)
  (hkv : f (k, v)) :
  List.find? f (Map.toList m) = .some (k, v)
:= by
  replace hfind := map_find?_to_list_find? hfind
  cases m with | mk m =>
  simp only [toList_mk_id] at hfind ⊢
  induction m with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.find?]
    split
    · rename_i heq
      have := hf hd heq
      simp only [List.find?, this, BEq.rfl, Option.some.injEq] at hfind
      simp [hfind]
    · rename_i heq
      apply ih
      simp only [List.find?] at hfind
      split at hfind
      · simp only [Option.some.injEq] at hfind
        simp only [←hfind] at hkv
        simp [hkv] at heq
      · exact hfind

public theorem map_keys_empty_implies_map_empty
  {m : Map α β}
  (h : m.keys.toList = []) :
  m = Map.empty
:= by
  cases m with | mk m =>
  cases m with
  | nil => rfl
  | cons hd tl =>
    simp only [Map.keys, Set.toList, Set.elts] at h
    contradiction

/-- TODO: This is redundant with `eq_iff_toList_eq` -/
public theorem toList_congr
  {m₁ m₂ : Map α β}
  (h : m₁.toList = m₂.toList) :
  m₁ = m₂
:= by
  exact eq_iff_toList_eq.mp h

@[simp]
public theorem find?_append
  [LT α] [StrictLT α] [DecidableEq α] [DecidableLT α]
  {m₁ m₂ : Map α β} {k : α}:
  (m₁ ++ m₂).find? k = (m₁.find? k).or (m₂.find? k)
:= by
  have h_append_eq : (m₁ ++ m₂).find? k = (Map.make (m₁.toList ++ m₂.toList)).find? k := by
    rfl
  rw [h_append_eq]
  rw [make_find?_eq_list_find?]
  rw [List.find?_append]
  simp [Map.find?, Option.map, Option.or]
  cases List.find? (fun x => x.fst == k) m₁.toList
  . simp
    cases List.find? (fun x => x.fst == k) m₂.toList <;> simp
  . simp

@[simp]
public theorem contains_append
  [LT α] [StrictLT α] [DecidableLT α][DecidableEq α] {m₁ m₂ : Map α β} {k : α} :
  (m₁ ++ m₂).contains k ↔ m₁.contains k ∨ m₂.contains k
:= by
  have h₁ := Map.find?_append (m₁ := m₁) (m₂ := m₂) (k := k)
  simp only [Option.or] at h₁
  simp only [Map.contains]
  split at h₁
  all_goals
    rename_i h₂
    simp [h₁, h₂]

public theorem find?_append_right
  [LT α] [StrictLT α] [DecidableEq α] [DecidableLT α]
  {m₁ m₂ : Map α β} {k : α} :
  m₁.contains k = false → (m₁ ++ m₂).find? k = m₂.find? k
:= by
  rw [Map.find?_append]
  intro h₁
  replace h₁ : m₁.find? k = none := by
    simpa [Map.contains] using h₁
  simp [h₁]

public theorem find?_append_left
  [LT α] [StrictLT α] [DecidableEq α] [DecidableLT α]
  {m₁ m₂ : Map α β} {k : α} :
  m₂.contains k = false → (m₁ ++ m₂).find? k = m₁.find? k
:= by
  rw [Map.find?_append]
  intro h₁
  replace h₁ : m₂.find? k = none := by
    simpa [Map.contains] using h₁
  simp [h₁]

public theorem filter_wf [LT α] [DecidableLT α] [StrictLT α] (p : α → β → Bool) (m : Map α β) :
  WellFormed m →
  WellFormed (m.filter p)
:= by
  intro h
  exact wf_iff_sorted.mpr (List.filter_sortedBy _ (wf_iff_sorted.mp h))

public theorem find?_filter_if_find? {α : Type u} {β : Type v} [BEq α] [LawfulBEq α]
  {k : α} {val : β} {m : Map α β} {p : α → β → Bool} :
  m.find? k = some val → p k val = true →
  ((m.filter p).find? k = some val)
:= by
  simp only [Map.find?, Map.filter]
  intro h₁ h₂
  split at h₁
  · rename_i k' v' h₃
    injection h₁ with h₁; subst h₁
    have hk : k' = k := by
      simpa using List.find?_some h₃
    subst hk
    have h₄ := List.find?_filter_if_find? p h₃ h₂
    cases h₅ : List.find? (fun x => x.fst == k') (m.toList.filter (fun kv => p kv.fst kv.snd))
    case none =>
      replace h₅ : (k', v') ∈ m.toList → p k' v' = true → k' ≠ k' := by
        simp only [List.find?_filter, beq_iff_eq, Bool.decide_and, Bool.decide_eq_true, List.find?_eq_none, Bool.and_eq_true, not_and, Prod.forall] at h₅
        exact h₅ k' v'
      simp only [List.find?_filter] at h₄
      have h_mem_kv : (k', v') ∈ m.toList :=
        List.mem_of_find?_eq_some h₄
      have h_p_kv : p k' v' = true := by
        simpa using List.find?_some h₄
      specialize h₅ h_mem_kv h_p_kv
      contradiction
    case some kv =>
      have : kv = (k', v') := by
        have := h₄
        rw [h₅] at this
        injection this
      simp_all
  · contradiction

public theorem find?_filter_iff_find {α : Type u} {β : Type v} [BEq α] [LawfulBEq α] [DecidableEq α] [LT α] [StrictLT α] [DecidableLT α]
  {k : α} {val : β} {m : Map α β} {p : α → β → Bool} :
  m.WellFormed →
  ((m.find? k = some val ∧ p k val = true) ↔ ((m.filter p).find? k = some val))
:= by
  intro h_wf
  constructor
  · simp only [and_imp]
    exact Map.find?_filter_if_find?
  · simp only [Map.find?, Map.filter]
    intro h₁
    split at h₁ <;> try contradiction
    rename_i k' v' h₂
    injection h₁ with h₁ ; subst h₁
    have hk : k' = k := by
      simpa using List.find?_some h₂
    subst hk
    have h_sorted := Map.wf_iff_sorted.mp h_wf
    have h_find_toList := List.find?_filter_sorted k' v' m.toList p h_sorted h₂
    simp [h_find_toList]

public theorem filter_contains_if_find_matching {α : Type u} {β : Type v} [BEq α] [LawfulBEq α]
  {k : α} {m : Map α β} {p : α → β → Bool} :
  (∃ v, m.find? k = some v ∧ p k v = true) → (m.filter p).contains k
:= by
  intro ⟨v, hfind, hpred⟩
  rw [Map.contains_iff_some_find?]
  exists v
  exact Map.find?_filter_if_find? hfind hpred

public theorem find_matching_iff_filter_contains {α : Type u} {β : Type v} [BEq α] [LawfulBEq α] [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {k : α} {m : Map α β} (p : α → β → Bool) :
  m.WellFormed →
  ((∃ v, m.find? k = some v ∧ p k v = true) ↔ (m.filter p).contains k)
:= by
  intro h_wf
  have h_find? := λ v =>
    Map.find?_filter_iff_find (p := p) (val := v) (k := k) h_wf
  simp [Map.contains_iff_some_find?, h_find?]

public theorem filter_not_contains {α : Type u} {β : Type v} [BEq α] [LawfulBEq α] (k : α) (m : Map α β) :
  (m.filter (λ k' _ => k' != k)|>.contains k) = false
:= by
  have h_none : List.find? (λ _ => false) m.toList = none := by simp [List.find?_eq_none]
  simp [h_none, Map.contains, Map.find?, Map.filter]

end Cedar.Data.Map
