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

/-!
# Paths along a relation

Facts about `Relation.TransGen`, and about walks: paths that record the vertex
each of their edges leaves from.

They live in `Cedar.Relation` rather than `Relation`, like the Mathlib copies in
`Cedar.List`, so that a file can import both Cedar and Mathlib.
-/

namespace Cedar.Relation

/-- A path starts with an edge. -/
public theorem transGen_head {α} {r : α → α → Prop} {a b : α}
  (h : Relation.TransGen r a b) : ∃ c, r a c
:= by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

/-- A path ends with an edge. -/
public theorem transGen_tail {α} {r : α → α → Prop} {a b : α}
  (h : Relation.TransGen r a b) : ∃ c, r c b
:= by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

/-- A path stays a path along a larger relation. -/
public theorem transGen_mono {α} {r s : α → α → Prop} (hrs : ∀ a b, r a b → s a b)
  {a b : α} (h : Relation.TransGen r a b) : Relation.TransGen s a b
:= by
  induction h with
  | single h => exact .single (hrs _ _ h)
  | tail _ h ih => exact .tail ih (hrs _ _ h)

/-- A path along `edge` from `x` to `y` whose edges leave from `srcs`, in order. -/
public inductive Walk {α} (edge : α → α → Prop) : α → α → List α → Prop
  | single {x y} : edge x y → Walk edge x y [x]
  | cons {x z y srcs} : edge x z → Walk edge z y srcs → Walk edge x y (x :: srcs)

/-- Walks compose. -/
public theorem Walk.append {α} {edge : α → α → Prop} {x y z : α} {s₁ s₂ : List α}
  (h₁ : Walk edge x y s₁) (h₂ : Walk edge y z s₂) : Walk edge x z (s₁ ++ s₂)
:= by
  induction h₁ with
  | single h => exact .cons h h₂
  | cons h _ ih => exact .cons h (ih h₂)

/-- Every path is a walk. -/
public theorem Walk.of_transGen {α} {edge : α → α → Prop} {x y : α}
  (h : Relation.TransGen edge x y) : ∃ srcs, Walk edge x y srcs
:= by
  induction h with
  | single h => exact ⟨_, .single h⟩
  | tail _ h ih =>
    obtain ⟨_, w⟩ := ih
    exact ⟨_, w.append (.single h)⟩

/-- Every vertex a walk leaves from has an edge. -/
public theorem Walk.source_edge {α} {edge : α → α → Prop} {x y : α} {srcs : List α}
  (h : Walk edge x y srcs) : ∀ v ∈ srcs, ∃ w, edge v w
:= by
  induction h with
  | single h => simpa using ⟨_, h⟩
  | cons h _ ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨_, h⟩
    · exact ih v hv

/-- A walk through `v` continues from `v` along a suffix of its sources. -/
public theorem Walk.suffix {α} {edge : α → α → Prop} {x y v : α} {srcs : List α}
  (h : Walk edge x y srcs) (hv : v ∈ srcs) :
  ∃ srcs', srcs' <:+ srcs ∧ Walk edge v y srcs'
:= by
  induction h with
  | single h =>
    obtain rfl := List.mem_singleton.mp hv
    exact ⟨_, List.suffix_refl _, .single h⟩
  | cons h w ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨_, List.suffix_refl _, .cons h w⟩
    · obtain ⟨srcs', hsfx, w'⟩ := ih hv
      exact ⟨srcs', hsfx.trans (List.suffix_cons _ _), w'⟩

/-- Every walk can be shortened to one that leaves from each vertex at most once. -/
public theorem Walk.nodup {α} {edge : α → α → Prop} {x y : α} {srcs : List α}
  (h : Walk edge x y srcs) :
  ∃ srcs', srcs'.Nodup ∧ srcs' ⊆ srcs ∧ Walk edge x y srcs'
:= by
  induction h with
  | @single x _ h => exact ⟨[x], by simp, List.Subset.refl _, .single h⟩
  | @cons x _ _ _ h _ ih =>
    obtain ⟨srcs', hnodup, hsub, w⟩ := ih
    by_cases hx : x ∈ srcs'
    · obtain ⟨srcs'', hsfx, w'⟩ := w.suffix hx
      exact ⟨srcs'', hnodup.sublist hsfx.sublist,
        fun _ hv => List.mem_cons_of_mem _ (hsub (hsfx.subset hv)), w'⟩
    · exact ⟨x :: srcs', List.nodup_cons.mpr ⟨hx, hnodup⟩, List.cons_subset_cons _ hsub,
        .cons h w⟩

end Cedar.Relation
