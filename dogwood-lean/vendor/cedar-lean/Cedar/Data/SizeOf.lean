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
import all Cedar.Data.Map -- allow accessing internals of Cedar.Data.Map, necessary for sizeOf calculations
public import Cedar.Data.Set

/-!
  Lemmas involving `sizeOf`, which are located here rather than in `Cedar/Thm`
  because they are needed for some definitions in `Cedar/Spec` and/or
  `Cedar/Partial`, and our convention prevents files in `Cedar/Spec` or
  `Cedar/Partial` from depending on lemmas in `Cedar/Thm`.
-/

/-! ## List -/

namespace Cedar.Data.List

public theorem sizeOf_attach₂ [SizeOf α] [SizeOf β] {a : α} {b : β} {l : List (α × β)} :
  (a, b) ∈ l → sizeOf (a, b).snd < 1 + sizeOf l
:= by
  intro hin
  simp only
  replace hin := List.sizeOf_lt_of_mem hin
  simp only [Prod.mk.sizeOf_spec] at hin
  omega

public theorem sizeOf_attach₃ [SizeOf α] [SizeOf β] {a : α} {b : β} {l : List (α × β)} :
  (a, b) ∈ l → sizeOf (a, b).snd < 1 + (1 + sizeOf l)
:= by
  intro hin
  simp only
  replace hin := List.sizeOf_lt_of_mem hin
  simp only [Prod.mk.sizeOf_spec] at hin
  omega

end Cedar.Data.List

namespace Cedar.Data.Map

/-! ## Map -/

public theorem sizeOf_lt_of_value [SizeOf α] [SizeOf β] {m : Map α β} {k : α} {v : β}
  (h : (k, v) ∈ m.1) :
  sizeOf v < sizeOf m
:= by
  simp only [Membership.mem] at h
  replace h := List.sizeOf_lt_of_mem h
  have v_lt_kv : sizeOf v < sizeOf (k, v) := by
    simp only [sizeOf, Prod._sizeOf_1]
    omega
  have m1_lt_m : sizeOf m.1 < sizeOf m := by
    simp only [sizeOf, Map._sizeOf_1]
    omega
  omega

public theorem sizeOf_lt_of_find? [SizeOf α] [SizeOf β] [DecidableEq α] {m : Map α β} {k : α} {v : β}
  (h : m.find? k = some v) :
  sizeOf v < sizeOf m
:= by
  simp only [find?, toList] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst v
  rename_i h
  replace h := List.mem_of_find?_eq_some h
  have := List.sizeOf_lt_of_mem h
  simp_all only [sizeOf, Prod._sizeOf_1, _sizeOf_1]
  omega

public theorem sizeOf_lt_of_toList [SizeOf α] [SizeOf β] (m : Map α β) :
  sizeOf m.toList < sizeOf m
:= by
  unfold toList
  conv => rhs ; unfold sizeOf _sizeOf_inst _sizeOf_1 ; simp only
  generalize sizeOf m.1 = s
  omega

public theorem sizeOf_lt_of_values [SizeOf α] [SizeOf β] {m : Map α β}
  (h : b ∈ m.values) :
  sizeOf b < sizeOf m
:= by
  simp only [values, List.mem_map, Prod.exists, exists_eq_right] at h
  replace ⟨a, h⟩ := h
  exact List.sizeOf_snd_lt_sizeOf_list h

public theorem sizeOf_lt_of_tl [SizeOf α] [SizeOf β] {m : Map α β} {tl : List (α × β)}
  (h : m.toList = (k, v) :: tl) :
  1 + sizeOf tl < sizeOf m
:= by
  conv => rhs ; unfold sizeOf _sizeOf_inst _sizeOf_1
  simp only
  unfold toList at h
  simp only [h, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
  omega

end Cedar.Data.Map

namespace Cedar.Data.Set

/-! ## Set -/

public theorem sizeOf_lt_of_mem [SizeOf α] {s : Set α}
  (h : a ∈ s) :
  sizeOf a < sizeOf s
:= by
  simp only [Membership.mem, elts] at h
  replace h := List.sizeOf_lt_of_mem h
  have _ : sizeOf s.1 < sizeOf s := by
    simp only [sizeOf, _sizeOf_1]
    omega
  omega

public theorem sizeOf_lt_of_elts [SizeOf α] (s : Set α) :
  sizeOf s.elts < sizeOf s
:= by
  simp only [elts]
  conv => rhs ; unfold sizeOf _sizeOf_inst _sizeOf_1 ; simp
  omega

public theorem sizeOf_mk [SizeOf α] (xs : List α) :
  sizeOf (Set.mk xs) = 1 + sizeOf xs
:= by simp

end Cedar.Data.Set
