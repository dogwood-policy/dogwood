import Dogwood.Thm.Monitorable

/-!
# A condition depends on its valuation only through its free variables

`sat_congr_val`: two valuations that agree on a condition's free variables make it hold at the
same timepoints. The same holds of what an operand denotes (`denotes_congr_val`) and of an
aggregate's total (`total_congr_val`).

`bindAll_map`, `map_bindAll` and `lookup_zip_map` read an aggregation row back off the valuation
that binds it, as an implementation that computes the rows needs.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value)

theorem eval?_congr_val {e : Event} {v v' : Valuation} (t : Term) (h : ∀ y ∈ t.fv, v y = v' y) :
    t.eval? e v = t.eval? e v' := by
  cases t <;> simp_all [Term.eval?, Term.fv]

theorem mem_argsFv {args : List (Path × Term)} {a : Path × Term} (ha : a ∈ args) :
    ∀ y ∈ a.2.fv, y ∈ Formula.argsFv args := by
  induction args with
  | nil => cases ha
  | cons b args ih =>
    intro y hy
    simp only [Formula.argsFv, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact .inl hy
    · exact .inr (ih ha y hy)

theorem argsMatch_congr_val {e : Event} {v v' : Valuation} {ev : Event} {args : List (Path × Term)}
    (h : ∀ y ∈ Formula.argsFv args, v y = v' y) : ArgsMatch e v ev args ↔ ArgsMatch e v' ev args := by
  unfold ArgsMatch
  refine forall_congr' fun a => imp_congr_right fun ha => exists_congr fun w => and_congr_right fun _ => ?_
  have hv := eval?_congr_val (e := e) a.2 fun y hy => h y (mem_argsFv ha y hy)
  cases ht : a.2 <;> simp only [Term.Matches] <;> rw [ht] at hv <;> rw [hv]

theorem bindAll_congr {xs : List VarName} {ws : List TVal} (hlen : ws.length = xs.length)
    {v v' : Valuation} (y : VarName) (hy : y ∈ xs ∨ v y = v' y) :
    (v.bindAll xs ws) y = (v'.bindAll xs ws) y := by
  induction xs generalizing ws v v' with
  | nil => cases ws <;> simp_all [Valuation.bindAll]
  | cons x xs ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      simp only [Valuation.bindAll]
      apply ih (by simpa using hlen)
      by_cases hx : y ∈ xs
      · exact .inl hx
      · right
        by_cases hyx : y = x
        · simp [Valuation.bind, hyx]
        · simp only [Valuation.bind, hyx, if_false]
          rcases hy with hy | hy
          · rcases List.mem_cons.mp hy with h | h
            · exact absurd h hyx
            · exact absurd h hx
          · exact hy

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

mutual

theorem sat_congr_val : (φ : Formula) → ∀ (v v' : Valuation) (j : Nat), (∀ y ∈ φ.fv, v y = v' y) →
    (Sat ι rate σ e vis v j φ ↔ Sat ι rate σ e vis v' j φ)
  | .and φ ψ, v, v', j, h => by
    simp only [Formula.fv, List.mem_append] at h
    simp only [Sat]
    rw [sat_congr_val φ v v' j fun y hy => h y (.inl hy), sat_congr_val ψ v v' j fun y hy => h y (.inr hy)]
  | .not φ, v, v', j, h => by
    simp only [Sat]; rw [sat_congr_val φ v v' j h]
  | .formerly w φ, v, v', j, h => by
    simp only [Sat]
    exact exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => sat_congr_val φ v v' k h
  | .previous w φ, v, v', j, h => by
    simp only [Sat]
    exact exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => and_congr_right fun _ => sat_congr_val φ v v' k h
  | .since φ w ψ, v, v', j, h => by
    simp only [Formula.fv, List.mem_append] at h
    simp only [Sat]
    refine exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => and_congr (sat_congr_val ψ v v' k fun y hy => h y (.inr hy)) ?_
    exact forall_congr' fun k' => imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right
      fun _ => sat_congr_val φ v v' k' fun y hy => h y (.inl hy)
  | .pred a k args, v, v', j, h => by
    simp only [Formula.fv] at h
    simp only [Sat]
    exact exists_congr fun p => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => argsMatch_congr_val h
  | .cmp op l r, v, v', j, h => by
    simp only [Formula.fv, List.mem_append] at h
    simp only [Sat]
    exact exists_congr fun a => exists_congr fun b =>
      and_congr (denotes_congr_val l v v' j (fun y hy => h y (.inl hy)) a)
        (and_congr_left fun _ => denotes_congr_val r v v' j (fun y hy => h y (.inr hy)) b)
  | .exist x φ, v, v', j, h => by
    simp only [Sat]
    refine exists_congr fun w => sat_congr_val φ _ _ j fun y hy => ?_
    by_cases hyx : y = x.name
    · simp [Valuation.bind, hyx]
    · simp only [Valuation.bind, hyx, if_false]
      exact h y (by simp [Formula.fv, hy, hyx])
  | .tp x, v, v', j, h => by
    simp only [Formula.fv, List.mem_singleton, forall_eq] at h
    simp only [Sat, h]

theorem denotes_congr_val : (t : Term) → ∀ (v v' : Valuation) (j : Nat), (∀ y ∈ t.fv, v y = v' y) →
    ∀ c, (Denotes ι rate σ e vis v j t c ↔ Denotes ι rate σ e vis v' j t c)
  | .agg a, v, v', j, h, c => by
    simp only [Denotes]
    exact exists_congr fun n => and_congr_left fun _ => total_congr_val a v v' j h n
  | .arith op l r, v, v', j, h, c => by
    simp only [Term.fv, List.mem_append] at h
    simp only [Denotes]
    exact exists_congr fun m => exists_congr fun n =>
      and_congr (denotes_congr_val l v v' j (fun y hy => h y (.inl hy)) _)
        (and_congr_left fun _ => denotes_congr_val r v v' j (fun y hy => h y (.inr hy)) _)
  | .entity _, v, v', _, h, c | .long _, v, v', _, h, c | .decimal _, v, v', _, h, c
  | .string _, v, v', _, h, c | .bool _, v, v', _, h, c | .context _, v, v', _, h, c
  | .scope _ _, v, v', _, h, c | .var _, v, v', _, h, c | .wildcard, v, v', _, h, c => by
    simp only [Denotes]
    rw [eval?_congr_val _ h]

theorem total_congr_val : (a : Aggregate) → ∀ (v v' : Valuation) (j : Nat), (∀ y ∈ a.fv, v y = v' y) →
    ∀ n, (Total ι rate σ e vis v j a n ↔ Total ι rate σ e vis v' j a n)
  | .count dom body, v, v', j, h, n | .sum _ dom body, v, v', j, h, n => by
    simp only [Total]
    have hrow : ∀ row : List TVal, row.length = (domainNames dom).length →
        (Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body ↔
          Sat ι rate σ e vis (v'.bindAll (domainNames dom) row) j body) := by
      intro row hl
      apply sat_congr_val body _ _ j
      intro y hy
      apply bindAll_congr hl
      by_cases hd : y ∈ domainNames dom
      · exact .inl hd
      · right
        apply h
        simp only [Aggregate.fv, List.mem_filter, Bool.not_eq_true']
        refine ⟨hy, ?_⟩
        cases hc : (List.map (fun x => x.name) dom).contains y
        · rfl
        · exact absurd (mem_dedup.mpr (List.contains_iff_mem.mp hc)) hd
    all_goals
      refine exists_congr fun rows => and_congr_right fun _ => and_congr_left fun _ =>
        forall_congr' fun row => ?_
      constructor
      · intro hm
        rw [hm]
        exact ⟨fun ⟨hl, hs⟩ => ⟨hl, (hrow row hl).mp hs⟩, fun ⟨hl, hs⟩ => ⟨hl, (hrow row hl).mpr hs⟩⟩
      · intro hm
        rw [hm]
        exact ⟨fun ⟨hl, hs⟩ => ⟨hl, (hrow row hl).mpr hs⟩, fun ⟨hl, hs⟩ => ⟨hl, (hrow row hl).mp hs⟩⟩

end

end

/-! ## Reading rows back off a valuation -/

theorem bindAll_map {v : Valuation} {xs : List VarName} (hnd : xs.Nodup) (f : VarName → TVal) :
    ∀ y ∈ xs, (v.bindAll xs (xs.map f)) y = some (f y) := by
  induction xs generalizing v with
  | nil => intro y h; cases h
  | cons x xs ih =>
    intro y hy
    have ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, Valuation.bindAll]
    by_cases hyx : y ∈ xs
    · exact ih hnd' y hyx
    · have hyeq : y = x := by
        rcases List.mem_cons.mp hy with h | h
        · exact h
        · exact absurd h hyx
      subst hyeq
      rw [bindAll_not_mem hyx]
      simp [Valuation.bind]

/-- A list of values of the length of `xs` is the values its binding gives `xs`. -/
theorem map_bindAll {v : Valuation} {xs : List VarName} (hnd : xs.Nodup) {vals : List TVal}
    (hlen : vals.length = xs.length) (d : TVal) :
    xs.map (fun y => ((v.bindAll xs vals) y).getD d) = vals := by
  induction xs generalizing v vals with
  | nil => cases vals <;> simp_all
  | cons x xs ih =>
    cases vals with
    | nil => simp at hlen
    | cons w ws =>
      have ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      simp only [List.map_cons, List.cons.injEq, Valuation.bindAll]
      refine ⟨?_, ih (v := v.bind x w) hnd' (by simpa using hlen)⟩
      rw [bindAll_not_mem hx]
      simp [Valuation.bind]

/-- The value a list of pairs looks up for the first key of the list it was zipped from. -/
theorem lookup_zip_map {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {β : Type} (f : α → β) {s : α}
    (hs : s ∈ xs) :
    (xs.zip (xs.map f)).lookup s = some (f s) := by
  induction xs with
  | nil => cases hs
  | cons x xs ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
    by_cases h : s = x
    · subst h; simp
    · have : (s == x) = false := by simpa using h
      rw [this]
      exact ih (by simpa [h] using hs)

end Dogwood.Thm
