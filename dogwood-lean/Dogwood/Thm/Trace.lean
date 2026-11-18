import Dogwood.Spec.Event

/-!
# Well-formed traces

Facts about `Trace.StrictlyIncreasing`, the language's rule that the timestamps of accepted
events strictly increase, and about the weaker `Trace.Nondecreasing`: their reading at indices,
that the rule implies the weaker property, that both survive taking a subsequence, a prefix, or
a suffix of the trace, and when appending one event keeps them.
-/

namespace Dogwood.Spec.Trace

open Dogwood.Spec

variable {σ τ : Trace}

/-! ## At indices -/

theorem strictlyIncreasing_iff_getElem :
    σ.StrictlyIncreasing ↔
      ∀ i j (hi : i < σ.length) (hj : j < σ.length), i < j → σ[i].ts < σ[j].ts := by
  unfold StrictlyIncreasing
  rw [List.pairwise_iff_getElem]

theorem nondecreasing_iff_getElem :
    σ.Nondecreasing ↔
      ∀ i j (hi : i < σ.length) (hj : j < σ.length), i ≤ j → σ[i].ts ≤ σ[j].ts := by
  unfold Nondecreasing
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    rcases Nat.lt_or_eq_of_le hij with hlt | rfl
    · exact h i j hi hj hlt
    · exact Int.le_refl _
  · intro h i j hi hj hij
    exact h i j hi hj (Nat.le_of_lt hij)

/-- Under the language's rule, an earlier timepoint has a smaller timestamp. -/
theorem StrictlyIncreasing.ts_lt (h : σ.StrictlyIncreasing) {i j : Nat} {p q : TimePoint}
    (hij : i < j) (hp : σ[i]? = some p) (hq : σ[j]? = some q) : p.ts < q.ts := by
  have hj : j < σ.length := by
    rcases Nat.lt_or_ge j σ.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hq; cases hq
  have hi : i < σ.length := Nat.lt_trans hij hj
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hp
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hq
  subst hp; subst hq
  exact strictlyIncreasing_iff_getElem.mp h i j hi hj hij

/-- On a nondecreasing trace, an earlier timepoint has a timestamp no larger. -/
theorem Nondecreasing.ts_le (h : σ.Nondecreasing) {i j : Nat} {p q : TimePoint}
    (hij : i ≤ j) (hp : σ[i]? = some p) (hq : σ[j]? = some q) : p.ts ≤ q.ts := by
  have hj : j < σ.length := by
    rcases Nat.lt_or_ge j σ.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hq; cases hq
  have hi : i < σ.length := Nat.lt_of_le_of_lt hij hj
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hp
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hq
  subst hp; subst hq
  exact nondecreasing_iff_getElem.mp h i j hi hj hij

/-- The language's rule implies the weaker property. -/
theorem StrictlyIncreasing.nondecreasing (h : σ.StrictlyIncreasing) : σ.Nondecreasing :=
  List.Pairwise.imp (fun h => Int.le_of_lt h) h

/-- Under the language's rule, two timepoints with the same timestamp are the same timepoint. -/
theorem StrictlyIncreasing.index_eq (h : σ.StrictlyIncreasing) {i j : Nat} {p q : TimePoint}
    (hp : σ[i]? = some p) (hq : σ[j]? = some q) (hts : p.ts = q.ts) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · have := h.ts_lt hij hp hq; omega
  · rfl
  · have := h.ts_lt hij hq hp; omega

/-! ## Subsequences, prefixes, suffixes -/

theorem StrictlyIncreasing.sublist (h : σ.StrictlyIncreasing) (hs : τ.Sublist σ) :
    τ.StrictlyIncreasing :=
  List.Pairwise.sublist hs h

theorem Nondecreasing.sublist (h : σ.Nondecreasing) (hs : τ.Sublist σ) : τ.Nondecreasing :=
  List.Pairwise.sublist hs h

theorem StrictlyIncreasing.take (h : σ.StrictlyIncreasing) (n : Nat) :
    Trace.StrictlyIncreasing (σ.take n) :=
  h.sublist (List.take_sublist n σ)

theorem StrictlyIncreasing.drop (h : σ.StrictlyIncreasing) (n : Nat) :
    Trace.StrictlyIncreasing (σ.drop n) :=
  h.sublist (List.drop_sublist n σ)

theorem StrictlyIncreasing.filter (h : σ.StrictlyIncreasing) (P : TimePoint → Bool) :
    Trace.StrictlyIncreasing (σ.filter P) :=
  h.sublist List.filter_sublist

theorem Nondecreasing.take (h : σ.Nondecreasing) (n : Nat) : Trace.Nondecreasing (σ.take n) :=
  h.sublist (List.take_sublist n σ)

theorem Nondecreasing.drop (h : σ.Nondecreasing) (n : Nat) : Trace.Nondecreasing (σ.drop n) :=
  h.sublist (List.drop_sublist n σ)

theorem Nondecreasing.filter (h : σ.Nondecreasing) (P : TimePoint → Bool) :
    Trace.Nondecreasing (σ.filter P) :=
  h.sublist List.filter_sublist

theorem StrictlyIncreasing.of_append_left (h : Trace.StrictlyIncreasing (σ ++ τ)) :
    σ.StrictlyIncreasing :=
  h.sublist (List.sublist_append_left σ τ)

theorem StrictlyIncreasing.nil : Trace.StrictlyIncreasing [] := List.Pairwise.nil

/-! ## Appending an event -/

/-- Appending `p` keeps the language's rule exactly when `p`'s timestamp is greater than every
accepted event's. -/
theorem strictlyIncreasing_append_singleton {p : TimePoint} :
    Trace.StrictlyIncreasing (σ ++ [p]) ↔ σ.StrictlyIncreasing ∧ ∀ q ∈ σ, q.ts < p.ts := by
  unfold StrictlyIncreasing
  rw [List.pairwise_append]
  simp

/-- On a trace that keeps the rule, being greater than the last timestamp is being greater than
every timestamp. -/
theorem StrictlyIncreasing.lt_of_getLast? (h : σ.StrictlyIncreasing) {q : TimePoint}
    (hq : σ.getLast? = some q) {p : TimePoint} (hp : q.ts < p.ts) : ∀ r ∈ σ, r.ts < p.ts := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hlast : σ[σ.length - 1]? = some q := by
    rw [List.getLast?_eq_getElem?] at hq; exact hq
  rcases Nat.lt_or_ge i (σ.length - 1) with hlt | hge
  · exact Int.lt_trans (h.ts_lt hlt (List.getElem?_eq_getElem hi) hlast) hp
  · have : i = σ.length - 1 := by omega
    subst this
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hlast
    rw [hlast]; exact hp

end Dogwood.Spec.Trace
