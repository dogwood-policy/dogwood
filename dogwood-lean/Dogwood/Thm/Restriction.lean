import Dogwood.Spec.Temporal.Safety

/-!
# The restriction closure

Facts about `Formula.Restricts`, the variables a condition range-restricts:

* `restricts_mono`: restricting more variables outside restricts more inside;
* `restricts_sub`: a condition restricts only its free variables, besides those restricted
  outside it;
* `restricts_congr`: whether a condition restricts `x` depends only on which of its free
  variables, and whether `x` itself, are restricted outside it;
* `restricts_and_iff`: the closure of a `&&` chain is reached by iteration, after at most one
  more round than the chain has free variables (`Formula.stage`). This is what makes the
  closure computable, both for the decision procedure (`Dogwood.Thm.restrictsB_iff`) and for the
  candidate values (`Dogwood.Thm.rr_sound`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-! ## Monotonicity -/

theorem Formula.restricts_mono : (φ : Formula) → {R R' : VarName → Prop} →
    (∀ z, R z → R' z) → ∀ {x}, φ.Restricts R x → φ.Restricts R' x
  | .pred _ _ _, _, _, _, _, h => h
  | .tp _, _, _, _, _, h => h
  | .cmp op l r, _, _, hR, x, h => by
    cases op <;> simp only [Formula.Restricts] at h ⊢
    exact ⟨h.1, fun y hy => hR y (h.2 y hy)⟩
  | .not _, _, _, _, _, h => h
  | .formerly _ φ, _, _, hR, _, h => Formula.restricts_mono φ hR h
  | .previous _ φ, _, _, hR, _, h => Formula.restricts_mono φ hR h
  | .since _ _ ψ, _, _, hR, _, h => Formula.restricts_mono ψ hR h
  | .exist y φ, _, _, hR, _, h =>
    ⟨h.1, Formula.restricts_mono φ (fun z hz => ⟨hz.1, hR z hz.2⟩) h.2⟩
  | .and _ _, _, _, hR, _, h => fun S hS hφ hψ => h S (fun z hz => hS z (hR z hz)) hφ hψ

theorem Formula.restricted_mono {φ : Formula} {R R' : VarName → Prop} (hR : ∀ z, R z → R' z)
    {x : VarName} (h : φ.Restricted R x) : φ.Restricted R' x :=
  h.elim (fun h => .inl (hR x h)) fun h => .inr (Formula.restricts_mono φ hR h)

/-! ## A condition restricts only its free variables -/

theorem mem_argsFv_of_mem {args : List (Path × Term)} {p : Path} {t : Term}
    (h : (p, t) ∈ args) : ∀ y ∈ t.fv, y ∈ Formula.argsFv args := by
  induction args with
  | nil => cases h
  | cons a args ih =>
    intro y hy
    obtain ⟨q, u⟩ := a
    simp only [Formula.argsFv, List.mem_append]
    rcases List.mem_cons.mp h with h | h
    · cases h; exact .inl hy
    · exact .inr (ih h y hy)

theorem eqRestricted_mem_fv {l r : Term} {x : VarName} (h : eqRestricted? l r = some x) :
    x ∈ l.fv ++ r.fv := by
  cases l <;> cases r <;> simp only [eqRestricted?] at h <;>
    first
    | (split at h <;> simp_all [Term.fv])
    | simp_all

theorem Formula.restricts_sub : (φ : Formula) → {R : VarName → Prop} → ∀ {x},
    φ.Restricts R x → x ∈ φ.fv ∨ R x
  | .pred _ _ args, _, x, ⟨p, h⟩ => .inl (mem_argsFv_of_mem h x (by simp [Term.fv]))
  | .tp _, _, _, h => by
    simp only [Formula.Restricts] at h
    subst h
    exact .inl (by simp [Formula.fv])
  | .cmp op l r, _, _, h => by
    cases op <;> simp only [Formula.Restricts] at h
    exact .inl (eqRestricted_mem_fv h.1)
  | .not _, _, _, h => h.elim
  | .formerly _ φ, _, _, h => Formula.restricts_sub φ h
  | .previous _ φ, _, _, h => Formula.restricts_sub φ h
  | .since φ _ ψ, _, _, h => by
    rcases Formula.restricts_sub ψ h with h | h
    · exact .inl (by simp [Formula.fv, h])
    · exact .inr h
  | .exist y φ, _, _, ⟨hne, h⟩ => by
    rcases Formula.restricts_sub φ h with h | h
    · exact .inl (by simp [Formula.fv, h, hne])
    · exact .inr h.2
  | .and φ ψ, R, x, h => by
    refine h (fun z => z ∈ (Formula.and φ ψ).fv ∨ R z) (fun z hz => .inr hz) ?_ ?_
    · intro z hz
      rcases Formula.restricts_sub φ hz with h | h
      · exact .inl (by simp [Formula.fv, h])
      · exact h
    · intro z hz
      rcases Formula.restricts_sub ψ hz with h | h
      · exact .inl (by simp [Formula.fv, h])
      · exact h

/-! ## Congruence -/

/-- The `&&` case of `restricts_congr`, given congruence for the two conjuncts: each closure is
contained in the other, outside the chain's free variables. -/
theorem restricts_and_congr_aux (φ ψ : Formula)
    (ihφ : ∀ {R R' : VarName → Prop}, (∀ y ∈ φ.fv, R y ↔ R' y) → ∀ {x}, (R x ↔ R' x) →
      (φ.Restricts R x ↔ φ.Restricts R' x))
    (ihψ : ∀ {R R' : VarName → Prop}, (∀ y ∈ ψ.fv, R y ↔ R' y) → ∀ {x}, (R x ↔ R' x) →
      (ψ.Restricts R x ↔ ψ.Restricts R' x))
    {R₁ R₂ : VarName → Prop} (h₁₂ : ∀ y ∈ (Formula.and φ ψ).fv, R₁ y ↔ R₂ y) {x : VarName}
    (hx₁₂ : R₁ x ↔ R₂ x) (h : (Formula.and φ ψ).Restricts R₁ x) :
    (Formula.and φ ψ).Restricts R₂ x := by
  intro S hS hφ hψ
  let T : VarName → Prop := fun z => S z ∨ (z ∉ (Formula.and φ ψ).fv ∧ R₁ z)
  have hT : ∀ z ∈ (Formula.and φ ψ).fv, (T z ↔ S z) := fun z hz =>
    ⟨fun h => h.elim id fun h => absurd hz h.1, Or.inl⟩
  have hTx := h T (fun z hz => by
      by_cases hzf : z ∈ (Formula.and φ ψ).fv
      · exact .inl (hS z ((h₁₂ z hzf).mp hz))
      · exact .inr ⟨hzf, hz⟩)
    (fun z hz => by
      rcases Formula.restricts_sub φ hz with hzf | hzT
      · have hzf' : z ∈ (Formula.and φ ψ).fv := by simp [Formula.fv, hzf]
        have := (ihφ (fun y hy => hT y (by simp [Formula.fv, hy])) (hT z hzf')).mp hz
        exact .inl (hφ z this)
      · exact hzT)
    (fun z hz => by
      rcases Formula.restricts_sub ψ hz with hzf | hzT
      · have hzf' : z ∈ (Formula.and φ ψ).fv := by simp [Formula.fv, hzf]
        have := (ihψ (fun y hy => hT y (by simp [Formula.fv, hy])) (hT z hzf')).mp hz
        exact .inl (hψ z this)
      · exact hzT)
  rcases hTx with hSx | ⟨_, hR₁x⟩
  · exact hSx
  · exact hS x (hx₁₂.mp hR₁x)


theorem Formula.restricts_congr : (φ : Formula) → {R R' : VarName → Prop} →
    (∀ y ∈ φ.fv, R y ↔ R' y) → ∀ {x}, (R x ↔ R' x) → (φ.Restricts R x ↔ φ.Restricts R' x)
  | .pred _ _ _, _, _, _, _, _ => Iff.rfl
  | .tp _, _, _, _, _, _ => Iff.rfl
  | .cmp op l r, R, R', hR, x, _ => by
    cases op <;> simp only [Formula.Restricts]
    refine and_congr_right fun hx => forall_congr' fun y => imp_congr_right fun hy => hR y ?_
    simp only [Formula.fv]
    unfold valueSide at hy
    cases l with
    | var z =>
      simp only at hy
      split at hy
      · exact List.mem_append_right _ hy
      · exact List.mem_append_left _ hy
    | _ => exact List.mem_append_left _ hy
  | .not _, _, _, _, _, _ => Iff.rfl
  | .formerly _ φ, _, _, hR, _, hx => Formula.restricts_congr φ hR hx
  | .previous _ φ, _, _, hR, _, hx => Formula.restricts_congr φ hR hx
  | .since φ _ ψ, _, _, hR, _, hx =>
    Formula.restricts_congr ψ (fun y hy => hR y (by simp [Formula.fv, hy])) hx
  | .exist y φ, R, R', hR, x, hx => by
    simp only [Formula.Restricts]
    refine and_congr_right fun hne => Formula.restricts_congr φ ?_ ?_
    · intro z hz
      by_cases hzy : z = y.name
      · simp [hzy]
      · simp only [hzy, ne_eq, not_false_eq_true, true_and]
        exact hR z (by simp [Formula.fv, hz, hzy])
    · simp only [hne, ne_eq, not_false_eq_true, true_and]; exact hx
  | .and φ ψ, R, R', hR, x, hx =>
    ⟨restricts_and_congr_aux φ ψ (Formula.restricts_congr φ) (Formula.restricts_congr ψ) hR hx,
      restricts_and_congr_aux φ ψ (Formula.restricts_congr φ) (Formula.restricts_congr ψ)
        (fun y hy => (hR y hy).symm) hx.symm⟩

/-! ## The closure is reached by iteration -/

/-- The `i`-th round of the closure of `φ && ψ` from `R`: the variables restricted after `i`
rounds, in each of which every conjunct adds what it restricts from the variables found so
far. -/
def Formula.stage (R : VarName → Prop) (φ ψ : Formula) : Nat → VarName → Prop
  | 0 => R
  | i + 1 => fun z => Formula.stage R φ ψ i z ∨ φ.Restricts (Formula.stage R φ ψ i) z ∨
      ψ.Restricts (Formula.stage R φ ψ i) z

theorem Formula.stage_succ_of {R : VarName → Prop} {φ ψ : Formula} {i : Nat} {z : VarName}
    (h : Formula.stage R φ ψ i z) : Formula.stage R φ ψ (i + 1) z := .inl h

theorem Formula.stage_mono {R : VarName → Prop} {φ ψ : Formula} :
    ∀ {i j : Nat}, i ≤ j → ∀ {z}, Formula.stage R φ ψ i z → Formula.stage R φ ψ j z
  | i, j, hij, z, h => by
    induction j with
    | zero => obtain rfl : i = 0 := by omega
              exact h
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact Formula.stage_succ_of (ih (by omega))
      · obtain rfl : i = j + 1 := by omega
        exact h

/-- Every round lies inside the closure. -/
theorem Formula.stage_sub {R : VarName → Prop} {φ ψ : Formula} :
    ∀ (i : Nat) {z}, Formula.stage R φ ψ i z → (Formula.and φ ψ).Restricts R z
  | 0, z, h => fun S hS _ _ => hS z h
  | i + 1, z, h => by
    intro S hS hφ hψ
    have ih : ∀ y, Formula.stage R φ ψ i y → S y := fun y hy =>
      Formula.stage_sub i hy S hS hφ hψ
    rcases h with h | h | h
    · exact ih z h
    · exact hφ z (Formula.restricts_mono φ ih h)
    · exact hψ z (Formula.restricts_mono ψ ih h)

/-- A round that adds no free variable of the chain is closed. -/
theorem Formula.stage_closed_of {R : VarName → Prop} {φ ψ : Formula} {i : Nat}
    (h : ∀ y ∈ (Formula.and φ ψ).fv, Formula.stage R φ ψ (i + 1) y → Formula.stage R φ ψ i y) :
    (∀ z, φ.Restricts (Formula.stage R φ ψ i) z → Formula.stage R φ ψ i z) ∧
      (∀ z, ψ.Restricts (Formula.stage R φ ψ i) z → Formula.stage R φ ψ i z) := by
  constructor
  · intro z hz
    rcases Formula.restricts_sub φ hz with hzf | hz'
    · exact h z (by simp [Formula.fv, hzf]) (.inr (.inl hz))
    · exact hz'
  · intro z hz
    rcases Formula.restricts_sub ψ hz with hzf | hz'
    · exact h z (by simp [Formula.fv, hzf]) (.inr (.inr hz))
    · exact hz'

/-- A closed round stays the same in every later round. -/
theorem Formula.stage_stable {R : VarName → Prop} {φ ψ : Formula} {i : Nat}
    (hc : (∀ z, φ.Restricts (Formula.stage R φ ψ i) z → Formula.stage R φ ψ i z) ∧
      (∀ z, ψ.Restricts (Formula.stage R φ ψ i) z → Formula.stage R φ ψ i z)) :
    ∀ k {z}, Formula.stage R φ ψ (i + k) z → Formula.stage R φ ψ i z
  | 0, _, h => h
  | k + 1, z, h => by
    have ih : ∀ y, Formula.stage R φ ψ (i + k) y → Formula.stage R φ ψ i y :=
      fun y hy => Formula.stage_stable hc k hy
    rcases h with h | h | h
    · exact ih z h
    · exact hc.1 z (Formula.restricts_mono φ ih h)
    · exact hc.2 z (Formula.restricts_mono ψ ih h)

section Counting

open Classical

/-- How many entries of `V` the predicate holds of. -/
noncomputable def countIn (V : List VarName) (P : VarName → Prop) : Nat :=
  (V.filter fun y => decide (P y)).length

theorem countIn_le (V : List VarName) (P : VarName → Prop) : countIn V P ≤ V.length :=
  List.length_filter_le _ _

theorem countIn_mono (V : List VarName) {P Q : VarName → Prop} (h : ∀ y ∈ V, P y → Q y) :
    countIn V P ≤ countIn V Q := by
  induction V with
  | nil => simp [countIn]
  | cons y V ih =>
    have ih' := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
    simp only [countIn, List.filter_cons] at ih' ⊢
    by_cases hp : P y <;> by_cases hq : Q y <;> simp [hp, hq] at ih' ⊢ <;> try omega
    exact absurd (h y (List.mem_cons_self ..) hp) hq

/-- Two predicates, one implying the other on `V`, that hold of as many entries of `V` agree
on `V`. -/
theorem countIn_eq {V : List VarName} {P Q : VarName → Prop} (h : ∀ y ∈ V, P y → Q y)
    (heq : countIn V P = countIn V Q) : ∀ y ∈ V, Q y → P y := by
  induction V with
  | nil => intro y hy; cases hy
  | cons y V ih =>
    have h' : ∀ z ∈ V, P z → Q z := fun z hz => h z (List.mem_cons_of_mem _ hz)
    have hle := countIn_mono V h'
    intro z hz hq
    by_cases hpy : P y
    · have hqy : Q y := h y (List.mem_cons_self ..) hpy
      have heq' : countIn V P = countIn V Q := by
        simp only [countIn, List.filter_cons, hpy, hqy, decide_true, if_true,
          List.length_cons] at heq
        simpa [countIn] using heq
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hpy
      · exact ih h' heq' z hz hq
    · by_cases hqy : Q y
      · have : countIn V P = countIn V Q + 1 := by
          simp only [countIn, List.filter_cons, hpy, hqy, decide_true, decide_false, if_true,
            List.length_cons] at heq
          simpa [countIn] using heq
        simp only [countIn] at hle this
        omega
      · have heq' : countIn V P = countIn V Q := by
          simp only [countIn, List.filter_cons, hpy, hqy, decide_false] at heq
          simpa [countIn] using heq
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd hq hqy
        · exact ih h' heq' z hz hq

/-- Some round up to the number of free variables of the chain is closed. -/
theorem Formula.exists_closed_stage (R : VarName → Prop) (φ ψ : Formula) :
    ∃ i ≤ (Formula.and φ ψ).fv.length,
      ∀ y ∈ (Formula.and φ ψ).fv, Formula.stage R φ ψ (i + 1) y → Formula.stage R φ ψ i y := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  -- Every round adds a free variable of the chain, so round `i` holds at least `i` of them.
  have grow : ∀ i, i ≤ (Formula.and φ ψ).fv.length + 1 →
      i ≤ countIn (Formula.and φ ψ).fv (Formula.stage R φ ψ i) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have hle := countIn_mono (Formula.and φ ψ).fv (P := Formula.stage R φ ψ i)
        (Q := Formula.stage R φ ψ (i + 1)) fun y _ hy => Formula.stage_succ_of hy
      have hne' : countIn (Formula.and φ ψ).fv (Formula.stage R φ ψ i) ≠
          countIn (Formula.and φ ψ).fv (Formula.stage R φ ψ (i + 1)) :=
        fun heq => hne i (by omega) (countIn_eq (fun y _ hy => Formula.stage_succ_of hy) heq)
      have := ih (by omega)
      omega
  have h1 := grow ((Formula.and φ ψ).fv.length + 1) (Nat.le_refl _)
  have h2 := countIn_le (Formula.and φ ψ).fv
    (Formula.stage R φ ψ ((Formula.and φ ψ).fv.length + 1))
  omega

end Counting

/-- The number of rounds that reach the closure of `φ && ψ`. -/
def Formula.rounds (φ ψ : Formula) : Nat := (Formula.and φ ψ).fv.length + 1

/-- **The closure of a chain is reached by iteration.** -/
theorem Formula.restricts_and_iff {R : VarName → Prop} {φ ψ : Formula} {x : VarName} :
    (Formula.and φ ψ).Restricts R x ↔ Formula.stage R φ ψ (Formula.rounds φ ψ) x := by
  constructor
  · intro h
    obtain ⟨i, hi, hcl⟩ := Formula.exists_closed_stage R φ ψ
    have hc := Formula.stage_closed_of hcl
    have hx : Formula.stage R φ ψ i x :=
      h _ (fun z hz => Formula.stage_mono (R := R) (φ := φ) (ψ := ψ) (Nat.zero_le i) hz) hc.1 hc.2
    exact Formula.stage_mono (by simp only [Formula.rounds]; omega) hx
  · exact Formula.stage_sub _

/-- The closure of a chain contains what each conjunct restricts from it. -/
theorem Formula.restricts_and_closed_left {R : VarName → Prop} {φ ψ : Formula} {z : VarName}
    (h : φ.Restricts ((Formula.and φ ψ).Restricts R) z) : (Formula.and φ ψ).Restricts R z :=
  fun S hS hφ hψ => hφ z (Formula.restricts_mono φ (fun _ hy => hy S hS hφ hψ) h)

theorem Formula.restricts_and_closed_right {R : VarName → Prop} {φ ψ : Formula} {z : VarName}
    (h : ψ.Restricts ((Formula.and φ ψ).Restricts R) z) : (Formula.and φ ψ).Restricts R z :=
  fun S hS hφ hψ => hψ z (Formula.restricts_mono ψ (fun _ hy => hy S hS hφ hψ) h)

theorem Formula.restricts_and_base {R : VarName → Prop} {φ ψ : Formula} {z : VarName}
    (h : R z) : (Formula.and φ ψ).Restricts R z :=
  fun _ hS _ _ => hS z h

end Dogwood.Thm
