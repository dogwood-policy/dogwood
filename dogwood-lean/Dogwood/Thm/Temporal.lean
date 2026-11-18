import Dogwood.Spec.Temporal.Semantics

/-!
# Properties of temporal satisfaction

* **Locality** (`sat_congr`): whether a condition holds at timepoint `j`
  depends on the trace only through the timepoints `0 … j` — their events and
  their visibility.
  The language is past-only.
* **Windows** (`sat_formerly_mono`): widening a `formerly` window can only
  make it hold more often.
* **Aggregates are well-defined** (`total_unique`): an aggregate has at most
  one total.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-- Two traces, and two visibilities, agree on the timepoints `0 … j`. -/
def AgreeUpTo (σ₁ σ₂ : Trace) (vis₁ vis₂ : Nat → Prop) (j : Nat) : Prop :=
  ∀ k ≤ j, σ₁[k]? = σ₂[k]? ∧ (vis₁ k ↔ vis₂ k)

section

variable {σ₁ σ₂ : Trace} {vis₁ vis₂ : Nat → Prop}

theorem AgreeUpTo.mono {j k : Nat} (h : AgreeUpTo σ₁ σ₂ vis₁ vis₂ j) (hk : k ≤ j) :
    AgreeUpTo σ₁ σ₂ vis₁ vis₂ k :=
  fun k' hk' => h k' (Nat.le_trans hk' hk)

theorem inWindow_congr {rate : TickRate} {j k : Nat} {w : Window} (h : AgreeUpTo σ₁ σ₂ vis₁ vis₂ j)
    (hk : k ≤ j) : InWindow rate σ₁ j k w ↔ InWindow rate σ₂ j k w := by
  simp only [InWindow, (h j (Nat.le_refl j)).1, (h k hk).1]

variable {ι : ImplChoices} {rate : TickRate} {e : Event}

mutual

theorem sat_congr : (φ : Formula) → (v : Valuation) → (j : Nat) →
    AgreeUpTo σ₁ σ₂ vis₁ vis₂ j → (Sat ι rate σ₁ e vis₁ v j φ ↔ Sat ι rate σ₂ e vis₂ v j φ)
  | .and φ ψ, v, j, h => by
    simp only [Sat]; rw [sat_congr φ v j h, sat_congr ψ v j h]
  | .not φ, v, j, h => by
    simp only [Sat]; rw [sat_congr φ v j h]
  | .formerly w φ, v, j, h => by
    simp only [Sat]
    constructor
    · rintro ⟨k, hk, hv, hw, hs⟩
      exact ⟨k, hk, ((h k hk).2).mp hv, (inWindow_congr h hk).mp hw,
        (sat_congr φ v k (h.mono hk)).mp hs⟩
    · rintro ⟨k, hk, hv, hw, hs⟩
      exact ⟨k, hk, ((h k hk).2).mpr hv, (inWindow_congr h hk).mpr hw,
        (sat_congr φ v k (h.mono hk)).mpr hs⟩
  | .previous w φ, v, j, h => by
    simp only [Sat]
    constructor
    · rintro ⟨k, hk, hv, hlast, hw, hs⟩
      have hk' := Nat.le_of_lt hk
      refine ⟨k, hk, ((h k hk').2).mp hv, ?_, (inWindow_congr h hk').mp hw,
        (sat_congr φ v k (h.mono hk')).mp hs⟩
      intro k' h₁ h₂ hv'
      exact hlast k' h₁ h₂ (((h k' (Nat.le_of_lt h₂)).2).mpr hv')
    · rintro ⟨k, hk, hv, hlast, hw, hs⟩
      have hk' := Nat.le_of_lt hk
      refine ⟨k, hk, ((h k hk').2).mpr hv, ?_, (inWindow_congr h hk').mpr hw,
        (sat_congr φ v k (h.mono hk')).mpr hs⟩
      intro k' h₁ h₂ hv'
      exact hlast k' h₁ h₂ (((h k' (Nat.le_of_lt h₂)).2).mp hv')
  | .since φ w ψ, v, j, h => by
    simp only [Sat]
    constructor
    · rintro ⟨k, hk, hv, hw, hs, hall⟩
      refine ⟨k, hk, ((h k hk).2).mp hv, (inWindow_congr h hk).mp hw,
        (sat_congr ψ v k (h.mono hk)).mp hs, ?_⟩
      intro k' h₁ h₂ hv'
      exact (sat_congr φ v k' (h.mono h₂)).mp (hall k' h₁ h₂ (((h k' h₂).2).mpr hv'))
    · rintro ⟨k, hk, hv, hw, hs, hall⟩
      refine ⟨k, hk, ((h k hk).2).mpr hv, (inWindow_congr h hk).mpr hw,
        (sat_congr ψ v k (h.mono hk)).mpr hs, ?_⟩
      intro k' h₁ h₂ hv'
      exact (sat_congr φ v k' (h.mono h₂)).mpr (hall k' h₁ h₂ (((h k' h₂).2).mp hv'))
  | .pred a kd args, v, j, h => by
    simp only [Sat, (h j (Nat.le_refl j)).1]
  | .cmp op l r, v, j, h => by
    simp only [Sat]
    constructor
    · rintro ⟨a, b, ha, hb, hop⟩
      exact ⟨a, b, (denotes_congr l v j h a).mp ha, (denotes_congr r v j h b).mp hb, hop⟩
    · rintro ⟨a, b, ha, hb, hop⟩
      exact ⟨a, b, (denotes_congr l v j h a).mpr ha, (denotes_congr r v j h b).mpr hb, hop⟩
  | .exist x φ, v, j, h => by
    simp only [Sat]
    exact exists_congr fun w => sat_congr φ (v.bind x.name w) j h
  | .tp x, v, j, h => by
    simp only [Sat]

theorem denotes_congr : (t : Term) → (v : Valuation) → (j : Nat) →
    AgreeUpTo σ₁ σ₂ vis₁ vis₂ j → (c : CVal) →
    (Denotes ι rate σ₁ e vis₁ v j t c ↔ Denotes ι rate σ₂ e vis₂ v j t c)
  | .agg a, v, j, h, c => by
    simp only [Denotes]
    exact exists_congr fun n => and_congr_left fun _ => total_congr a v j h n
  | .arith _ l r, v, j, h, c => by
    simp only [Denotes]
    exact exists_congr fun m => exists_congr fun n => by
      rw [denotes_congr l v j h (.num m), denotes_congr r v j h (.num n)]
  | .entity _, _, _, _, _ => by simp only [Denotes]
  | .long _, _, _, _, _ => by simp only [Denotes]
  | .decimal _, _, _, _, _ => by simp only [Denotes]
  | .string _, _, _, _, _ => by simp only [Denotes]
  | .bool _, _, _, _, _ => by simp only [Denotes]
  | .context _, _, _, _, _ => by simp only [Denotes]
  | .scope _ _, _, _, _, _ => by simp only [Denotes]
  | .var _, _, _, _, _ => by simp only [Denotes]
  | .wildcard, _, _, _, _ => by simp only [Denotes]

theorem total_congr : (a : Aggregate) → (v : Valuation) → (j : Nat) →
    AgreeUpTo σ₁ σ₂ vis₁ vis₂ j → (n : Int) →
    (Total ι rate σ₁ e vis₁ v j a n ↔ Total ι rate σ₂ e vis₂ v j a n)
  | .count dom body, v, j, h, n => by
    have ih := fun v' => sat_congr body v' j h
    simp only [Total, ih]
  | .sum s dom body, v, j, h, n => by
    have ih := fun v' => sat_congr body v' j h
    simp only [Total, ih]

end

/-- **Past-only.** Extending a trace never changes whether a condition held at
one of its timepoints. -/
theorem sat_append (τ : Trace) (vis : Nat → Prop) (v : Valuation) (j : Nat) (φ : Formula)
    (hj : j < σ₁.length) :
    Sat ι rate (σ₁ ++ τ) e vis v j φ ↔ Sat ι rate σ₁ e vis v j φ :=
  sat_congr φ v j fun _ hk =>
    ⟨List.getElem?_append_left (Nat.lt_of_le_of_lt hk hj), Iff.rfl⟩

end

/-- A wider `formerly` window holds whenever a narrower one does. -/
theorem sat_formerly_mono {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}
    {v : Valuation} {j : Nat} {w₁ w₂ : Window} {φ : Formula} (hw : w₁.seconds ≤ w₂.seconds) :
    Sat ι rate σ e vis v j (.formerly w₁ φ) → Sat ι rate σ e vis v j (.formerly w₂ φ) := by
  have hw' : w₁.ticks rate ≤ w₂.ticks rate :=
    Int.mul_le_mul_of_nonneg_right hw (Int.natCast_nonneg _)
  simp only [Sat, InWindow]
  rintro ⟨k, hk, hv, ⟨pj, pk, hpj, hpk, h₀, h₁⟩, hs⟩
  exact ⟨k, hk, hv, ⟨pj, pk, hpj, hpk, h₀, Int.le_trans h₁ hw'⟩, hs⟩

/-! ## Aggregates are well-defined -/

private theorem perm_of_nodup_of_mem_iff {α : Type} {l₁ l₂ : List α} (d₁ : l₁.Nodup)
    (d₂ : l₂.Nodup) (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.Perm l₂ :=
  (List.perm_ext_iff_of_nodup d₁ d₂).mpr h

private theorem perm_sum_int {l₁ l₂ : List Int} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => simp
  | cons _ _ ih => simp [ih]
  | swap => simpa [List.sum_cons] using Int.add_left_comm ..
  | trans _ _ ih₁ ih₂ => simp [ih₁, ih₂]

/-- An aggregate has at most one total. -/
theorem total_unique {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}
    {v : Valuation} {j : Nat} {a : Aggregate} {n m : Int}
    (hn : Total ι rate σ e vis v j a n) (hm : Total ι rate σ e vis v j a m) : n = m := by
  cases a with
  | count dom body =>
    obtain ⟨r₁, d₁, h₁, rfl⟩ := hn
    obtain ⟨r₂, d₂, h₂, rfl⟩ := hm
    have hp := perm_of_nodup_of_mem_iff d₁ d₂ fun row => (h₁ row).trans (h₂ row).symm
    rw [hp.length_eq]
  | sum s dom body =>
    obtain ⟨r₁, d₁, h₁, rfl⟩ := hn
    obtain ⟨r₂, d₂, h₂, rfl⟩ := hm
    have hp := perm_of_nodup_of_mem_iff d₁ d₂ fun row => (h₁ row).trans (h₂ row).symm
    exact perm_sum_int (hp.map _)

end Dogwood.Thm
