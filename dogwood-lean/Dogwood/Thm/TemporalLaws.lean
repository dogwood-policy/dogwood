import Dogwood.Thm.Temporal
import Dogwood.Spec.Temporal.Readings
import Dogwood.Thm.Monitorable

/-!
# Laws of the temporal operators

The temporal operators mean what their names say:

* **Windows are monotone** (`inWindow_mono`, `sat_previous_mono`, `sat_since_mono`, and
  `Formula.Widens.sat` in general, which subsumes `sat_formerly_mono`): widening a window in a
  positive position never makes a condition fail where it held. A `since` window bounds only the
  anchor, so the same anchor still witnesses it.
* **The present is in every non-negative window** (`sat_formerly_of_now`); on a trace whose
  timestamps strictly increase, a zero window sees only the present (`sat_formerly_zero_iff`).
* **`previous` is a `formerly`** (`sat_formerly_of_previous`), and **`formerly` is a `since`**
  whose left side always holds (`sat_since_iff_formerly`).
* **The step of `previous`** (`sat_previous_step`, `not_sat_previous_first`): `previous` reads the
  previous visible timepoint, and fails at the first one.
* **The expansion of `since`** (`sat_since_iff_anchor`, `sinceAnchor_step`, `sinceAnchor_first`,
  `sinceAnchor_invisible`, `inWindow_of_later`): the anchors of `φ since ψ` at a visible timepoint
  are the present, when `ψ` holds there, and, when `φ` holds there, the anchors at the previous
  visible timepoint. The window only filters the anchors, and on a trace whose timestamps never
  decrease a later anchor is in the window whenever an earlier one is, so it is enough to check
  the latest anchor. This is the recursion an incremental monitor computes, keeping only the latest
  anchor.
* **Nested `formerly` windows add up** (`sat_formerly_formerly`): `formerly within W₁ (formerly
  within W₂ φ)` implies `formerly within W φ` when `W₁ + W₂ ≤ W`. The converse fails on discrete
  time, since it needs a timepoint between the two. A nested condition can therefore see events
  older than any one of its windows: the validator's per-window cap does not bound how old an event
  that matters can be; the horizon (`Formula.horizon`, `Dogwood.Thm.sat_horizon`) does.
* **Aggregates** (`count_pos_iff`, `count_eq_zero_iff`, `count_mono`, `count_widens`,
  `sum_nonneg`, `sum_mono`, `sum_widens`): a count is positive exactly when some row satisfies its body; counting
  is monotone in the body, so widening a window in a positive position of the body never lowers a
  count; a sum of non-negative summands is non-negative and monotone in the body. These are about
  exact totals (`Total`), before any reading of out-of-range results. A count counts distinct rows
  of its `for` domain, not events: counting occurrences needs a domain variable restricted by
  `tp`.
* **Comparisons with aggregates** (`sat_cmp_agg_long`, `sat_agg_cmp_up_iff`,
  `sat_agg_cmp_down_iff`, `sat_count_cmp_mono_up`, `sat_count_cmp_mono_down`,
  `sat_count_cmp_widens`, `sat_count_cmp_narrows`, their `sum` forms, `sat_count_gt_zero_iff`,
  `sat_count_eq_zero_iff`, `sat_count_lt_rows`): the aggregate laws as comparisons a condition
  writes, through the reading of out-of-range totals. `≥` and `>` survive enlarging the body's
  rows, `<` and `≤` survive shrinking them, `count … < k` bounds every list of distinct rows; with
  `Int64.MAX` excluded as a threshold for `>` and `≤`. Widening keeps an aggregate safe
  (`Formula.Widens.safe_iff`), so the widened total exists (`count_total_of_widens`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

/-! ## Windows -/

theorem inWindow_mono {j k : Nat} {w₁ w₂ : Window} (hw : w₁.ticks rate ≤ w₂.ticks rate) :
    InWindow rate σ j k w₁ → InWindow rate σ j k w₂ := by
  rintro ⟨pj, pk, hpj, hpk, h₀, h₁⟩
  exact ⟨pj, pk, hpj, hpk, h₀, Int.le_trans h₁ hw⟩

/-- A wider `previous` window holds whenever a narrower one does. -/
theorem sat_previous_mono {v : Valuation} {j : Nat} {w₁ w₂ : Window} {φ : Formula}
    (hw : w₁.ticks rate ≤ w₂.ticks rate) :
    Sat ι rate σ e vis v j (.previous w₁ φ) → Sat ι rate σ e vis v j (.previous w₂ φ) := by
  simp only [Sat]
  rintro ⟨k, hk, hv, hlast, hin, hs⟩
  exact ⟨k, hk, hv, hlast, inWindow_mono hw hin, hs⟩

/-- **A wider `since` window holds whenever a narrower one does.** The window bounds only the
anchor: a wider window admits earlier anchors, but the anchor that witnessed the narrower one
still witnesses it. -/
theorem sat_since_mono {v : Valuation} {j : Nat} {w₁ w₂ : Window} {φ ψ : Formula}
    (hw : w₁.ticks rate ≤ w₂.ticks rate) :
    Sat ι rate σ e vis v j (.since φ w₁ ψ) → Sat ι rate σ e vis v j (.since φ w₂ ψ) := by
  simp only [Sat]
  rintro ⟨k, hk, hv, hin, hψ, hφ⟩
  exact ⟨k, hk, hv, inWindow_mono hw hin, hψ, hφ⟩

end Dogwood.Thm

namespace Dogwood.Spec.Temporal

open Dogwood.Thm

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

/-- `φ'` is `φ` with windows in positive positions widened: under `&&`, `exists`, and both sides
of `since`, and inside the temporal operators themselves. A negation, a comparison (and so an
aggregate), a predicate, and `tp` are left as they are. -/
inductive Formula.Widens (rate : TickRate) : Formula → Formula → Prop
  | refl (φ : Formula) : Formula.Widens rate φ φ
  | and {φ φ' ψ ψ' : Formula} :
      Formula.Widens rate φ φ' → Formula.Widens rate ψ ψ' →
      Formula.Widens rate (.and φ ψ) (.and φ' ψ')
  | exist (x : Binder) {φ φ' : Formula} :
      Formula.Widens rate φ φ' → Formula.Widens rate (.exist x φ) (.exist x φ')
  | formerly {w w' : Window} {φ φ' : Formula} :
      w.ticks rate ≤ w'.ticks rate → Formula.Widens rate φ φ' →
      Formula.Widens rate (.formerly w φ) (.formerly w' φ')
  | previous {w w' : Window} {φ φ' : Formula} :
      w.ticks rate ≤ w'.ticks rate → Formula.Widens rate φ φ' →
      Formula.Widens rate (.previous w φ) (.previous w' φ')
  | since {w w' : Window} {φ φ' ψ ψ' : Formula} :
      w.ticks rate ≤ w'.ticks rate → Formula.Widens rate φ φ' → Formula.Widens rate ψ ψ' →
      Formula.Widens rate (.since φ w ψ) (.since φ' w' ψ')

/-- **Widening windows in positive positions never makes a condition fail where it held.** -/
theorem Formula.Widens.sat {φ φ' : Formula} (h : Formula.Widens rate φ φ') :
    ∀ {v : Valuation} {j : Nat}, Sat ι rate σ e vis v j φ → Sat ι rate σ e vis v j φ' := by
  induction h with
  | refl => exact id
  | and _ _ ih₁ ih₂ =>
    intro v j hs
    simp only [Sat] at hs ⊢
    exact ⟨ih₁ hs.1, ih₂ hs.2⟩
  | exist x _ ih =>
    intro v j hs
    simp only [Sat] at hs ⊢
    obtain ⟨w, hw⟩ := hs
    exact ⟨w, ih hw⟩
  | formerly hw _ ih =>
    intro v j hs
    simp only [Sat] at hs ⊢
    obtain ⟨k, hk, hv, hin, hφ⟩ := hs
    exact ⟨k, hk, hv, inWindow_mono hw hin, ih hφ⟩
  | previous hw _ ih =>
    intro v j hs
    simp only [Sat] at hs ⊢
    obtain ⟨k, hk, hv, hlast, hin, hφ⟩ := hs
    exact ⟨k, hk, hv, hlast, inWindow_mono hw hin, ih hφ⟩
  | since hw _ _ ihφ ihψ =>
    intro v j hs
    simp only [Sat] at hs ⊢
    obtain ⟨k, hk, hv, hin, hψ, hφ⟩ := hs
    exact ⟨k, hk, hv, inWindow_mono hw hin, ihψ hψ, fun k' h₁ h₂ h₃ => ihφ (hφ k' h₁ h₂ h₃)⟩

end Dogwood.Spec.Temporal

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

/-! ## The present, and `previous` -/

/-- **The present is in every non-negative window.** -/
theorem sat_formerly_of_now {v : Valuation} {j : Nat} {w : Window} {φ : Formula}
    (hw : 0 ≤ w.ticks rate) (hj : j < σ.length) (hv : vis j)
    (h : Sat ι rate σ e vis v j φ) : Sat ι rate σ e vis v j (.formerly w φ) := by
  simp only [Sat]
  refine ⟨j, Nat.le_refl j, hv, ⟨σ[j], σ[j], List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hj, by simp, by simpa using hw⟩, h⟩

/-- **A zero window sees only the present**, on a trace whose timestamps strictly increase. -/
theorem sat_formerly_zero_iff {v : Valuation} {j : Nat} {w : Window} {φ : Formula}
    (hσ : Trace.StrictlyIncreasing σ) (hw : w.ticks rate = 0) (hj : j < σ.length) (hv : vis j) :
    Sat ι rate σ e vis v j (.formerly w φ) ↔ Sat ι rate σ e vis v j φ := by
  constructor
  · intro hs
    simp only [Sat] at hs
    obtain ⟨k, hk, _, ⟨pj, pk, hpj, hpk, h₀, h₁⟩, hφ⟩ := hs
    rcases Nat.lt_or_ge k j with hlt | hge
    · exfalso
      obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.mp hpk
      obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp hpj
      have := List.pairwise_iff_getElem.mp hσ k j hk' hj hlt
      omega
    · have : k = j := Nat.le_antisymm hk hge
      subst this
      exact hφ
  · exact sat_formerly_of_now (by omega) hj hv

/-- **`previous` is a `formerly`**: the previous visible timepoint is a visible timepoint in the
window. -/
theorem sat_formerly_of_previous {v : Valuation} {j : Nat} {w : Window} {φ : Formula} :
    Sat ι rate σ e vis v j (.previous w φ) → Sat ι rate σ e vis v j (.formerly w φ) := by
  simp only [Sat]
  rintro ⟨k, hk, hv, _, hin, hφ⟩
  exact ⟨k, Nat.le_of_lt hk, hv, hin, hφ⟩

/-- **The step of `previous`.** With `i` the previous visible timepoint before `j`, `previous`
holds at `j` exactly when `i` is in the window and `φ` held at `i`. -/
theorem sat_previous_step {v : Valuation} {w : Window} {φ : Formula} {i j : Nat} (hvi : vis i)
    (hij : i < j) (hgap : ∀ k', i < k' → k' < j → ¬ vis k') :
    Sat ι rate σ e vis v j (.previous w φ) ↔
      InWindow rate σ j i w ∧ Sat ι rate σ e vis v i φ := by
  simp only [Sat]
  constructor
  · rintro ⟨k, hk, hv, hlast, hin, hφ⟩
    have : k = i := by
      rcases Nat.lt_trichotomy k i with h | h | h
      · exact absurd hvi (hlast i h hij)
      · exact h
      · exact absurd hv (hgap k h hk)
    subst this
    exact ⟨hin, hφ⟩
  · rintro ⟨hin, hφ⟩
    exact ⟨i, hij, hvi, hgap, hin, hφ⟩

/-- **`previous` fails at the first visible timepoint.** -/
theorem not_sat_previous_first {v : Valuation} {w : Window} {φ : Formula} {j : Nat}
    (hnone : ∀ k' < j, ¬ vis k') : ¬ Sat ι rate σ e vis v j (.previous w φ) := by
  simp only [Sat]
  rintro ⟨k, hk, hv, -⟩
  exact hnone k hk hv

/-- **`formerly` is a `since` whose left side always holds.** -/
theorem sat_since_iff_formerly {v : Valuation} {j : Nat} {w : Window} {χ φ : Formula}
    (hχ : ∀ k ≤ j, vis k → Sat ι rate σ e vis v k χ) :
    Sat ι rate σ e vis v j (.since χ w φ) ↔ Sat ι rate σ e vis v j (.formerly w φ) := by
  simp only [Sat]
  constructor
  · rintro ⟨k, hk, hv, hin, hφ, -⟩
    exact ⟨k, hk, hv, hin, hφ⟩
  · rintro ⟨k, hk, hv, hin, hφ⟩
    exact ⟨k, hk, hv, hin, hφ, fun k' _ h₂ h₃ => hχ k' h₂ h₃⟩

/-! ## The expansion of `since` -/

variable (ι rate σ e vis) in
/-- `k` is an anchor of `φ since ψ` at `j`, whatever the window: a visible timepoint at or before
`j` where `ψ` holds, after which `φ` holds at every visible timepoint through `j`. -/
def SinceAnchor (v : Valuation) (φ ψ : Formula) (j k : Nat) : Prop :=
  k ≤ j ∧ vis k ∧ Sat ι rate σ e vis v k ψ ∧
    ∀ k', k < k' → k' ≤ j → vis k' → Sat ι rate σ e vis v k' φ

/-- **`since` is an anchor in the window.** -/
theorem sat_since_iff_anchor {v : Valuation} {j : Nat} {w : Window} {φ ψ : Formula} :
    Sat ι rate σ e vis v j (.since φ w ψ) ↔
      ∃ k, SinceAnchor ι rate σ e vis v φ ψ j k ∧ InWindow rate σ j k w := by
  simp only [Sat, SinceAnchor]
  constructor
  · rintro ⟨k, hk, hv, hin, hψ, hφ⟩
    exact ⟨k, ⟨hk, hv, hψ, hφ⟩, hin⟩
  · rintro ⟨k, ⟨hk, hv, hψ, hφ⟩, hin⟩
    exact ⟨k, hk, hv, hin, hψ, hφ⟩

/-- **The step of `since`.** At a visible timepoint `j`, with no visible timepoint strictly
between `i` and `j` (so `i` is the previous visible timepoint, if `i` is visible), the anchors are
`j` itself, when `ψ` holds there, and, when `φ` holds there, the anchors at `i`. -/
theorem sinceAnchor_step {v : Valuation} {φ ψ : Formula} {i j k : Nat} (hvj : vis j)
    (hij : i < j) (hgap : ∀ k', i < k' → k' < j → ¬ vis k') :
    SinceAnchor ι rate σ e vis v φ ψ j k ↔
      (k = j ∧ Sat ι rate σ e vis v j ψ) ∨
        (Sat ι rate σ e vis v j φ ∧ SinceAnchor ι rate σ e vis v φ ψ i k) := by
  constructor
  · rintro ⟨hkj, hvk, hψ, hφ⟩
    rcases Nat.lt_or_ge k j with hlt | hge
    · have hki : k ≤ i := by
        rcases Nat.lt_or_ge i k with h | h
        · exact absurd hvk (hgap k h hlt)
        · exact h
      exact .inr ⟨hφ j hlt (Nat.le_refl j) hvj,
        ⟨hki, hvk, hψ, fun k' h₁ h₂ h₃ => hφ k' h₁ (by omega) h₃⟩⟩
    · have : k = j := Nat.le_antisymm hkj hge
      subst this
      exact .inl ⟨rfl, hψ⟩
  · rintro (⟨rfl, hψ⟩ | ⟨hφj, hki, hvk, hψ, hφ⟩)
    · exact ⟨Nat.le_refl k, hvj, hψ, fun k' h₁ h₂ _ => absurd (Nat.lt_of_lt_of_le h₁ h₂)
        (Nat.lt_irrefl k)⟩
    · refine ⟨by omega, hvk, hψ, fun k' h₁ h₂ h₃ => ?_⟩
      rcases Nat.lt_or_ge k' j with hlt | hge
      · have hk'i : k' ≤ i := by
          rcases Nat.lt_or_ge i k' with h | h
          · exact absurd h₃ (hgap k' h hlt)
          · exact h
        exact hφ k' h₁ hk'i h₃
      · have : k' = j := Nat.le_antisymm h₂ hge
        subst this
        exact hφj

/-- **The first visible timepoint.** With no visible timepoint before `j`, its only anchor is
`j` itself, when `ψ` holds there. -/
theorem sinceAnchor_first {v : Valuation} {φ ψ : Formula} {j k : Nat} (hvj : vis j)
    (hnone : ∀ k' < j, ¬ vis k') :
    SinceAnchor ι rate σ e vis v φ ψ j k ↔ k = j ∧ Sat ι rate σ e vis v j ψ := by
  constructor
  · rintro ⟨hkj, hvk, hψ, _⟩
    rcases Nat.lt_or_ge k j with hlt | hge
    · exact absurd hvk (hnone k hlt)
    · have : k = j := Nat.le_antisymm hkj hge
      subst this
      exact ⟨rfl, hψ⟩
  · rintro ⟨rfl, hψ⟩
    exact ⟨Nat.le_refl k, hvj, hψ, fun k' h₁ h₂ _ => absurd (Nat.lt_of_lt_of_le h₁ h₂)
      (Nat.lt_irrefl k)⟩

/-- **An invisible timepoint changes no anchor.** If `j` is not visible and `i` is the previous
visible timepoint, the anchors at `j` are the anchors at `i`. -/
theorem sinceAnchor_invisible {v : Valuation} {φ ψ : Formula} {i j k : Nat} (hvj : ¬ vis j)
    (hij : i < j) (hgap : ∀ k', i < k' → k' < j → ¬ vis k') :
    SinceAnchor ι rate σ e vis v φ ψ j k ↔ SinceAnchor ι rate σ e vis v φ ψ i k := by
  have hle : ∀ k', k' ≤ j → vis k' → k' ≤ i := fun k' hk' hv => by
    rcases Nat.lt_or_ge i k' with h | h
    · rcases Nat.lt_or_ge k' j with h' | h'
      · exact absurd hv (hgap k' h h')
      · have : k' = j := Nat.le_antisymm hk' h'
        subst this
        exact absurd hv hvj
    · exact h
  constructor
  · rintro ⟨hkj, hvk, hψ, hφ⟩
    exact ⟨hle k hkj hvk, hvk, hψ, fun k' h₁ h₂ h₃ => hφ k' h₁ (by omega) h₃⟩
  · rintro ⟨hki, hvk, hψ, hφ⟩
    exact ⟨by omega, hvk, hψ, fun k' h₁ h₂ h₃ => hφ k' h₁ (hle k' h₂ h₃) h₃⟩

/-- **Only the latest anchor needs the window check.** On a trace whose timestamps never decrease,
a later timepoint is in the window whenever an earlier one is: if some anchor of `φ since ψ` is in
the window, so is the latest. -/
theorem inWindow_of_later (hσ : Trace.Nondecreasing σ) {j k₁ k₂ : Nat} {w : Window}
    (h₁₂ : k₁ ≤ k₂) (h₂ : k₂ ≤ j) (h : InWindow rate σ j k₁ w) : InWindow rate σ j k₂ w := by
  obtain ⟨pj, pk, hpj, hpk, h₀, h₁⟩ := h
  have hj : j < σ.length := (List.getElem?_eq_some_iff.mp hpj).1
  have hk₂ : k₂ < σ.length := by omega
  obtain ⟨hk₁, rfl⟩ := List.getElem?_eq_some_iff.mp hpk
  obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp hpj
  have mono : ∀ a b (ha : a < σ.length) (hb : b < σ.length), a ≤ b → σ[a].ts ≤ σ[b].ts := by
    intro a b ha hb hab
    rcases Nat.lt_or_ge a b with hlt | hge
    · exact List.pairwise_iff_getElem.mp hσ a b ha hb hlt
    · have : a = b := by omega
      subst this
      exact Int.le_refl _
  have := mono k₁ k₂ hk₁ hk₂ h₁₂
  have := mono k₂ j hk₂ hj h₂
  exact ⟨σ[j], σ[k₂], List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hk₂, by omega,
    by omega⟩

/-! ## Nested windows -/

/-- **Nested `formerly` windows add up.** The converse fails on discrete time: an event within
`W₁ + W₂` need not have a timepoint between it and the present that is within `W₁` of the one and
`W₂` of the other. -/
theorem sat_formerly_formerly {v : Valuation} {j : Nat} {w₁ w₂ w : Window} {φ : Formula}
    (hw : w₁.ticks rate + w₂.ticks rate ≤ w.ticks rate) :
    Sat ι rate σ e vis v j (.formerly w₁ (.formerly w₂ φ)) →
      Sat ι rate σ e vis v j (.formerly w φ) := by
  simp only [Sat]
  rintro ⟨k, hk, _, ⟨pj, pk, hpj, hpk, h₀, h₁⟩, m, hm, hvm, ⟨pk', pm, hpk', hpm, h₂, h₃⟩, hφ⟩
  rw [hpk] at hpk'
  cases hpk'
  exact ⟨m, Nat.le_trans hm hk, hvm, ⟨pj, pm, hpj, hpm, by omega, by omega⟩, hφ⟩

/-! ## Aggregates -/

/-- **A count is positive exactly when some row satisfies its body.** -/
theorem count_pos_iff {v : Valuation} {j : Nat} {dom : List Binder} {body : Formula} {n : Int}
    (hT : Total ι rate σ e vis v j (.count dom body) n) :
    0 < n ↔ ∃ row : List TVal, row.length = (domainNames dom).length ∧
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body := by
  obtain ⟨rows, _, hmem, rfl⟩ := hT
  constructor
  · intro h
    obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos (by omega : 0 < rows.length)
    exact ⟨r, (hmem r).mp hr⟩
  · rintro ⟨r, hr⟩
    have := List.length_pos_of_mem ((hmem r).mpr hr)
    omega

/-- **A count is zero exactly when no row satisfies its body.** -/
theorem count_eq_zero_iff {v : Valuation} {j : Nat} {dom : List Binder} {body : Formula} {n : Int}
    (hT : Total ι rate σ e vis v j (.count dom body) n) :
    n = 0 ↔ ∀ row : List TVal, row.length = (domainNames dom).length →
      ¬ Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body := by
  have hpos := count_pos_iff hT
  have hnn : 0 ≤ n := by
    obtain ⟨rows, _, _, rfl⟩ := hT
    omega
  constructor
  · intro h0 row hl hs
    have := hpos.mpr ⟨row, hl, hs⟩
    omega
  · intro hnone
    rcases Int.lt_or_le 0 n with h | h
    · obtain ⟨row, hl, hs⟩ := hpos.mp h
      exact absurd hs (hnone row hl)
    · omega

/-- **Counting is monotone in the body.** If every row of `body₁` is a row of `body₂`, the first
count is at most the second. -/
theorem count_mono {v : Valuation} {j : Nat} {dom : List Binder} {body₁ body₂ : Formula}
    {n₁ n₂ : Int}
    (h : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₁ →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂)
    (h₁ : Total ι rate σ e vis v j (.count dom body₁) n₁)
    (h₂ : Total ι rate σ e vis v j (.count dom body₂) n₂) : n₁ ≤ n₂ := by
  obtain ⟨rows₁, d₁, m₁, rfl⟩ := h₁
  obtain ⟨rows₂, _, m₂, rfl⟩ := h₂
  have hsub : rows₁ ⊆ rows₂ := fun r hr => by
    obtain ⟨hl, hs⟩ := (m₁ r).mp hr
    exact (m₂ r).mpr ⟨hl, h r hl hs⟩
  have := (List.subperm_of_subset d₁ hsub).length_le
  omega

/-- **Widening windows in positive positions of a count's body never lowers the count.** -/
theorem count_widens {v : Valuation} {j : Nat} {dom : List Binder} {body body' : Formula}
    {n n' : Int} (hW : Formula.Widens rate body body')
    (h₁ : Total ι rate σ e vis v j (.count dom body) n)
    (h₂ : Total ι rate σ e vis v j (.count dom body') n') : n ≤ n' :=
  count_mono (fun _ _ hs => hW.sat hs) h₁ h₂

private theorem sum_nonneg_of {l : List Int} (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons]
    have := h a (by simp)
    have := ih fun x hx => h x (by simp [hx])
    omega

private theorem sum_perm {l₁ l₂ : List Int} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => simp
  | cons _ _ ih => simp [ih]
  | swap => simpa [List.sum_cons] using Int.add_left_comm ..
  | trans _ _ ih₁ ih₂ => simp [ih₁, ih₂]

private theorem sum_sublist_le {l₁ l₂ : List Int} (h : l₁.Sublist l₂) (hnn : ∀ x ∈ l₂, 0 ≤ x) :
    l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => simp
  | cons a _ ih =>
    simp only [List.sum_cons]
    have := hnn a (by simp)
    have := ih fun x hx => hnn x (by simp [hx])
    omega
  | cons_cons a _ ih =>
    simp only [List.sum_cons]
    have := ih fun x hx => hnn x (by simp [hx])
    omega

/-- **A sum of non-negative summands is non-negative.** -/
theorem sum_nonneg {v : Valuation} {j : Nat} {s : VarName} {dom : List Binder} {body : Formula}
    {n : Int}
    (h : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body →
      0 ≤ summand s (domainNames dom) row)
    (hT : Total ι rate σ e vis v j (.sum s dom body) n) : 0 ≤ n := by
  obtain ⟨rows, _, hmem, rfl⟩ := hT
  apply sum_nonneg_of
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hl, hs⟩ := (hmem r).mp hr
  exact h r hl hs

/-- **Sums of non-negative summands are monotone in the body.** If every row of `body₁` is a row
of `body₂`, and the rows of `body₂` have non-negative summands, the first sum is at most the
second. -/
theorem sum_mono {v : Valuation} {j : Nat} {s : VarName} {dom : List Binder}
    {body₁ body₂ : Formula} {n₁ n₂ : Int}
    (h : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₁ →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂)
    (hnn : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂ →
      0 ≤ summand s (domainNames dom) row)
    (h₁ : Total ι rate σ e vis v j (.sum s dom body₁) n₁)
    (h₂ : Total ι rate σ e vis v j (.sum s dom body₂) n₂) : n₁ ≤ n₂ := by
  obtain ⟨rows₁, d₁, m₁, rfl⟩ := h₁
  obtain ⟨rows₂, _, m₂, rfl⟩ := h₂
  have hsub : rows₁ ⊆ rows₂ := fun r hr => by
    obtain ⟨hl, hs⟩ := (m₁ r).mp hr
    exact (m₂ r).mpr ⟨hl, h r hl hs⟩
  obtain ⟨l, hperm, hsl⟩ := List.subperm_of_subset d₁ hsub
  rw [← sum_perm (hperm.map (summand s (domainNames dom)))]
  apply sum_sublist_le (hsl.map _)
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hl, hs⟩ := (m₂ r).mp hr
  exact hnn r hl hs

/-- **Widening windows in positive positions of a sum's body never lowers the sum**, when the
summands of the widened body's rows are non-negative. -/
theorem sum_widens {v : Valuation} {j : Nat} {s : VarName} {dom : List Binder}
    {body body' : Formula} {n n' : Int} (hW : Formula.Widens rate body body')
    (hnn : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body' →
      0 ≤ summand s (domainNames dom) row)
    (h₁ : Total ι rate σ e vis v j (.sum s dom body) n)
    (h₂ : Total ι rate σ e vis v j (.sum s dom body') n') : n ≤ n' :=
  sum_mono (fun _ _ hs => hW.sat hs) hnn h₁ h₂

/-! ## Comparisons with aggregates

The aggregate laws, at the level of the comparisons a condition writes. An aggregate compared with
a `Long` literal holds when its exact total, read by the reading `ι` (`readLong`), compares with
the literal (`sat_cmp_agg_long`). For an aggregate whose totals are never negative, as a count's
are and a sum's of non-negative summands, only the top of the `Long` range matters, and the
comparison is a comparison of the exact total (`sat_agg_cmp_up_iff`, `sat_agg_cmp_down_iff`):
`≥ k` and `> k` under a total admissible reading, `< k` and `≤ k` under any admissible reading,
for every `k` in `≥` and `<`, and for `k` below `Int64.MAX` in `>` and `≤`. At `Int64.MAX` itself
an admissible reading may read a larger total lower than a smaller one. So the monotonicity of
counts and sums carries over: `≥` and `>` survive enlarging the body's rows, widening windows in
positive positions in particular, and `<` and `≤` survive shrinking them, the direction of a rate
limit (`sat_count_cmp_mono_up`, `sat_count_cmp_mono_down`, their `sum` forms, and the `Widens`
forms `sat_count_cmp_widens`, `sat_count_cmp_narrows`, …). A comparison `count … < k` bounds every
list of distinct rows of the body (`sat_count_lt_rows`).

The upward lifts need the other aggregate's total to exist; for a safe aggregate it does, and
widening keeps an aggregate safe (`Formula.Widens.safe_iff`, `count_total_of_widens`). The
downward lifts need nothing: the smaller total is a filter of the larger (`count_total_of_sub`).
Under a reading that reports errors, a decision is that of every total completion of the reading,
or fails closed (`Dogwood.Thm.authorize_dichotomy`), so the upward lifts apply to each completion.
-/

private theorem readLong_num {f : Int → Option Int} {n : Int} {x : CVal}
    (h : readLong f n = some x) : ∃ m, x = .num m := by
  unfold readLong at h
  split at h
  · simp only [Option.some.injEq] at h
    exact ⟨n, h.symm⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨m, _, rfl⟩ := h
    exact ⟨m, rfl⟩

private theorem readLong_of_total {f : Int → Option Int} (ht : ∀ n, (f n).isSome = true)
    (n : Int) : ∃ m, readLong f n = some (.num m) := by
  unfold readLong
  split
  · exact ⟨n, rfl⟩
  · cases hf : f n with
    | none =>
      have := ht n
      rw [hf] at this
      cases this
    | some m => exact ⟨m, by simp⟩

private theorem readLong_in {f : Int → Option Int} {n : Int} (h₀ : Int64.MIN ≤ n)
    (h₁ : n ≤ Int64.MAX) : readLong f n = some (.num n) := by
  unfold readLong
  simp [h₀, h₁]

/-- What a side-preserving reading reads an exact result `n` as: `n` itself in range, at least
`Int64.MAX` above it, at most `Int64.MIN` below it. -/
private theorem readLong_cases {f : Int → Option Int} (hf : SidePreserving f) {n m : Int}
    (h : readLong f n = some (.num m)) :
    (Int64.MIN ≤ n ∧ n ≤ Int64.MAX ∧ m = n) ∨ (Int64.MAX < n ∧ Int64.MAX ≤ m) ∨
      (n < Int64.MIN ∧ m ≤ Int64.MIN) := by
  unfold readLong at h
  split at h
  · rename_i hin
    simp only [Option.some.injEq, CVal.num.injEq] at h
    exact .inl ⟨hin.1, hin.2, h.symm⟩
  · rename_i hn
    simp only [Option.map_eq_some_iff, CVal.num.injEq] at h
    obtain ⟨m', hm', rfl⟩ := h
    have hs := hf n m' hm'
    simp only [Int64.MIN, Int64.MAX] at hs hn ⊢
    by_cases h : 9223372036854775807 < n
    · exact .inr (.inl ⟨h, hs.1 h⟩)
    · exact .inr (.inr ⟨by omega, hs.2 (by omega)⟩)

/-- **An aggregate compared with a `Long` literal** holds exactly when its exact total, read by the
reading, compares with the literal. -/
theorem sat_cmp_agg_long {v : Valuation} {j : Nat} {op : CmpOp} {a : Aggregate} {c : Int64} :
    Sat ι rate σ e vis v j (.cmp op (.agg a) (.long c)) ↔
      ∃ n m, Total ι rate σ e vis v j a n ∧ readLong ι.outOfRange n = some (.num m) ∧
        op.Holds (.num m) (.num c.toInt) := by
  simp only [Sat, Denotes, Term.eval?, ImplChoices.aggregateValue]
  constructor
  · rintro ⟨x, y, ⟨n, hn, hx⟩, ⟨w, hw, rfl⟩, hop⟩
    simp only [Option.some.injEq] at hw
    subst hw
    obtain ⟨m, rfl⟩ := readLong_num hx
    exact ⟨n, m, hn, hx, hop⟩
  · rintro ⟨n, m, hn, hm, hop⟩
    exact ⟨.num m, .num c.toInt, ⟨n, hn, hm⟩, ⟨.val (.prim (.int c)), rfl, rfl⟩, hop⟩

/-- **`≥ k` and `> k` compare the exact total**, for an aggregate whose totals are never negative,
under a total admissible reading (`> k` for `k` below `Int64.MAX`). -/
theorem sat_agg_cmp_up_iff (hadm : ι.Admissible) (htot : ι.Total) {v : Valuation} {j : Nat}
    {a : Aggregate} (hnn : ∀ n, Total ι rate σ e vis v j a n → 0 ≤ n) {op : CmpOp} {c : Int64}
    (hop : op = .ge ∨ (op = .gt ∧ c.toInt < Int64.MAX)) :
    Sat ι rate σ e vis v j (.cmp op (.agg a) (.long c)) ↔
      ∃ n, Total ι rate σ e vis v j a n ∧ op.Holds (.num n) (.num c.toInt) := by
  have hc₁ := Int64.le_toInt c
  have hc₂ := Int64.toInt_lt c
  rw [sat_cmp_agg_long]
  constructor
  · rintro ⟨n, m, hn, hm, hh⟩
    refine ⟨n, hn, ?_⟩
    have h₀ := hnn n hn
    have cs := readLong_cases hadm.aggregate hm
    simp only [Int64.MIN, Int64.MAX] at cs hop
    rcases hop with rfl | ⟨rfl, hc⟩ <;> simp only [CmpOp.Holds] at hh ⊢ <;> omega
  · rintro ⟨n, hn, hh⟩
    obtain ⟨m, hm⟩ := readLong_of_total htot.aggregate n
    refine ⟨n, m, hn, hm, ?_⟩
    have h₀ := hnn n hn
    have cs := readLong_cases hadm.aggregate hm
    simp only [Int64.MIN, Int64.MAX] at cs hop
    rcases hop with rfl | ⟨rfl, hc⟩ <;> simp only [CmpOp.Holds] at hh ⊢ <;> omega

/-- **`< k` and `≤ k` compare the exact total**, for an aggregate whose totals are never negative,
under any admissible reading (`≤ k` for `k` below `Int64.MAX`): such a total is then in range. -/
theorem sat_agg_cmp_down_iff (hadm : ι.Admissible) {v : Valuation} {j : Nat} {a : Aggregate}
    (hnn : ∀ n, Total ι rate σ e vis v j a n → 0 ≤ n) {op : CmpOp} {c : Int64}
    (hop : op = .lt ∨ (op = .le ∧ c.toInt < Int64.MAX)) :
    Sat ι rate σ e vis v j (.cmp op (.agg a) (.long c)) ↔
      ∃ n, Total ι rate σ e vis v j a n ∧ op.Holds (.num n) (.num c.toInt) := by
  have hc₁ := Int64.le_toInt c
  have hc₂ := Int64.toInt_lt c
  rw [sat_cmp_agg_long]
  constructor
  · rintro ⟨n, m, hn, hm, hh⟩
    refine ⟨n, hn, ?_⟩
    have h₀ := hnn n hn
    have cs := readLong_cases hadm.aggregate hm
    simp only [Int64.MIN, Int64.MAX] at cs hop
    rcases hop with rfl | ⟨rfl, hc⟩ <;> simp only [CmpOp.Holds] at hh ⊢ <;> omega
  · rintro ⟨n, hn, hh⟩
    have h₀ := hnn n hn
    have hin : n ≤ Int64.MAX := by
      simp only [Int64.MAX] at hop ⊢
      rcases hop with rfl | ⟨rfl, hc⟩ <;> simp only [CmpOp.Holds] at hh <;> omega
    exact ⟨n, n, hn, readLong_in (by simp only [Int64.MIN]; omega) hin, hh⟩

private theorem count_total_nonneg {v : Valuation} {j : Nat} {dom : List Binder} {body : Formula}
    {n : Int} (hT : Total ι rate σ e vis v j (.count dom body) n) : 0 ≤ n := by
  obtain ⟨rows, _, _, rfl⟩ := hT
  omega

/-- A count whose body's rows are among another's has a total: the other's rows, filtered. -/
theorem count_total_of_sub {v : Valuation} {j : Nat} {dom : List Binder} {body₁ body₂ : Formula}
    {n₂ : Int}
    (h : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₁ →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂)
    (h₂ : Total ι rate σ e vis v j (.count dom body₂) n₂) :
    ∃ n₁, Total ι rate σ e vis v j (.count dom body₁) n₁ := by
  classical
  obtain ⟨rows, hd, hm, -⟩ := h₂
  refine ⟨_, rows.filter fun r =>
      decide (Sat ι rate σ e vis (v.bindAll (domainNames dom) r) j body₁),
    hd.sublist List.filter_sublist, fun row => ?_, rfl⟩
  simp only [List.mem_filter, decide_eq_true_eq, hm]
  exact ⟨fun ⟨⟨hl, _⟩, hs⟩ => ⟨hl, hs⟩, fun ⟨hl, hs⟩ => ⟨⟨hl, h row hl hs⟩, hs⟩⟩

/-- A sum whose body's rows are among another's has a total: the other's rows, filtered. -/
theorem sum_total_of_sub {v : Valuation} {j : Nat} {s : VarName} {dom : List Binder}
    {body₁ body₂ : Formula} {n₂ : Int}
    (h : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₁ →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂)
    (h₂ : Total ι rate σ e vis v j (.sum s dom body₂) n₂) :
    ∃ n₁, Total ι rate σ e vis v j (.sum s dom body₁) n₁ := by
  classical
  obtain ⟨rows, hd, hm, -⟩ := h₂
  refine ⟨_, rows.filter fun r =>
      decide (Sat ι rate σ e vis (v.bindAll (domainNames dom) r) j body₁),
    hd.sublist List.filter_sublist, fun row => ?_, rfl⟩
  simp only [List.mem_filter, decide_eq_true_eq, hm]
  exact ⟨fun ⟨⟨hl, _⟩, hs⟩ => ⟨hl, hs⟩, fun ⟨hl, hs⟩ => ⟨⟨hl, h row hl hs⟩, hs⟩⟩

/-- **`count … ≥ k` survives enlarging the body's rows**, and so does `count … > k` for `k` below
`Int64.MAX`, under a total admissible reading. -/
theorem sat_count_cmp_mono_up (hadm : ι.Admissible) (htot : ι.Total) {v : Valuation} {j : Nat}
    {dom : List Binder} {body₁ body₂ : Formula}
    (h : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₁ →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂)
    (hT₂ : ∃ n₂, Total ι rate σ e vis v j (.count dom body₂) n₂) {op : CmpOp} {c : Int64}
    (hop : op = .ge ∨ (op = .gt ∧ c.toInt < Int64.MAX)) :
    Sat ι rate σ e vis v j (.cmp op (.agg (.count dom body₁)) (.long c)) →
      Sat ι rate σ e vis v j (.cmp op (.agg (.count dom body₂)) (.long c)) := by
  rw [sat_agg_cmp_up_iff hadm htot (fun _ => count_total_nonneg) hop,
    sat_agg_cmp_up_iff hadm htot (fun _ => count_total_nonneg) hop]
  rintro ⟨n₁, hn₁, hh⟩
  obtain ⟨n₂, hn₂⟩ := hT₂
  have := count_mono h hn₁ hn₂
  refine ⟨n₂, hn₂, ?_⟩
  rcases hop with rfl | ⟨rfl, _⟩ <;> simp only [CmpOp.Holds] at hh ⊢ <;> omega

/-- **`count … < k` survives shrinking the body's rows**, and so does `count … ≤ k` for `k` below
`Int64.MAX`, under any admissible reading. This is the direction of a rate limit. -/
theorem sat_count_cmp_mono_down (hadm : ι.Admissible) {v : Valuation} {j : Nat}
    {dom : List Binder} {body₁ body₂ : Formula}
    (h : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₁ →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂) {op : CmpOp} {c : Int64}
    (hop : op = .lt ∨ (op = .le ∧ c.toInt < Int64.MAX)) :
    Sat ι rate σ e vis v j (.cmp op (.agg (.count dom body₂)) (.long c)) →
      Sat ι rate σ e vis v j (.cmp op (.agg (.count dom body₁)) (.long c)) := by
  rw [sat_agg_cmp_down_iff hadm (fun _ => count_total_nonneg) hop,
    sat_agg_cmp_down_iff hadm (fun _ => count_total_nonneg) hop]
  rintro ⟨n₂, hn₂, hh⟩
  obtain ⟨n₁, hn₁⟩ := count_total_of_sub h hn₂
  have := count_mono h hn₁ hn₂
  refine ⟨n₁, hn₁, ?_⟩
  rcases hop with rfl | ⟨rfl, _⟩ <;> simp only [CmpOp.Holds] at hh ⊢ <;> omega

/-- **`sum … ≥ k` survives enlarging the body's rows**, and so does `sum … > k` for `k` below
`Int64.MAX`, under a total admissible reading, when the larger body's rows have non-negative
summands. -/
theorem sat_sum_cmp_mono_up (hadm : ι.Admissible) (htot : ι.Total) {v : Valuation} {j : Nat}
    {s : VarName} {dom : List Binder} {body₁ body₂ : Formula}
    (h : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₁ →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂)
    (hnn : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂ →
      0 ≤ summand s (domainNames dom) row)
    (hT₂ : ∃ n₂, Total ι rate σ e vis v j (.sum s dom body₂) n₂) {op : CmpOp} {c : Int64}
    (hop : op = .ge ∨ (op = .gt ∧ c.toInt < Int64.MAX)) :
    Sat ι rate σ e vis v j (.cmp op (.agg (.sum s dom body₁)) (.long c)) →
      Sat ι rate σ e vis v j (.cmp op (.agg (.sum s dom body₂)) (.long c)) := by
  rw [sat_agg_cmp_up_iff hadm htot
      (fun _ => sum_nonneg fun row hl hs => hnn row hl (h row hl hs)) hop,
    sat_agg_cmp_up_iff hadm htot (fun _ => sum_nonneg hnn) hop]
  rintro ⟨n₁, hn₁, hh⟩
  obtain ⟨n₂, hn₂⟩ := hT₂
  have := sum_mono h hnn hn₁ hn₂
  refine ⟨n₂, hn₂, ?_⟩
  rcases hop with rfl | ⟨rfl, _⟩ <;> simp only [CmpOp.Holds] at hh ⊢ <;> omega

/-- **`sum … < k` survives shrinking the body's rows**, and so does `sum … ≤ k` for `k` below
`Int64.MAX`, under any admissible reading, when the larger body's rows have non-negative
summands. -/
theorem sat_sum_cmp_mono_down (hadm : ι.Admissible) {v : Valuation} {j : Nat} {s : VarName}
    {dom : List Binder} {body₁ body₂ : Formula}
    (h : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₁ →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂)
    (hnn : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body₂ →
      0 ≤ summand s (domainNames dom) row) {op : CmpOp} {c : Int64}
    (hop : op = .lt ∨ (op = .le ∧ c.toInt < Int64.MAX)) :
    Sat ι rate σ e vis v j (.cmp op (.agg (.sum s dom body₂)) (.long c)) →
      Sat ι rate σ e vis v j (.cmp op (.agg (.sum s dom body₁)) (.long c)) := by
  rw [sat_agg_cmp_down_iff hadm (fun _ => sum_nonneg hnn) hop,
    sat_agg_cmp_down_iff hadm
      (fun _ => sum_nonneg fun row hl hs => hnn row hl (h row hl hs)) hop]
  rintro ⟨n₂, hn₂, hh⟩
  obtain ⟨n₁, hn₁⟩ := sum_total_of_sub h hn₂
  have := sum_mono h hnn hn₁ hn₂
  refine ⟨n₁, hn₁, ?_⟩
  rcases hop with rfl | ⟨rfl, _⟩ <;> simp only [CmpOp.Holds] at hh ⊢ <;> omega

/-- **`count … ≥ k` survives widening**, and so does `count … > k` for `k` below `Int64.MAX`, under
a total admissible reading: widening windows in positive positions of the body never makes the
comparison fail. -/
theorem sat_count_cmp_widens (hadm : ι.Admissible) (htot : ι.Total) {v : Valuation} {j : Nat}
    {dom : List Binder} {body body' : Formula} (hW : Formula.Widens rate body body')
    (hT' : ∃ n', Total ι rate σ e vis v j (.count dom body') n') {op : CmpOp} {c : Int64}
    (hop : op = .ge ∨ (op = .gt ∧ c.toInt < Int64.MAX)) :
    Sat ι rate σ e vis v j (.cmp op (.agg (.count dom body)) (.long c)) →
      Sat ι rate σ e vis v j (.cmp op (.agg (.count dom body')) (.long c)) :=
  sat_count_cmp_mono_up hadm htot (fun _ _ hs => hW.sat hs) hT' hop

/-- **`count … < k` survives narrowing**, and so does `count … ≤ k` for `k` below `Int64.MAX`,
under any admissible reading: if the comparison holds with windows widened in positive positions
of the body, it holds for the body. This is the direction of a rate limit. -/
theorem sat_count_cmp_narrows (hadm : ι.Admissible) {v : Valuation} {j : Nat}
    {dom : List Binder} {body body' : Formula} (hW : Formula.Widens rate body body')
    {op : CmpOp} {c : Int64} (hop : op = .lt ∨ (op = .le ∧ c.toInt < Int64.MAX)) :
    Sat ι rate σ e vis v j (.cmp op (.agg (.count dom body')) (.long c)) →
      Sat ι rate σ e vis v j (.cmp op (.agg (.count dom body)) (.long c)) :=
  sat_count_cmp_mono_down hadm (fun _ _ hs => hW.sat hs) hop

/-- **`sum … ≥ k` survives widening**, and so does `sum … > k` for `k` below `Int64.MAX`, under a
total admissible reading, when the summands of the widened body's rows are non-negative. -/
theorem sat_sum_cmp_widens (hadm : ι.Admissible) (htot : ι.Total) {v : Valuation} {j : Nat}
    {s : VarName} {dom : List Binder} {body body' : Formula} (hW : Formula.Widens rate body body')
    (hnn : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body' →
      0 ≤ summand s (domainNames dom) row)
    (hT' : ∃ n', Total ι rate σ e vis v j (.sum s dom body') n') {op : CmpOp} {c : Int64}
    (hop : op = .ge ∨ (op = .gt ∧ c.toInt < Int64.MAX)) :
    Sat ι rate σ e vis v j (.cmp op (.agg (.sum s dom body)) (.long c)) →
      Sat ι rate σ e vis v j (.cmp op (.agg (.sum s dom body')) (.long c)) :=
  sat_sum_cmp_mono_up hadm htot (fun _ _ hs => hW.sat hs) hnn hT' hop

/-- **`sum … < k` survives narrowing**, and so does `sum … ≤ k` for `k` below `Int64.MAX`, under any
admissible reading, when the summands of the widened body's rows are non-negative. -/
theorem sat_sum_cmp_narrows (hadm : ι.Admissible) {v : Valuation} {j : Nat} {s : VarName}
    {dom : List Binder} {body body' : Formula} (hW : Formula.Widens rate body body')
    (hnn : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body' →
      0 ≤ summand s (domainNames dom) row) {op : CmpOp} {c : Int64}
    (hop : op = .lt ∨ (op = .le ∧ c.toInt < Int64.MAX)) :
    Sat ι rate σ e vis v j (.cmp op (.agg (.sum s dom body')) (.long c)) →
      Sat ι rate σ e vis v j (.cmp op (.agg (.sum s dom body)) (.long c)) :=
  sat_sum_cmp_mono_down hadm (fun _ _ hs => hW.sat hs) hnn hop

/-- **`count … > 0` holds exactly when some row satisfies the body**, under a total admissible
reading. -/
theorem sat_count_gt_zero_iff (hadm : ι.Admissible) (htot : ι.Total) {v : Valuation} {j : Nat}
    {dom : List Binder} {body : Formula} {n : Int}
    (hT : Total ι rate σ e vis v j (.count dom body) n) :
    Sat ι rate σ e vis v j (.cmp .gt (.agg (.count dom body)) (.long 0)) ↔
      ∃ row : List TVal, row.length = (domainNames dom).length ∧
        Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body := by
  have hz : (0 : Int64).toInt = 0 := by decide
  rw [sat_agg_cmp_up_iff hadm htot (fun _ => count_total_nonneg)
    (.inr ⟨rfl, by simp [hz, Int64.MAX]⟩), ← count_pos_iff hT]
  constructor
  · rintro ⟨n₀, hn₀, hh⟩
    have := total_unique hn₀ hT
    subst this
    simpa [CmpOp.Holds, hz] using hh
  · intro hpos
    exact ⟨n, hT, by simpa [CmpOp.Holds, hz] using hpos⟩

/-- **`count … == 0` holds exactly when no row satisfies the body**, under any admissible
reading. -/
theorem sat_count_eq_zero_iff (hadm : ι.Admissible) {v : Valuation} {j : Nat}
    {dom : List Binder} {body : Formula} {n : Int}
    (hT : Total ι rate σ e vis v j (.count dom body) n) :
    Sat ι rate σ e vis v j (.cmp .eq (.agg (.count dom body)) (.long 0)) ↔
      ∀ row : List TVal, row.length = (domainNames dom).length →
        ¬ Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body := by
  have hz : (0 : Int64).toInt = 0 := by decide
  rw [sat_cmp_agg_long, ← count_eq_zero_iff hT]
  have h₀ := count_total_nonneg hT
  constructor
  · rintro ⟨n₀, m, hn₀, hm, hh⟩
    have := total_unique hn₀ hT
    subst this
    have c₁ := readLong_cases hadm.aggregate hm
    simp only [CmpOp.Holds, hz, CVal.num.injEq] at hh
    simp only [Int64.MIN, Int64.MAX] at c₁
    omega
  · intro h
    subst h
    refine ⟨0, 0, hT, readLong_in (by simp [Int64.MIN]) (by simp [Int64.MAX]), ?_⟩
    simp [CmpOp.Holds, hz]

/-- **`count … < k` bounds every list of distinct rows of the body**, under any admissible
reading: fewer than `k` distinct rows satisfy it. This is the form a rate limit is used in. -/
theorem sat_count_lt_rows (hadm : ι.Admissible) {v : Valuation} {j : Nat} {dom : List Binder}
    {body : Formula} {c : Int64}
    (h : Sat ι rate σ e vis v j (.cmp .lt (.agg (.count dom body)) (.long c)))
    (L : List (List TVal)) (hL : L.Nodup)
    (hs : ∀ row ∈ L, row.length = (domainNames dom).length ∧
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body) :
    (L.length : Int) < c.toInt := by
  rw [sat_agg_cmp_down_iff hadm (fun _ => count_total_nonneg) (.inl rfl)] at h
  obtain ⟨n, ⟨rows, -, hm, rfl⟩, hh⟩ := h
  have hsub : L ⊆ rows := fun r hr => (hm r).mpr (hs r hr)
  have := (List.subperm_of_subset hL hsub).length_le
  simp only [CmpOp.Holds] at hh
  omega

end Dogwood.Thm

namespace Dogwood.Spec.Temporal

open Dogwood.Thm

/-- Widening windows changes no free variable. -/
theorem Formula.Widens.fv_eq {rate : TickRate} {φ φ' : Formula} (h : Formula.Widens rate φ φ') :
    φ.fv = φ'.fv := by
  induction h with
  | refl => rfl
  | and _ _ ih₁ ih₂ => simp only [Formula.fv, ih₁, ih₂]
  | exist x _ ih => simp only [Formula.fv, ih]
  | formerly _ _ ih => simp only [Formula.fv, ih]
  | previous _ _ ih => simp only [Formula.fv, ih]
  | since _ _ _ ih₁ ih₂ => simp only [Formula.fv, ih₁, ih₂]

/-- Widening windows changes no restriction. -/
theorem Formula.Widens.restricts_iff {rate : TickRate} {φ φ' : Formula}
    (h : Formula.Widens rate φ φ') : ∀ R x, φ.Restricts R x ↔ φ'.Restricts R x := by
  induction h with
  | refl => exact fun _ _ => Iff.rfl
  | and _ _ ih₁ ih₂ =>
    intro R x
    simp only [Formula.Restricts]
    refine forall_congr' fun S => imp_congr_right fun _ => ?_
    exact imp_congr (forall_congr' fun z => imp_congr_left (ih₁ S z))
      (imp_congr (forall_congr' fun z => imp_congr_left (ih₂ S z)) Iff.rfl)
  | exist x _ ih =>
    intro R y
    simp only [Formula.Restricts, ih]
  | formerly _ _ ih =>
    intro R y
    simp only [Formula.Restricts, ih]
  | previous _ _ ih =>
    intro R y
    simp only [Formula.Restricts, ih]
  | since _ _ _ _ ih₂ =>
    intro R y
    simp only [Formula.Restricts, ih₂]

/-- **Widening windows keeps a condition safe**, and unsafe: safety does not read windows. -/
theorem Formula.Widens.safe_iff {rate : TickRate} {φ φ' : Formula} (h : Formula.Widens rate φ φ') :
    ∀ R, φ.Safe R ↔ φ'.Safe R := by
  induction h with
  | refl => exact fun _ => Iff.rfl
  | and h₁ h₂ ih₁ ih₂ =>
    intro R
    have hr := (Formula.Widens.and h₁ h₂).restricts_iff
    have : (Formula.and _ _).Restricts R = (Formula.and _ _).Restricts R :=
      funext fun x => propext (hr R x)
    simp only [Formula.Safe, this, ih₁, ih₂]
  | exist x h ih =>
    intro R
    simp only [Formula.Safe, ih, h.restricts_iff]
  | formerly _ _ ih =>
    intro R
    simp only [Formula.Safe, ih]
  | previous _ _ ih =>
    intro R
    simp only [Formula.Safe, ih]
  | since _ h₁ h₂ ih₁ ih₂ =>
    intro R
    have : Formula.Restricted R _ = Formula.Restricted R _ :=
      funext fun x => propext (or_congr Iff.rfl (h₂.restricts_iff R x))
    simp only [Formula.Safe, this, ih₁, ih₂, h₁.fv_eq]

end Dogwood.Spec.Temporal

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

/-- **A safe count, widened, has a total** (`total_exists`, since widening keeps it safe). -/
theorem count_total_of_widens {R : VarName → Prop} {dom : List Binder} {body body' : Formula}
    (hW : Formula.Widens rate body body') (hs : (Aggregate.count dom body).Safe R) (v : Valuation)
    (j : Nat) : ∃ n', Total ι rate σ e vis v j (.count dom body') n' := by
  have hs' : (Aggregate.count dom body').Safe R := by
    simp only [Aggregate.Safe] at hs ⊢
    exact ⟨fun b hb => (hW.restricts_iff _ _).mp (hs.1 b hb), (hW.safe_iff _).mp hs.2⟩
  exact total_exists (J := j) hs' v (Nat.le_refl j)

/-- **A safe sum, widened, has a total.** -/
theorem sum_total_of_widens {R : VarName → Prop} {s : VarName} {dom : List Binder}
    {body body' : Formula} (hW : Formula.Widens rate body body')
    (hs : (Aggregate.sum s dom body).Safe R) (v : Valuation) (j : Nat) :
    ∃ n', Total ι rate σ e vis v j (.sum s dom body') n' := by
  have hs' : (Aggregate.sum s dom body').Safe R := by
    simp only [Aggregate.Safe] at hs ⊢
    exact ⟨fun b hb => (hW.restricts_iff _ _).mp (hs.1 b hb), (hW.safe_iff _).mp hs.2⟩
  exact total_exists (J := j) hs' v (Nat.le_refl j)

end Dogwood.Thm
