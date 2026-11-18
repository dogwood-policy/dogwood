import Dogwood.Spec.Temporal.Horizon
import Dogwood.Spec.EventSchema
import Dogwood.Spec.Temporal.Typing
import Dogwood.Thm.Trace
import Dogwood.Thm.Slice
import Dogwood.Thm.Implementation

/-!
# A condition looks back no further than its horizon

`sat_horizon`: on traces whose timestamps never decrease, whether a condition holds at timepoint
`j` depends only on the timepoints `k ≤ j` whose timestamps lie within the condition's horizon
before `j`'s: `ts(j) − ts(k) ≤ horizon` (`Formula.horizon`), both counted in ticks of the clock
rate. Aggregates are included: the rows of an aggregate at `j` are read off the same timepoints.
The language's rule, timestamps that strictly increase (`Trace.StrictlyIncreasing`), implies the
hypothesis.

Two traces, with their visibilities, *agree within `H` of `j`* (`AgreeWithin`) when they have
the same events, and the same visibility, at every timepoint within `H` ticks before `j` in
either trace. Then a condition whose horizon is at most `H` holds at `j` in one exactly when it
holds at `j` in the other. The timepoint `j` itself is within any `H ≥ 0`.

The trace must not have decreasing timestamps: `previous` reads the visibility of every
timepoint between its match and `j`, and `since` reads its left side there, and only on a
nondecreasing trace do those timepoints lie within the window.

Corollaries:

* `sat_horizon_vis` and `sat_restrict_horizon`: on one trace, the visibility of timepoints
  beyond the horizon does not matter;
* `sat_drop_horizon`: evaluating over a suffix of the trace that keeps every timepoint within
  the horizon is evaluating over the trace. This is what an implementation that prunes the events
  beyond the horizon relies on;
* `authorize_horizon` and `authorize_drop_horizon` lift the two to decisions, with the policy
  set's horizon (`PolicySet.horizon`).

For a condition whose windows are nonnegative, the horizon is its longest look-back in ticks:
windows add up along nested temporal operators, and the operands of `&&`, of a comparison, of a
compound operand, and the two sides of `since` take the larger horizon.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-! ## Horizons are nonnegative -/

theorem Window.reach_nonneg (w : Window) (rate : TickRate) : 0 ≤ w.reach rate :=
  Int.le_max_left 0 _

/-- A window of nonnegative length reaches its length in ticks. -/
theorem Window.reach_of_nonneg {w : Window} {rate : TickRate} (h : 0 ≤ w.seconds) :
    w.reach rate = w.ticks rate :=
  Int.max_eq_right (Int.mul_nonneg h (Int.natCast_nonneg _))

theorem Window.ticks_le_reach (w : Window) (rate : TickRate) : w.ticks rate ≤ w.reach rate :=
  Int.le_max_right 0 _

/-- At one tick per second, a window's length in ticks is its length in seconds. -/
theorem Window.ticks_seconds (w : Window) : w.ticks .seconds = w.seconds := by
  simp [Window.ticks, TickRate.seconds]

section

variable (rate : TickRate)

mutual

theorem Formula.horizon_nonneg : (φ : Formula) → 0 ≤ φ.horizon rate
  | .and φ ψ => by
    have := Formula.horizon_nonneg φ
    simp only [Formula.horizon]; omega
  | .not φ | .exist _ φ => by simpa [Formula.horizon] using Formula.horizon_nonneg φ
  | .formerly w φ | .previous w φ => by
    have := Formula.horizon_nonneg φ
    have := Window.reach_nonneg w rate
    simp only [Formula.horizon]; omega
  | .since φ w ψ => by
    have := Formula.horizon_nonneg φ
    have := Window.reach_nonneg w rate
    simp only [Formula.horizon]; omega
  | .pred .. | .tp _ => by simp [Formula.horizon]
  | .cmp _ l r => by
    have := Term.horizon_nonneg l
    simp only [Formula.horizon]; omega

theorem Term.horizon_nonneg : (t : Term) → 0 ≤ t.horizon rate
  | .agg a => by simpa [Term.horizon] using Aggregate.horizon_nonneg a
  | .arith _ l r => by
    have := Term.horizon_nonneg l
    simp only [Term.horizon]; omega
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _ | .var _
  | .wildcard => by simp [Term.horizon]

theorem Aggregate.horizon_nonneg : (a : Aggregate) → 0 ≤ a.horizon rate
  | .count _ body | .sum _ _ body => by simpa [Aggregate.horizon] using Formula.horizon_nonneg body

end

end

/-! ## Pin injection keeps the horizon -/

section

variable (S : EventSchema) (rate : TickRate)

mutual

theorem Formula.horizon_injectPins : (φ : Formula) → (φ.injectPins S).horizon rate = φ.horizon rate
  | .and φ ψ => by
    simp [Formula.injectPins, Formula.horizon, Formula.horizon_injectPins φ,
      Formula.horizon_injectPins ψ]
  | .not φ => by simp [Formula.injectPins, Formula.horizon, Formula.horizon_injectPins φ]
  | .formerly _ φ => by simp [Formula.injectPins, Formula.horizon, Formula.horizon_injectPins φ]
  | .previous _ φ => by simp [Formula.injectPins, Formula.horizon, Formula.horizon_injectPins φ]
  | .since φ _ ψ => by
    simp [Formula.injectPins, Formula.horizon, Formula.horizon_injectPins φ,
      Formula.horizon_injectPins ψ]
  | .pred _ _ _ => by simp [Formula.injectPins, Formula.horizon]
  | .cmp _ l r => by
    simp [Formula.injectPins, Formula.horizon, Term.horizon_injectPins l, Term.horizon_injectPins r]
  | .exist _ φ => by simp [Formula.injectPins, Formula.horizon, Formula.horizon_injectPins φ]
  | .tp _ => rfl

theorem Term.horizon_injectPins : (t : Term) → (t.injectPins S).horizon rate = t.horizon rate
  | .agg a => by simp [Term.injectPins, Term.horizon, Aggregate.horizon_injectPins a]
  | .arith _ l r => by
    simp [Term.injectPins, Term.horizon, Term.horizon_injectPins l, Term.horizon_injectPins r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _ | .var _
  | .wildcard => rfl

theorem Aggregate.horizon_injectPins : (a : Aggregate) → (a.injectPins S).horizon rate = a.horizon rate
  | .count _ body => by
    simp [Aggregate.injectPins, Aggregate.horizon, Formula.horizon_injectPins body]
  | .sum _ _ body => by
    simp [Aggregate.injectPins, Aggregate.horizon, Formula.horizon_injectPins body]

end

mutual

theorem Formula.tpFree_injectPins : (φ : Formula) → (φ.injectPins S).tpFree = φ.tpFree
  | .and φ ψ => by
    simp [Formula.injectPins, Formula.tpFree, Formula.tpFree_injectPins φ,
      Formula.tpFree_injectPins ψ]
  | .not φ => by simp [Formula.injectPins, Formula.tpFree, Formula.tpFree_injectPins φ]
  | .formerly _ φ => by simp [Formula.injectPins, Formula.tpFree, Formula.tpFree_injectPins φ]
  | .previous _ φ => by simp [Formula.injectPins, Formula.tpFree, Formula.tpFree_injectPins φ]
  | .since φ _ ψ => by
    simp [Formula.injectPins, Formula.tpFree, Formula.tpFree_injectPins φ,
      Formula.tpFree_injectPins ψ]
  | .pred _ _ _ => by simp [Formula.injectPins, Formula.tpFree]
  | .cmp _ l r => by
    simp [Formula.injectPins, Formula.tpFree, Term.tpFree_injectPins l, Term.tpFree_injectPins r]
  | .exist _ φ => by simp [Formula.injectPins, Formula.tpFree, Formula.tpFree_injectPins φ]
  | .tp _ => rfl

theorem Term.tpFree_injectPins : (t : Term) → (t.injectPins S).tpFree = t.tpFree
  | .agg a => by simp [Term.injectPins, Term.tpFree, Aggregate.tpFree_injectPins a]
  | .arith _ l r => by
    simp [Term.injectPins, Term.tpFree, Term.tpFree_injectPins l, Term.tpFree_injectPins r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _ | .var _
  | .wildcard => rfl

theorem Aggregate.tpFree_injectPins : (a : Aggregate) → (a.injectPins S).tpFree = a.tpFree
  | .count _ body => by
    simp [Aggregate.injectPins, Aggregate.tpFree, Formula.tpFree_injectPins body]
  | .sum _ _ body => by
    simp [Aggregate.injectPins, Aggregate.tpFree, Formula.tpFree_injectPins body]

end

end

/-! ## Windows -/

section

variable (S : EventSchema)

mutual

theorem Formula.windows_injectPins : (φ : Formula) → (φ.injectPins S).windows = φ.windows
  | .and φ ψ => by
    simp [Formula.injectPins, Formula.windows, Formula.windows_injectPins φ,
      Formula.windows_injectPins ψ]
  | .since φ w ψ => by
    simp [Formula.injectPins, Formula.windows, Formula.windows_injectPins φ,
      Formula.windows_injectPins ψ]
  | .not φ => by simp [Formula.injectPins, Formula.windows, Formula.windows_injectPins φ]
  | .formerly w φ => by simp [Formula.injectPins, Formula.windows, Formula.windows_injectPins φ]
  | .previous w φ => by simp [Formula.injectPins, Formula.windows, Formula.windows_injectPins φ]
  | .exist x φ => by simp [Formula.injectPins, Formula.windows, Formula.windows_injectPins φ]
  | .cmp op l r => by
    simp [Formula.injectPins, Formula.windows, Term.windows_injectPins l,
      Term.windows_injectPins r]
  | .pred .. | .tp _ => by simp [Formula.injectPins, Formula.windows]

theorem Term.windows_injectPins : (t : Term) → (t.injectPins S).windows = t.windows
  | .agg (.count dom body) => by
    simp [Term.injectPins, Aggregate.injectPins, Term.windows, Formula.windows_injectPins body]
  | .agg (.sum s dom body) => by
    simp [Term.injectPins, Aggregate.injectPins, Term.windows, Formula.windows_injectPins body]
  | .arith op l r => by
    simp [Term.injectPins, Term.windows, Term.windows_injectPins l, Term.windows_injectPins r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _ | .var _
  | .wildcard => by simp [Term.injectPins, Term.windows]

end

theorem _root_.Dogwood.Spec.Temporal.Formula.WindowsNonneg.injectPins {φ : Formula}
    (h : φ.WindowsNonneg) :
    (φ.injectPins S).WindowsNonneg :=
  fun w hw => h w (by rwa [Formula.windows_injectPins] at hw)

end

/-- A window within the cap is positive. -/
theorem Window.seconds_pos_of_withinCap {w : Window} {cap : Int} (h : w.withinCap cap = true) :
    0 < w.seconds := by
  simp only [Window.withinCap, Bool.and_eq_true, decide_eq_true_eq] at h
  have hu : 0 < w.unit.toSeconds := by cases w.unit <;> simp [TimeUnit.toSeconds]
  simp only [Window.seconds]
  exact Int.mul_pos h.1.1 hu

mutual

/-- **Typing makes every window nonnegative.** -/
theorem Formula.WellTyped.windowsNonneg {C : TypingCtx} : {Γ : Bindings} → {φ : Formula} →
    Formula.WellTyped C Γ φ → φ.WindowsNonneg
  | _, _, .and h₁ h₂ => fun w hw => by
    simp only [Formula.windows, List.mem_append] at hw
    exact hw.elim ((Formula.WellTyped.windowsNonneg h₁) w) ((Formula.WellTyped.windowsNonneg h₂) w)
  | _, _, .not h => fun w hw => (Formula.WellTyped.windowsNonneg h) w (by simpa [Formula.windows] using hw)
  | _, _, .formerly hc h => fun w hw => by
    simp only [Formula.windows, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact Int.le_of_lt (Window.seconds_pos_of_withinCap hc)
    · exact (Formula.WellTyped.windowsNonneg h) w hw
  | _, _, .previous hc h => fun w hw => by
    simp only [Formula.windows, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact Int.le_of_lt (Window.seconds_pos_of_withinCap hc)
    · exact (Formula.WellTyped.windowsNonneg h) w hw
  | _, _, .since hc h₁ h₂ => fun w hw => by
    simp only [Formula.windows, List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | hw | hw
    · exact Int.le_of_lt (Window.seconds_pos_of_withinCap hc)
    · exact (Formula.WellTyped.windowsNonneg h₁) w hw
    · exact (Formula.WellTyped.windowsNonneg h₂) w hw
  | _, _, .pred _ _ _ => fun w hw => by simp [Formula.windows] at hw
  | _, _, .eq _ hl hr _ => fun w hw => by
    simp only [Formula.windows, List.mem_append] at hw
    exact hw.elim ((Term.Typed.windowsNonneg hl) w) ((Term.Typed.windowsNonneg hr) w)
  | _, _, .ord _ hl hr => fun w hw => by
    simp only [Formula.windows, List.mem_append] at hw
    exact hw.elim ((Term.Typed.windowsNonneg hl) w) ((Term.Typed.windowsNonneg hr) w)
  | _, _, .exist _ h => fun w hw => (Formula.WellTyped.windowsNonneg h) w (by simpa [Formula.windows] using hw)
  | _, _, .tp _ => fun w hw => by simp [Formula.windows] at hw

theorem Term.Typed.windowsNonneg {C : TypingCtx} : {Γ : Bindings} → {t : Term} → {τ : TType} →
    Term.Typed C Γ t τ → ∀ w ∈ t.windows, 0 ≤ w.seconds
  | _, _, _, .entity _ | _, _, _, .long | _, _, _, .decimal _ | _, _, _, .string
  | _, _, _, .bool | _, _, _, .context _ _ | _, _, _, .scopeRoot
  | _, _, _, .scopeAttr _ _ _ | _, _, _, .var _ => fun w hw => by simp [Term.windows] at hw
  | _, _, _, .agg h => (Aggregate.Typed.windowsNonneg h)
  | _, _, _, .arith h₁ h₂ => fun w hw => by
    simp only [Term.windows, List.mem_append] at hw
    exact hw.elim ((Term.Typed.windowsNonneg h₁) w) ((Term.Typed.windowsNonneg h₂) w)

theorem Aggregate.Typed.windowsNonneg {C : TypingCtx} : {Γ : Bindings} → {a : Aggregate} →
    Aggregate.Typed C Γ a → ∀ w ∈ (Term.agg a).windows, 0 ≤ w.seconds
  | _, _, .count _ h => fun w hw => (Formula.WellTyped.windowsNonneg h) w (by simpa [Term.windows] using hw)
  | _, _, .sum _ _ h => fun w hw => (Formula.WellTyped.windowsNonneg h) w (by simpa [Term.windows] using hw)

end

/-! ## Agreement within a horizon -/

/-- Timepoint `k` lies within `H` ticks before timepoint `j` of `σ`: `k ≤ j`, both are
timepoints of `σ`, and their timestamps differ by at most `H`. -/
def WithinHorizon (σ : Trace) (j k : Nat) (H : Int) : Prop :=
  k ≤ j ∧ ∃ pj pk, σ[j]? = some pj ∧ σ[k]? = some pk ∧ pj.ts - pk.ts ≤ H

/-- Two traces, and two visibilities, agree within `H` of timepoint `j`: they have the same
events, and the same visibility, at every timepoint within `H` ticks before `j` in either
trace. -/
def AgreeWithin (σ₁ σ₂ : Trace) (vis₁ vis₂ : Nat → Prop) (j : Nat) (H : Int) : Prop :=
  ∀ k, WithinHorizon σ₁ j k H ∨ WithinHorizon σ₂ j k H → σ₁[k]? = σ₂[k]? ∧ (vis₁ k ↔ vis₂ k)

section

variable {σ₁ σ₂ : Trace} {vis₁ vis₂ : Nat → Prop} {j : Nat} {H : Int}

theorem AgreeWithin.symm (h : AgreeWithin σ₁ σ₂ vis₁ vis₂ j H) : AgreeWithin σ₂ σ₁ vis₂ vis₁ j H :=
  fun k hk => ⟨(h k hk.symm).1.symm, (h k hk.symm).2.symm⟩

/-- The timepoint itself is within every nonnegative horizon. -/
theorem AgreeWithin.getElem?_self (h : AgreeWithin σ₁ σ₂ vis₁ vis₂ j H) (hH : 0 ≤ H) :
    σ₁[j]? = σ₂[j]? := by
  cases h1 : σ₁[j]? with
  | some p =>
    rw [← h1]
    exact (h j (.inl ⟨Nat.le_refl j, p, p, h1, h1, by omega⟩)).1
  | none =>
    cases h2 : σ₂[j]? with
    | none => rfl
    | some q =>
      have := (h j (.inr ⟨Nat.le_refl j, q, q, h2, h2, by omega⟩)).1
      rw [h1, h2] at this; cases this

/-- Agreement within `H` of `j` gives agreement within `H − (ts(j) − ts(k))` of an earlier
timepoint `k` at which the traces agree. -/
theorem AgreeWithin.shift (h : AgreeWithin σ₁ σ₂ vis₁ vis₂ j H) {k : Nat} {pj pk : TimePoint}
    (hk : k ≤ j) (h1j : σ₁[j]? = some pj) (h2j : σ₂[j]? = some pj) (h1k : σ₁[k]? = some pk)
    (h2k : σ₂[k]? = some pk) {H' : Int} (hH : H' + (pj.ts - pk.ts) ≤ H) :
    AgreeWithin σ₁ σ₂ vis₁ vis₂ k H' := by
  intro k'' hk''
  apply h k''
  rcases hk'' with ⟨hle, qk, q, hqk, hq, hd⟩ | ⟨hle, qk, q, hqk, hq, hd⟩
  · rw [h1k, Option.some.injEq] at hqk; subst hqk
    exact .inl ⟨Nat.le_trans hle hk, pj, q, h1j, hq, by omega⟩
  · rw [h2k, Option.some.injEq] at hqk; subst hqk
    exact .inr ⟨Nat.le_trans hle hk, pj, q, h2j, hq, by omega⟩

end

private theorem exists_getElem?_of_le {σ : Trace} {j k : Nat} {p : TimePoint}
    (hp : σ[j]? = some p) (hk : k ≤ j) : ∃ q, σ[k]? = some q := by
  rcases Nat.lt_or_ge j σ.length with h | h
  · exact ⟨σ[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  · rw [List.getElem?_eq_none h] at hp; cases hp

/-! ## The horizon theorem -/

section

variable {ι : ImplChoices} {rate : TickRate} {e : Event}

mutual

theorem sat_horizon_imp : (φ : Formula) → (σ₁ σ₂ : Trace) → (vis₁ vis₂ : Nat → Prop) →
    Trace.Nondecreasing σ₁ → Trace.Nondecreasing σ₂ → (v : Valuation) → (j : Nat) → (H : Int) →
    φ.horizon rate ≤ H → AgreeWithin σ₁ σ₂ vis₁ vis₂ j H →
    Sat ι rate σ₁ e vis₁ v j φ → Sat ι rate σ₂ e vis₂ v j φ
  | .and φ ψ, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, hs => by
    simp only [Formula.horizon] at hH
    simp only [Sat] at hs ⊢
    exact ⟨sat_horizon_imp φ σ₁ σ₂ vis₁ vis₂ h₁ h₂ v j H (by omega) h hs.1,
      sat_horizon_imp ψ σ₁ σ₂ vis₁ vis₂ h₁ h₂ v j H (by omega) h hs.2⟩
  | .not φ, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, hs => by
    simp only [Formula.horizon] at hH
    simp only [Sat] at hs ⊢
    exact fun h2 => hs (sat_horizon_imp φ σ₂ σ₁ vis₂ vis₁ h₂ h₁ v j H hH h.symm h2)
  | .formerly w φ, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, hs => by
    simp only [Formula.horizon] at hH
    have hφ := Formula.horizon_nonneg rate φ
    have hw := Window.ticks_le_reach w rate
    simp only [Sat] at hs ⊢
    obtain ⟨k, hk, hv, ⟨pj, pk, hpj, hpk, h0, hwin⟩, hs⟩ := hs
    obtain ⟨hgk, hvk⟩ := h k (.inl ⟨hk, pj, pk, hpj, hpk, by omega⟩)
    have hpj₂ : σ₂[j]? = some pj := by rw [← h.getElem?_self (by omega)]; exact hpj
    have hpk₂ : σ₂[k]? = some pk := by rw [← hgk]; exact hpk
    exact ⟨k, hk, hvk.mp hv, ⟨pj, pk, hpj₂, hpk₂, h0, hwin⟩,
      sat_horizon_imp φ σ₁ σ₂ vis₁ vis₂ h₁ h₂ v k (H - (pj.ts - pk.ts)) (by omega)
        (h.shift hk hpj hpj₂ hpk hpk₂ (by omega)) hs⟩
  | .previous w φ, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, hs => by
    simp only [Formula.horizon] at hH
    have hφ := Formula.horizon_nonneg rate φ
    have hw := Window.ticks_le_reach w rate
    simp only [Sat] at hs ⊢
    obtain ⟨k, hk, hv, hlast, ⟨pj, pk, hpj, hpk, h0, hwin⟩, hs⟩ := hs
    obtain ⟨hgk, hvk⟩ := h k (.inl ⟨Nat.le_of_lt hk, pj, pk, hpj, hpk, by omega⟩)
    have hpj₂ : σ₂[j]? = some pj := by rw [← h.getElem?_self (by omega)]; exact hpj
    have hpk₂ : σ₂[k]? = some pk := by rw [← hgk]; exact hpk
    refine ⟨k, hk, hvk.mp hv, ?_, ⟨pj, pk, hpj₂, hpk₂, h0, hwin⟩,
      sat_horizon_imp φ σ₁ σ₂ vis₁ vis₂ h₁ h₂ v k (H - (pj.ts - pk.ts)) (by omega)
        (h.shift (Nat.le_of_lt hk) hpj hpj₂ hpk hpk₂ (by omega)) hs⟩
    intro k' hk1 hk2 hv2
    obtain ⟨q, hq⟩ := exists_getElem?_of_le hpj (Nat.le_of_lt hk2)
    have hle1 := h₁.ts_le (Nat.le_of_lt hk1) hpk hq
    have hle2 := h₁.ts_le (Nat.le_of_lt hk2) hq hpj
    exact hlast k' hk1 hk2
      ((h k' (.inl ⟨Nat.le_of_lt hk2, pj, q, hpj, hq, by omega⟩)).2.mpr hv2)
  | .since φ w ψ, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, hs => by
    simp only [Formula.horizon] at hH
    have hφ := Formula.horizon_nonneg rate φ
    have hψ := Formula.horizon_nonneg rate ψ
    have hw := Window.ticks_le_reach w rate
    simp only [Sat] at hs ⊢
    obtain ⟨k, hk, hv, ⟨pj, pk, hpj, hpk, h0, hwin⟩, hs, hall⟩ := hs
    obtain ⟨hgk, hvk⟩ := h k (.inl ⟨hk, pj, pk, hpj, hpk, by omega⟩)
    have hpj₂ : σ₂[j]? = some pj := by rw [← h.getElem?_self (by omega)]; exact hpj
    have hpk₂ : σ₂[k]? = some pk := by rw [← hgk]; exact hpk
    refine ⟨k, hk, hvk.mp hv, ⟨pj, pk, hpj₂, hpk₂, h0, hwin⟩,
      sat_horizon_imp ψ σ₁ σ₂ vis₁ vis₂ h₁ h₂ v k (H - (pj.ts - pk.ts)) (by omega)
        (h.shift hk hpj hpj₂ hpk hpk₂ (by omega)) hs, ?_⟩
    intro k' hk1 hk2 hv2
    obtain ⟨q, hq⟩ := exists_getElem?_of_le hpj hk2
    have hle1 := h₁.ts_le (Nat.le_of_lt hk1) hpk hq
    have hle2 := h₁.ts_le hk2 hq hpj
    obtain ⟨hgq, hvq⟩ := h k' (.inl ⟨hk2, pj, q, hpj, hq, by omega⟩)
    have hq₂ : σ₂[k']? = some q := by rw [← hgq]; exact hq
    exact sat_horizon_imp φ σ₁ σ₂ vis₁ vis₂ h₁ h₂ v k' (H - (pj.ts - q.ts)) (by omega)
      (h.shift hk2 hpj hpj₂ hq hq₂ (by omega)) (hall k' hk1 hk2 (hvq.mpr hv2))
  | .pred a kd args, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, hs => by
    simp only [Formula.horizon] at hH
    simp only [Sat] at hs ⊢
    rw [← h.getElem?_self hH]; exact hs
  | .cmp op l r, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, hs => by
    simp only [Formula.horizon] at hH
    simp only [Sat] at hs ⊢
    obtain ⟨a, b, ha, hb, hop⟩ := hs
    exact ⟨a, b, denotes_horizon_imp l σ₁ σ₂ vis₁ vis₂ h₁ h₂ v j H (by omega) h a ha,
      denotes_horizon_imp r σ₁ σ₂ vis₁ vis₂ h₁ h₂ v j H (by omega) h b hb, hop⟩
  | .exist x φ, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, hs => by
    simp only [Formula.horizon] at hH
    simp only [Sat] at hs ⊢
    obtain ⟨w, hw⟩ := hs
    exact ⟨w, sat_horizon_imp φ σ₁ σ₂ vis₁ vis₂ h₁ h₂ (v.bind x.name w) j H hH h hw⟩
  | .tp x, _, _, _, _, _, _, v, j, _, _, _, hs => by
    simp only [Sat] at hs ⊢; exact hs

theorem denotes_horizon_imp : (t : Term) → (σ₁ σ₂ : Trace) → (vis₁ vis₂ : Nat → Prop) →
    Trace.Nondecreasing σ₁ → Trace.Nondecreasing σ₂ → (v : Valuation) → (j : Nat) → (H : Int) →
    t.horizon rate ≤ H → AgreeWithin σ₁ σ₂ vis₁ vis₂ j H → (c : CVal) →
    Denotes ι rate σ₁ e vis₁ v j t c → Denotes ι rate σ₂ e vis₂ v j t c
  | .agg a, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, c, hd => by
    simp only [Term.horizon] at hH
    simp only [Denotes] at hd ⊢
    obtain ⟨n, ht, hv⟩ := hd
    exact ⟨n, total_horizon_imp a σ₁ σ₂ vis₁ vis₂ h₁ h₂ v j H hH h n ht, hv⟩
  | .arith op l r, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, c, hd => by
    simp only [Term.horizon] at hH
    simp only [Denotes] at hd ⊢
    obtain ⟨m, n, hl, hr, hv⟩ := hd
    exact ⟨m, n, denotes_horizon_imp l σ₁ σ₂ vis₁ vis₂ h₁ h₂ v j H (by omega) h _ hl,
      denotes_horizon_imp r σ₁ σ₂ vis₁ vis₂ h₁ h₂ v j H (by omega) h _ hr, hv⟩
  | .entity _, _, _, _, _, _, _, _, _, _, _, _, _, hd
  | .long _, _, _, _, _, _, _, _, _, _, _, _, _, hd
  | .decimal _, _, _, _, _, _, _, _, _, _, _, _, _, hd
  | .string _, _, _, _, _, _, _, _, _, _, _, _, _, hd
  | .bool _, _, _, _, _, _, _, _, _, _, _, _, _, hd
  | .context _, _, _, _, _, _, _, _, _, _, _, _, _, hd
  | .scope _ _, _, _, _, _, _, _, _, _, _, _, _, _, hd
  | .var _, _, _, _, _, _, _, _, _, _, _, _, _, hd
  | .wildcard, _, _, _, _, _, _, _, _, _, _, _, _, hd => by
    simp only [Denotes] at hd ⊢; exact hd

theorem total_horizon_imp : (a : Aggregate) → (σ₁ σ₂ : Trace) → (vis₁ vis₂ : Nat → Prop) →
    Trace.Nondecreasing σ₁ → Trace.Nondecreasing σ₂ → (v : Valuation) → (j : Nat) → (H : Int) →
    a.horizon rate ≤ H → AgreeWithin σ₁ σ₂ vis₁ vis₂ j H → (n : Int) →
    Total ι rate σ₁ e vis₁ v j a n → Total ι rate σ₂ e vis₂ v j a n
  | .count dom body, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, n, ht => by
    simp only [Aggregate.horizon] at hH
    have ih : ∀ v', Sat ι rate σ₁ e vis₁ v' j body ↔ Sat ι rate σ₂ e vis₂ v' j body := fun v' =>
      ⟨sat_horizon_imp body σ₁ σ₂ vis₁ vis₂ h₁ h₂ v' j H hH h,
        sat_horizon_imp body σ₂ σ₁ vis₂ vis₁ h₂ h₁ v' j H hH h.symm⟩
    simp only [Total, ih] at ht ⊢
    exact ht
  | .sum s dom body, σ₁, σ₂, vis₁, vis₂, h₁, h₂, v, j, H, hH, h, n, ht => by
    simp only [Aggregate.horizon] at hH
    have ih : ∀ v', Sat ι rate σ₁ e vis₁ v' j body ↔ Sat ι rate σ₂ e vis₂ v' j body := fun v' =>
      ⟨sat_horizon_imp body σ₁ σ₂ vis₁ vis₂ h₁ h₂ v' j H hH h,
        sat_horizon_imp body σ₂ σ₁ vis₂ vis₁ h₂ h₁ v' j H hH h.symm⟩
    simp only [Total, ih] at ht ⊢
    exact ht

end

variable {σ₁ σ₂ : Trace} {vis₁ vis₂ : Nat → Prop}

/-- **A condition looks back no further than its horizon.** On traces whose timestamps never
decrease, a condition whose horizon is at most `H` holds at timepoint `j` of one trace exactly
when it holds at `j` of another that agrees with it within `H` of `j`. -/
theorem sat_horizon (h₁ : Trace.Nondecreasing σ₁) (h₂ : Trace.Nondecreasing σ₂) (φ : Formula)
    (v : Valuation) (j : Nat) {H : Int} (hH : φ.horizon rate ≤ H)
    (h : AgreeWithin σ₁ σ₂ vis₁ vis₂ j H) :
    Sat ι rate σ₁ e vis₁ v j φ ↔ Sat ι rate σ₂ e vis₂ v j φ :=
  ⟨sat_horizon_imp φ σ₁ σ₂ vis₁ vis₂ h₁ h₂ v j H hH h,
    sat_horizon_imp φ σ₂ σ₁ vis₂ vis₁ h₂ h₁ v j H hH h.symm⟩

/-- What an operand denotes depends only on the timepoints within its horizon. -/
theorem denotes_horizon (h₁ : Trace.Nondecreasing σ₁) (h₂ : Trace.Nondecreasing σ₂) (t : Term)
    (v : Valuation) (j : Nat) {H : Int} (hH : t.horizon rate ≤ H)
    (h : AgreeWithin σ₁ σ₂ vis₁ vis₂ j H) (c : CVal) :
    Denotes ι rate σ₁ e vis₁ v j t c ↔ Denotes ι rate σ₂ e vis₂ v j t c :=
  ⟨denotes_horizon_imp t σ₁ σ₂ vis₁ vis₂ h₁ h₂ v j H hH h c,
    denotes_horizon_imp t σ₂ σ₁ vis₂ vis₁ h₂ h₁ v j H hH h.symm c⟩

/-- An aggregate's total depends only on the timepoints within its horizon. -/
theorem total_horizon (h₁ : Trace.Nondecreasing σ₁) (h₂ : Trace.Nondecreasing σ₂) (a : Aggregate)
    (v : Valuation) (j : Nat) {H : Int} (hH : a.horizon rate ≤ H)
    (h : AgreeWithin σ₁ σ₂ vis₁ vis₂ j H) (n : Int) :
    Total ι rate σ₁ e vis₁ v j a n ↔ Total ι rate σ₂ e vis₂ v j a n :=
  ⟨total_horizon_imp a σ₁ σ₂ vis₁ vis₂ h₁ h₂ v j H hH h n,
    total_horizon_imp a σ₂ σ₁ vis₂ vis₁ h₂ h₁ v j H hH h.symm n⟩

variable {σ : Trace}

/-- On one trace, the visibility of the timepoints beyond the horizon does not matter. -/
theorem sat_horizon_vis (hσ : Trace.Nondecreasing σ) (φ : Formula) (v : Valuation) (j : Nat)
    {H : Int} (hH : φ.horizon rate ≤ H) (hvis : ∀ k, WithinHorizon σ j k H → (vis₁ k ↔ vis₂ k)) :
    Sat ι rate σ e vis₁ v j φ ↔ Sat ι rate σ e vis₂ v j φ :=
  sat_horizon hσ hσ φ v j hH fun k hk => ⟨rfl, hvis k (hk.elim id id)⟩

/-- A condition observes only the visible timepoints within its horizon. -/
theorem sat_restrict_horizon (hσ : Trace.Nondecreasing σ) (φ : Formula) (vis : Nat → Prop)
    (v : Valuation) (j : Nat) {H : Int} (hH : φ.horizon rate ≤ H) :
    Sat ι rate σ e vis v j φ ↔ Sat ι rate σ e (fun k => vis k ∧ WithinHorizon σ j k H) v j φ :=
  sat_horizon_vis hσ φ v j hH fun _ hk => ⟨fun hv => ⟨hv, hk⟩, fun hv => hv.1⟩

/-- **Pruning beyond the horizon.** On a trace whose timestamps never decrease: if every
timepoint before `off` lies beyond the horizon of `j`, a condition holds at `j` of the trace
exactly when it holds at `j − off` of the suffix from `off`, under the same visibility, and a
valuation without timepoints. -/
theorem sat_drop_horizon (hσ : Trace.Nondecreasing σ) (φ : Formula)
    (vis : Nat → Prop) {v : Valuation} (hv : v.NoTp) {off j : Nat} (hoff : off ≤ j)
    (hj : j < σ.length) {H : Int} (hH : φ.horizon rate ≤ H) (hold : ∀ k < off, ¬ WithinHorizon σ j k H) :
    Sat ι rate (σ.drop off) e (fun i => vis (off + i)) v (j - off) φ ↔ Sat ι rate σ e vis v j φ := by
  have hsub := subsequence_drop σ off vis
  rw [sat_subseq_noTp hsub φ hv (j - off) (by simp; omega), Nat.add_sub_cancel' hoff]
  apply sat_horizon_vis hσ φ v j hH
  intro k hk
  obtain ⟨hkj, pj, pk, _, hpk, _⟩ := hk
  have hkl : k < σ.length := by
    rcases Nat.lt_or_ge k σ.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hpk; cases hpk
  have hko : off ≤ k := by
    by_contra hlt
    exact hold k (by omega) ⟨hkj, pj, pk, by assumption, hpk, by assumption⟩
  exact ⟨fun h => h.1, fun h => ⟨h, hko, hkl⟩⟩

end

/-! ## Decisions -/

theorem horizon_le_of_mem {P : PolicySet} {φ : Formula} (h : φ ∈ P.temporalLeaves) :
    φ.horizon P.tickRate ≤ P.horizon := by
  unfold PolicySet.horizon
  generalize P.temporalLeaves = L at h ⊢
  induction L with
  | nil => cases h
  | cons ψ rest ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem _root_.Dogwood.Spec.PolicySet.horizon_nonneg (P : PolicySet) : 0 ≤ P.horizon := by
  unfold PolicySet.horizon
  generalize P.temporalLeaves = L
  induction L with
  | nil => simp
  | cons ψ rest ih => simp only [List.foldr_cons]; omega

section

variable {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers}

/-- The decision is `authorize` once the leaves are known: two traces that agree at their
decision timepoints, and whose leaves hold alike there under every reading, decide alike. -/
theorem authorize_congr_leaves {σ₁ σ₂ : Trace} {n₁ n₂ : Nat} (hn : σ₁[n₁]? = σ₂[n₂]?)
    (hleaf : ∀ ι', ∀ φ ∈ P.temporalLeaves, P.LeafHolds ι' σ₁ n₁ φ ↔ P.LeafHolds ι' σ₂ n₂ φ) :
    P.authorize ι ω σ₁ n₁ = P.authorize ι ω σ₂ n₂ := by
  unfold PolicySet.authorize
  refine decideWith_congr hn fun p pr rs _ _ => ?_
  simp only [PolicySet.respond]
  refine supervaluate_congr fun ι' _ => ?_
  apply isAuthorized_congr
  intro q hq l hl
  cases l with
  | inl φ =>
    show @decide _ (Classical.propDecidable _) = @decide _ (Classical.propDecidable _)
    exact decide_eq_decide.mpr (hleaf ι' φ (mem_temporalLeaves hq hl))
  | inr c => rfl

/-- **A decision looks back no further than the policy set's horizon.** On traces whose
timestamps never decrease, two traces that have the same events within `H ≥ P.horizon` of the
timepoint `n`, in either trace, decide alike at `n`. -/
theorem authorize_horizon {σ₁ σ₂ : Trace} (h₁ : Trace.Nondecreasing σ₁)
    (h₂ : Trace.Nondecreasing σ₂) {n : Nat} {H : Int} (hH : P.horizon ≤ H)
    (hagree : ∀ k, WithinHorizon σ₁ n k H ∨ WithinHorizon σ₂ n k H → σ₁[k]? = σ₂[k]?) :
    P.authorize ι ω σ₁ n = P.authorize ι ω σ₂ n := by
  have hH0 : 0 ≤ H := Int.le_trans P.horizon_nonneg hH
  have hn : σ₁[n]? = σ₂[n]? := by
    cases h1 : σ₁[n]? with
    | some p =>
      rw [← h1]; exact hagree n (.inl ⟨Nat.le_refl n, p, p, h1, h1, by omega⟩)
    | none =>
      cases h2 : σ₂[n]? with
      | none => rfl
      | some q =>
        have := hagree n (.inr ⟨Nat.le_refl n, q, q, h2, h2, by omega⟩)
        rw [h1, h2] at this; cases this
  apply authorize_congr_leaves hn
  intro ι' φ hφ
  unfold PolicySet.LeafHolds
  rw [hn]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  apply sat_horizon h₁ h₂ _ _ n (H := H)
  · rw [Formula.horizon_injectPins]; exact Int.le_trans (horizon_le_of_mem hφ) hH
  · intro k hk
    have hk' := hagree k hk
    refine ⟨hk', ?_⟩
    simp only [EventSchema.Visible, hk']

/-- **Pruning beyond the policy set's horizon.** On a trace whose timestamps never decrease: if
every timepoint before `off` lies beyond `H ≥ P.horizon` of the timepoint `n`, the decision at `n`
is the decision at `n − off` of the suffix from `off`. An implementation that keeps only the
events within the horizon decides as the specification does. -/
theorem authorize_drop_horizon {σ : Trace} (hσ : Trace.Nondecreasing σ) {off n : Nat} (hoff : off ≤ n)
    (hn : n < σ.length) {H : Int} (hH : P.horizon ≤ H)
    (hold : ∀ k < off, ¬ WithinHorizon σ n k H) :
    P.authorize ι ω (σ.drop off) (n - off) = P.authorize ι ω σ n := by
  have hget : (σ.drop off)[n - off]? = σ[n]? := by
    rw [List.getElem?_drop, Nat.add_sub_cancel' hoff]
  have hleaf : ∀ ι', ∀ φ ∈ P.temporalLeaves,
      P.LeafHolds ι' (σ.drop off) (n - off) φ ↔ P.LeafHolds ι' σ n φ := by
    intro ι' φ hφ
    unfold PolicySet.LeafHolds
    rw [hget]
    refine exists_congr fun p => and_congr_right fun _ => ?_
    have hvis : Sat ι' P.tickRate (σ.drop off) p.event (P.schema.Visible (σ.drop off) p.event)
        Valuation.empty (n - off) (φ.injectPins P.schema) ↔
        Sat ι' P.tickRate (σ.drop off) p.event (fun i => P.schema.Visible σ p.event (off + i))
        Valuation.empty (n - off) (φ.injectPins P.schema) := by
      apply sat_congr
      intro k _
      refine ⟨rfl, ?_⟩
      simp only [EventSchema.Visible, List.getElem?_drop]
    rw [hvis]
    exact sat_drop_horizon hσ _ _ Valuation.noTp_empty hoff hn
      (by rw [Formula.horizon_injectPins]; exact Int.le_trans (horizon_le_of_mem hφ) hH) hold
  -- The two decisions agree once their timepoints and leaves do.
  exact authorize_congr_leaves hget hleaf

end

end Dogwood.Thm
