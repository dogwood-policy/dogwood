import Dogwood.Thm.Decision

/-!
# Scaling the clock

A trace's timestamps count ticks of a clock rate (`TickRate`), and windows are compared in ticks
of the same rate (`InWindow`, `Window.ticks`). Counting at a rate `c` times finer, with every
timestamp multiplied by `c` (`Trace.scale`), changes no truth value (`sat_scale`), no horizon
comparison, and no decision (`authorize_scale`): a window of `w` seconds spans `c` times as many
ticks at the finer rate. So the rate is a unit. A proof of an implementation that counts in
seconds applies to the same implementation counting in nanoseconds over the trace scaled by `10⁹`.

Stamping does not scale: an authorizer stamps an event whose clock reading is not after the last
stamp one tick after it (`Dogwood.Spec.Ingest`), and a tick is a finer increment at a finer rate.
At one tick per second such an event would be stamped a whole second late; at nanoseconds, one
nanosecond late. So an authorizer that stamps should count fine ticks, such as nanoseconds.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-! ## Scaled traces -/

theorem scale_getElem? (c : Nat) (σ : Trace) (k : Nat) :
    (σ.scale c)[k]? = σ[k]?.map fun p => ⟨p.ts * c, p.event⟩ := by
  simp [Trace.scale, List.getElem?_map]

theorem scale_length (c : Nat) (σ : Trace) : (σ.scale c).length = σ.length := by
  simp [Trace.scale]

/-- The events of a scaled trace are the trace's. -/
theorem scale_event? (c : Nat) (σ : Trace) (k : Nat) :
    (σ.scale c)[k]?.map (·.event) = σ[k]?.map (·.event) := by
  rw [scale_getElem?]
  cases σ[k]? <;> rfl

/-- At one tick per second, the rate `c` times finer counts `c` ticks per second. -/
theorem TickRate.seconds_mul {c : Nat} (hc : 0 < c) : (TickRate.seconds.mul c hc).perSecond = c := by
  simp [TickRate.mul, TickRate.seconds]

/-- A window at the finer rate is `c` times as long in ticks. -/
theorem Window.ticks_mul (w : Window) (rate : TickRate) {c : Nat} (hc : 0 < c) :
    w.ticks (rate.mul c hc) = w.ticks rate * c := by
  simp only [Window.ticks, TickRate.mul, Int.natCast_mul, Int.mul_assoc]

/-- The window's reach at the finer rate is `c` times its reach. -/
theorem Window.reach_mul (w : Window) (rate : TickRate) {c : Nat} (hc : 0 < c) :
    w.reach (rate.mul c hc) = w.reach rate * c := by
  have hc' : (0 : Int) < c := Int.ofNat_lt.mpr hc
  unfold Window.reach
  rw [Window.ticks_mul]
  rcases Int.le_total 0 (w.ticks rate) with h | h
  · rw [Int.max_eq_right h, Int.max_eq_right (Int.mul_nonneg h (Int.le_of_lt hc'))]
  · rw [Int.max_eq_left h, Int.max_eq_left (Int.mul_nonpos_of_nonpos_of_nonneg h (Int.le_of_lt hc')),
      Int.zero_mul]

theorem inWindow_scale {rate : TickRate} {c : Nat} (hc : 0 < c) {σ : Trace} {j k : Nat}
    {w : Window} : InWindow (rate.mul c hc) (σ.scale c) j k w ↔ InWindow rate σ j k w := by
  have hc' : (0 : Int) < c := Int.ofNat_lt.mpr hc
  unfold InWindow
  rw [scale_getElem?, scale_getElem?, Window.ticks_mul]
  cases σ[j]? with
  | none => simp
  | some pj =>
    cases σ[k]? with
    | none => simp
    | some pk =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · rintro ⟨_, _, rfl, rfl, h₀, h₁⟩
        rw [← Int.sub_mul] at h₀ h₁
        exact ⟨pj, pk, rfl, rfl, Int.nonneg_of_mul_nonneg_left h₀ hc',
          (Int.mul_le_mul_right hc').mp h₁⟩
      · rintro ⟨_, _, rfl, rfl, h₀, h₁⟩
        refine ⟨_, _, rfl, rfl, ?_, ?_⟩
        · rw [← Int.sub_mul]; exact Int.mul_nonneg h₀ (Int.le_of_lt hc')
        · rw [← Int.sub_mul]; exact (Int.mul_le_mul_right hc').mpr h₁

/-! ## Satisfaction -/

section

variable {ι : ImplChoices} {rate : TickRate} {c : Nat} (hc : 0 < c) {σ : Trace} {e : Event}
  {vis : Nat → Prop}

include hc

mutual

/-- **Scaling the clock preserves satisfaction.** A condition holds at timepoint `j` of the
trace scaled by `c`, at the rate `c` times finer, exactly when it holds at `j` of the trace at
its own rate. -/
theorem sat_scale : (φ : Formula) → (v : Valuation) → (j : Nat) →
    (Sat ι (rate.mul c hc) (σ.scale c) e vis v j φ ↔ Sat ι rate σ e vis v j φ)
  | .and φ ψ, v, j => by
    simp only [Sat]; rw [sat_scale φ v j, sat_scale ψ v j]
  | .not φ, v, j => by
    simp only [Sat]; rw [sat_scale φ v j]
  | .formerly w φ, v, j => by
    simp only [Sat, inWindow_scale hc]
    exact exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => sat_scale φ v k
  | .previous w φ, v, j => by
    simp only [Sat, inWindow_scale hc]
    exact exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => and_congr_right fun _ => sat_scale φ v k
  | .since φ w ψ, v, j => by
    simp only [Sat, inWindow_scale hc]
    refine exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ?_
    rw [sat_scale ψ v k]
    exact and_congr_right fun _ => forall_congr' fun k' => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ => sat_scale φ v k'
  | .pred a kd args, v, j => by
    simp only [Sat, scale_getElem?]
    cases σ[j]? <;> simp
  | .cmp op l r, v, j => by
    simp only [Sat]
    exact exists_congr fun a => exists_congr fun b => by
      rw [denotes_scale l v j a, denotes_scale r v j b]
  | .exist x φ, v, j => by
    simp only [Sat]
    exact exists_congr fun w => sat_scale φ (v.bind x.name w) j
  | .tp x, v, j => by
    simp only [Sat]

theorem denotes_scale : (t : Term) → (v : Valuation) → (j : Nat) → (c' : CVal) →
    (Denotes ι (rate.mul c hc) (σ.scale c) e vis v j t c' ↔ Denotes ι rate σ e vis v j t c')
  | .agg a, v, j, c' => by
    simp only [Denotes]
    exact exists_congr fun n => and_congr_left fun _ => total_scale a v j n
  | .arith _ l r, v, j, c' => by
    simp only [Denotes]
    exact exists_congr fun m => exists_congr fun n => by
      rw [denotes_scale l v j (.num m), denotes_scale r v j (.num n)]
  | .entity _, _, _, _ => by simp only [Denotes]
  | .long _, _, _, _ => by simp only [Denotes]
  | .decimal _, _, _, _ => by simp only [Denotes]
  | .string _, _, _, _ => by simp only [Denotes]
  | .bool _, _, _, _ => by simp only [Denotes]
  | .context _, _, _, _ => by simp only [Denotes]
  | .scope _ _, _, _, _ => by simp only [Denotes]
  | .var _, _, _, _ => by simp only [Denotes]
  | .wildcard, _, _, _ => by simp only [Denotes]

theorem total_scale : (a : Aggregate) → (v : Valuation) → (j : Nat) → (n : Int) →
    (Total ι (rate.mul c hc) (σ.scale c) e vis v j a n ↔ Total ι rate σ e vis v j a n)
  | .count dom body, v, j, n => by
    have ih := fun v' => sat_scale body v' j
    simp only [Total, ih]
  | .sum s dom body, v, j, n => by
    have ih := fun v' => sat_scale body v' j
    simp only [Total, ih]

end

end

section

variable (rate : TickRate) {c : Nat} (hc : 0 < c)

private theorem max_mul (c : Nat) (a b : Int) : max (a * c) (b * c) = max a b * c := by
  have hc' : (0 : Int) ≤ c := Int.natCast_nonneg c
  rcases Int.le_total a b with h | h
  · rw [Int.max_eq_right h, Int.max_eq_right (Int.mul_le_mul_of_nonneg_right h hc')]
  · rw [Int.max_eq_left h, Int.max_eq_left (Int.mul_le_mul_of_nonneg_right h hc')]

mutual

/-- The horizon at the finer rate is `c` times the horizon. -/
theorem Formula.horizon_mul : (φ : Formula) → φ.horizon (rate.mul c hc) = φ.horizon rate * c
  | .and φ ψ => by
    simp only [Formula.horizon, Formula.horizon_mul φ, Formula.horizon_mul ψ, max_mul]
  | .not φ | .exist _ φ => by simp only [Formula.horizon, Formula.horizon_mul φ]
  | .formerly w φ | .previous w φ => by
    simp only [Formula.horizon, Formula.horizon_mul φ, Window.reach_mul, Int.add_mul]
  | .since φ w ψ => by
    simp only [Formula.horizon, Formula.horizon_mul φ, Formula.horizon_mul ψ, Window.reach_mul,
      max_mul, Int.add_mul]
  | .pred .. | .tp _ => by simp [Formula.horizon]
  | .cmp _ l r => by
    simp only [Formula.horizon, Term.horizon_mul l, Term.horizon_mul r, max_mul]

theorem Term.horizon_mul : (t : Term) → t.horizon (rate.mul c hc) = t.horizon rate * c
  | .agg a => by simp only [Term.horizon, Aggregate.horizon_mul a]
  | .arith _ l r => by
    simp only [Term.horizon, Term.horizon_mul l, Term.horizon_mul r, max_mul]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _ | .var _
  | .wildcard => by simp [Term.horizon]

theorem Aggregate.horizon_mul : (a : Aggregate) → a.horizon (rate.mul c hc) = a.horizon rate * c
  | .count _ body | .sum _ _ body => by simp only [Aggregate.horizon, Formula.horizon_mul body]

end

end

/-! ## Decisions -/

/-- The schema's visibility depends on the trace's events only. -/
theorem visible_scale (S : EventSchema) (c : Nat) (σ : Trace) (e : Event) (k : Nat) :
    S.Visible (σ.scale c) e k ↔ S.Visible σ e k := by
  unfold EventSchema.Visible
  rw [scale_getElem?]
  cases σ[k]? <;> simp

/-- The policy set `P` with its clock counting at the rate `c` times finer. -/
def _root_.Dogwood.Spec.PolicySet.scale (P : PolicySet) (c : Nat) (hc : 0 < c) : PolicySet :=
  { P with tickRate := P.tickRate.mul c hc }

/-- A leaf holds at timepoint `n` of the scaled trace, at the finer rate, exactly when it holds at
`n` of the trace. -/
theorem leafHolds_scale {ι : ImplChoices} {P : PolicySet} {c : Nat} (hc : 0 < c) {σ : Trace}
    {n : Nat} {φ : Formula} :
    (P.scale c hc).LeafHolds ι (σ.scale c) n φ ↔ P.LeafHolds ι σ n φ := by
  unfold PolicySet.LeafHolds
  rw [scale_getElem?]
  cases hσ : σ[n]? with
  | none => simp
  | some p =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left']
    have hvis : (P.scale c hc).schema.Visible (σ.scale c) p.event =
        P.schema.Visible σ p.event := funext fun k => propext (visible_scale _ c σ _ k)
    rw [hvis]
    exact sat_scale (rate := P.tickRate) hc _ _ _

/-- A decision depends on a decision timepoint through its event only. -/
theorem decideWith_eq_event {P : PolicySet} {rules : Policies} {ω : Provider.Providers}
    {σ : Trace} {n : Nat} {respond : Event → Cedar.Spec.EntityUID → Cedar.Spec.EntityUID →
      Option Cedar.Spec.Response} :
    P.decideWith rules ω σ n respond =
      match σ[n]? with
      | none => .noDecision
      | some p => P.decideWith rules ω [⟨0, p.event⟩] 0 respond := by
  unfold PolicySet.decideWith
  cases σ[n]? <;> rfl

/-- **The outcome depends on the decision event only.** Two decisions at timepoints with the same
event, whose responses agree where every check passes, are the same. -/
theorem decideWith_congr_event {P : PolicySet} {rules : Policies} {ω : Provider.Providers}
    {σ₁ σ₂ : Trace} {n₁ n₂ : Nat} {respond₁ respond₂ : Event → Cedar.Spec.EntityUID →
      Cedar.Spec.EntityUID → Option Cedar.Spec.Response}
    (hn : σ₁[n₁]?.map (·.event) = σ₂[n₂]?.map (·.event))
    (h : ∀ p pr rs, σ₁[n₁]? = some p → P.Admits rules ω p pr rs →
      respond₁ p.event pr rs = respond₂ p.event pr rs) :
    P.decideWith rules ω σ₁ n₁ respond₁ = P.decideWith rules ω σ₂ n₂ respond₂ := by
  rw [decideWith_eq_event, decideWith_eq_event (σ := σ₂)]
  cases h₁ : σ₁[n₁]? with
  | none =>
    rw [h₁] at hn
    cases h₂ : σ₂[n₂]? with
    | none => rfl
    | some q => rw [h₂] at hn; cases hn
  | some p =>
    rw [h₁] at hn
    cases h₂ : σ₂[n₂]? with
    | none => rw [h₂] at hn; cases hn
    | some q =>
      rw [h₂] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      simp only
      rw [← hn]
      exact decideWith_congr rfl fun p' pr rs hp' ha => by
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hp'
        subst hp'
        exact h p pr rs h₁ ⟨ha.kind, ha.principal, ha.resource, ha.event, ha.request, ha.entities,
          ha.scopes, ha.providers, ha.outputs⟩

/-- **Scaling the clock preserves decisions.** The decision at timepoint `n` of the trace scaled by
`c`, with the policy set's clock `c` times finer, is the decision at `n` of the trace. -/
theorem authorize_scale {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers} {c : Nat}
    (hc : 0 < c) (σ : Trace) (n : Nat) :
    (P.scale c hc).authorize ι ω (σ.scale c) n = P.authorize ι ω σ n := by
  unfold PolicySet.authorize
  have hP : ∀ rules respond, (P.scale c hc).decideWith rules ω (σ.scale c) n respond =
      P.decideWith rules ω (σ.scale c) n respond := fun _ _ => rfl
  rw [hP]
  refine decideWith_congr_event (scale_event? c σ n) fun p pr rs _ _ => ?_
  simp only [PolicySet.respond]
  refine supervaluate_congr fun ι' _ => ?_
  have hleaves : (P.scale c hc).leaves ι' ω (σ.scale c) n p.event = P.leaves ι' ω σ n p.event := by
    simp only [PolicySet.leaves, Leaves.mk.injEq, and_true]
    funext φ
    exact decide_eq_decide.mpr (leafHolds_scale hc)
  rw [hleaves]
  rfl

end Dogwood.Thm
