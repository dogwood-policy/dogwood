import Dogwood.Thm.Horizon
import Dogwood.Thm.Scale
import Dogwood.Spec.Validity

/-!
# `max_horizon` is a retention bound

When the event schema declares `max_horizon`, validity caps every temporal leaf's horizon
(`Formula.horizon`, at one tick per second) at it (`PolicySet.Valid.horizon`). Since a condition looks back no further
than its horizon (`Dogwood.Thm.authorize_drop_horizon`), a service that keeps the events of the
last `max_horizon` decides every valid policy set as the specification does:

* **The bound** (`horizon_le_maxHorizon`): a valid policy set's horizon, in ticks of its clock, is
  at most its declared `max_horizon`'s seconds' worth of ticks.
* **Retention** (`authorize_drop_maxHorizon`): on a trace whose timestamps never decrease, if every
  timepoint before `off` lies more than `max_horizon` before the decision, dropping them changes
  no decision.

So retention of at least `max_horizon` is a static guarantee for every policy set an event schema
that declares it lets validate, whatever its nesting. Without the directive there is no cap, and no
such guarantee. (`max_window` alone is no such bound:
`Dogwood.Thm.horizon_formerlyIter_eq`.)
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-- A rate is whole seconds made `perSecond` times finer. -/
theorem TickRate.eq_seconds_mul (rate : TickRate) :
    rate = TickRate.seconds.mul rate.perSecond rate.pos := by
  cases rate
  simp [TickRate.mul, TickRate.seconds]

/-- **A horizon at any rate is the horizon in seconds times the rate.** -/
theorem Formula.horizon_eq_seconds_mul (φ : Formula) (rate : TickRate) :
    φ.horizon rate = φ.horizon .seconds * rate.perSecond := by
  conv => lhs; rw [TickRate.eq_seconds_mul rate]
  exact Formula.horizon_mul _ rate.pos φ

/-- **A valid policy set looks back at most `max_horizon`**: its horizon, in ticks of its clock,
is at most `max_horizon` seconds' worth of ticks. -/
theorem horizon_le_maxHorizon {P : PolicySet} (hv : P.Valid) {H : Int}
    (hH : P.maxHorizon = some H) (h0 : 0 ≤ H) :
    P.horizon ≤ H * P.tickRate.perSecond := by
  have hleaf : ∀ φ ∈ P.temporalLeaves,
      φ.horizon P.tickRate ≤ H * P.tickRate.perSecond := by
    intro φ hφ
    rw [Formula.horizon_eq_seconds_mul]
    exact Int.mul_le_mul_of_nonneg_right (hv.horizon H hH φ hφ) (Int.natCast_nonneg _)
  have hM : 0 ≤ H * P.tickRate.perSecond := Int.mul_nonneg h0 (Int.natCast_nonneg _)
  unfold PolicySet.horizon
  generalize P.temporalLeaves = L at hleaf
  induction L with
  | nil => simpa using hM
  | cons ψ rest ih =>
    simp only [List.foldr_cons]
    have h₁ := hleaf ψ (List.mem_cons_self ..)
    have h₂ := ih (fun φ hφ => hleaf φ (List.mem_cons_of_mem _ hφ))
    omega

variable {ι : ImplChoices} {ω : Provider.Providers}

/-- **Retention of `max_horizon` suffices.** For a valid policy set, on a trace whose timestamps
never decrease: if every timepoint before `off` lies more than `max_horizon` before the timepoint
`n` (in ticks of the set's clock), the decision at `n` is the decision at `n − off` of the suffix
from `off`. A service that keeps only the events of the last `max_horizon` decides every valid
policy set as the specification does. -/
theorem authorize_drop_maxHorizon {P : PolicySet} (hv : P.Valid) {H : Int}
    (hH : P.maxHorizon = some H) (h0 : 0 ≤ H)
    {σ : Trace} (hσ : Trace.Nondecreasing σ) {off n : Nat} (hoff : off ≤ n) (hn : n < σ.length)
    (hold : ∀ k < off, ¬ WithinHorizon σ n k (H * P.tickRate.perSecond)) :
    P.authorize ι ω (σ.drop off) (n - off) = P.authorize ι ω σ n :=
  authorize_drop_horizon hσ hoff hn (horizon_le_maxHorizon hv hH h0) hold

end Dogwood.Thm
