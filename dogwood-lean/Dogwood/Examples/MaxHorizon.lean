import Dogwood.Examples.ReadAfterLogin
import Dogwood.Thm.ValidityDecide
import Dogwood.Frontend.Derive

/-!
# Worked example: `max_horizon` caps nested look-back

`formerly within 24h (formerly within 24h Login)` keeps every window within the default 24h
`max_window`, but looks back 48h in total. Without a declared `max_horizon` there is no horizon
cap, and validity's horizon clause holds of it. Under a declared 24h `max_horizon` it fails, and
the set is not valid; raised to 48h, it holds again.
-/

namespace Dogwood.Examples.MaxHorizon

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Examples Dogwood.Examples.ReadAfterLogin

/-- A login response of the same user, within 24h. -/
def loginWithin24h : Formula :=
  .formerly ⟨24, .hours⟩ (.pred login "response" [(["input", "user"], .context ["input", "user"])])

/-- Two nested 24h windows: a 48h horizon. -/
def nested : Formula := .formerly ⟨24, .hours⟩ loginWithin24h

theorem nested_horizon : nested.horizon .seconds = 2 * 86400 := by decide

/-- The read policy with the nested condition, under the default caps: no `max_horizon`. -/
def nestedSet : PolicySet := onePolicy read nested schema actions

theorem nestedSet_leaves : nestedSet.temporalLeaves = [nested] := rfl

/-- Whether every temporal leaf of `P` is within a cap of `H` seconds. -/
def withinCap (P : PolicySet) (H : Int) : Bool :=
  P.temporalLeaves.all fun φ => decide (φ.horizon .seconds ≤ H)

/-- **Without a declared `max_horizon` there is no cap**: the horizon clause holds of any set. -/
theorem undeclared_unbounded : nestedSet.maxHorizon = none := rfl

/-- **A declared 24h `max_horizon` rejects the nested condition.** -/
theorem nested_rejected_at_24h : withinCap nestedSet 86400 = false := by decide

/-- **So the set with that cap is not valid**, whatever else holds of it. -/
theorem nested_not_valid_at_24h : ¬ ({ nestedSet with maxHorizon := some 86400 }).Valid :=
  fun hv => by
    have := hv.horizon 86400 rfl nested (List.mem_singleton_self _)
    revert this
    decide

/-- **Raised to 48h, `max_horizon` admits it.** -/
theorem nested_admitted_at_48h : withinCap nestedSet (2 * 86400) = true := by decide

/-- **A single 24h window is within a 24h cap.** -/
theorem single_admitted_at_24h :
    withinCap (onePolicy read loginWithin24h schema actions) 86400 = true := by decide

/-! ## The frontend port's resolution of the caps -/

open Dogwood.Frontend in
/-- **The port rejects a window cap longer than the horizon cap with the crate's message.** The
crate's test `window_above_horizon_message_is_exact` (`tests/max_horizon.rs`) pins the same text:
change both together. -/
theorem limits_message :
    Derive.limits { maxWindow := some ⟨48, .hours⟩, maxHorizon := some ⟨24, .hours⟩, decls := [] } =
      .error "`max_window = 48h` is longer than `max_horizon = 24h`; a temporal condition can never look back further than `max_horizon`, so no window could use its full cap. Set `max_horizon` to at least `48h`, or lower `max_window`" := by
  decide +kernel

open Dogwood.Frontend in
/-- **The port's resolution**: without `max_horizon` no horizon cap and a 24h window; a declared
`max_horizon` alone sets the window cap; a declared window cap within the horizon is kept. -/
theorem limits_resolution :
    Derive.limits { maxWindow := none, maxHorizon := none, decls := [] } =
        .ok (⟨24, .hours⟩, none) ∧
      Derive.limits { maxWindow := none, maxHorizon := some ⟨48, .hours⟩, decls := [] } =
        .ok (⟨48, .hours⟩, some ⟨48, .hours⟩) ∧
      Derive.limits { maxWindow := some ⟨8760, .hours⟩, maxHorizon := none, decls := [] } =
        .ok (⟨8760, .hours⟩, none) ∧
      Derive.limits { maxWindow := some ⟨1, .hours⟩, maxHorizon := some ⟨24, .hours⟩, decls := [] } =
        .ok (⟨1, .hours⟩, some ⟨24, .hours⟩) := by
  decide +kernel

end Dogwood.Examples.MaxHorizon
