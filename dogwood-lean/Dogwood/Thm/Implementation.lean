import Dogwood.Spec.Validity
import Dogwood.Thm.Decision
import Dogwood.Thm.Leaves

/-!
# What a proof of an implementation shows

An implementation of Dogwood computes the decision's temporal leaves its own way, as a temporal
engine plugged into the crate (`engine.rs`, `TemporalEngine`; the crate's own is
`InMemoryTemporalEngine`). Everything else of the decision, including the conformance checks of
the data the decision reads, it leaves to the crate's front end (`api.rs`, `decide_at`).
`PolicySet.authorizeWith` is that decision with the leaves supplied.

* `authorizeWith_eq`: when the implementation's leaf values decide `LeafHolds` under a total
  reading on every temporal leaf of the policy set at the decision events whose data conform
  (`PolicySet.Admits`), its outcome is `PolicySet.authorize`'s under the reading. A proof of an
  implementation can end with this step.
* `leafHolds_iff_global`: without a universal symmetric pin, a leaf holds exactly when its
  pinned form holds under global visibility, every timepoint visible.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-- **An implementation that decides the leaves decides as the specification does.** A leaf
valuation that decides `PolicySet.LeafHolds` under a total reading on every temporal leaf of the
policy set, at the decision events whose data conform, gives the specification's outcome under
the reading. -/
theorem authorizeWith_eq {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers}
    {σ : Trace} {n : Nat} {temporal : Event → Formula → Bool} (hι : ι.Total)
    (htemp : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
      ∀ φ ∈ P.temporalLeaves, (temporal p.event φ = true ↔ P.LeafHolds ι σ n φ)) :
    P.authorizeWith ω σ n temporal = P.authorize ι ω σ n := by
  unfold PolicySet.authorizeWith PolicySet.authorize
  refine decideWith_congr rfl fun p pr rs hσ h => ?_
  rw [respond_total hι, Option.some.injEq]
  apply isAuthorized_congr
  intro q hq l hl
  cases l with
  | inl φ =>
    show temporal p.event φ = @decide (P.LeafHolds ι σ n φ) (Classical.propDecidable _)
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    exact htemp p pr rs hσ h φ (mem_temporalLeaves hq hl)
  | inr c => rfl

/-- Without a universal symmetric pin, every timepoint is visible. -/
theorem visible_of_universalPins_nil {S : EventSchema} (h : S.universalPins = []) (σ : Trace)
    (e : Event) (k : Nat) : S.Visible σ e k :=
  Or.inl h

/-- **Global semantics.** Without a universal symmetric pin, a leaf holds at a decision exactly
when its pinned form holds there with every timepoint visible. -/
theorem leafHolds_iff_global {ι : ImplChoices} {P : PolicySet} {σ : Trace} {n : Nat}
    {φ : Formula} (h : P.schema.universalPins = []) :
    P.LeafHolds ι σ n φ ↔
      ∃ p, σ[n]? = some p ∧
        Sat ι P.tickRate σ p.event (fun _ => True) Valuation.empty n (φ.injectPins P.schema) := by
  unfold PolicySet.LeafHolds
  refine exists_congr fun p => and_congr_right fun _ => ?_
  exact sat_congr _ _ n fun k _ => ⟨rfl, ⟨fun _ => trivial, fun _ => Or.inl h⟩⟩

end Dogwood.Thm
