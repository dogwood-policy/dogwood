import Dogwood.Examples.RateLimit
import Dogwood.Thm.Partition
import Dogwood.Thm.Scale

/-!
# Worked example: key isolation

Under an event schema with a universal symmetric pin, such as the default schema's caller pin, a
temporal condition is key-local: a decision observes only the events of its own key. So no
caller's events can change another caller's decisions: in the rate limit of
`Dogwood.Examples.RateLimit`, one caller cannot use up another's quota.

* **A decision depends on its key's events only** (`authorize_eq_of_partitionOf_eq`): for any
  policy set whose schema has a universal pin, two traces suited to partitioned evaluation
  (`EventSchema.Partitionable`) decide the same event alike, at positions where the event's
  partition, the events of its key up to it with their timestamps, is the same.
* **For the rate limit** (`requestLimit_isolated`): the corollary for
  `Dogwood.Examples.RateLimit.requestLimit`.

The partitions must agree with their timestamps, and that is not automatic: an implementation
that stamps one log for all keys may stamp an event of one key one tick later because another
key's event arrived at the same reading (`Dogwood.Examples.PartitionedStamps`). The guarantee is
about the stamped traces.
-/

namespace Dogwood.Examples.KeyIsolation

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples

/-- **A decision under a universal pin depends on its key's events only**: on two traces suited
to partitioned evaluation, an event decided at two positions whose partitions agree is decided
alike, under every reading. -/
theorem authorize_eq_of_partitionOf_eq {ι : ImplChoices} {P : PolicySet}
    {ω : Provider.Providers} {σ₁ σ₂ : Trace} {n₁ n₂ : Nat} {p₁ p₂ : TimePoint}
    (hpins : P.schema.universalPins ≠ [])
    (hσ₁ : P.schema.Partitionable σ₁) (hσ₂ : P.schema.Partitionable σ₂)
    (hp₁ : σ₁[n₁]? = some p₁) (hp₂ : σ₂[n₂]? = some p₂) (he : p₁.event = p₂.event)
    (hpart : partitionOf P.schema σ₁ n₁ p₁.event = partitionOf P.schema σ₂ n₂ p₂.event) :
    P.authorize ι ω σ₁ n₁ = P.authorize ι ω σ₂ n₂ := by
  unfold PolicySet.authorize
  refine decideWith_congr_event (by rw [hp₁, hp₂]; simp [he]) fun q pr rs hq ha => ?_
  rw [hp₁] at hq
  cases hq
  simp only [PolicySet.respond]
  refine supervaluate_congr fun ι' _ => ?_
  have hleaves : P.leaves ι' ω σ₁ n₁ p₁.event = P.leaves ι' ω σ₂ n₂ p₁.event := by
    simp only [PolicySet.leaves, Leaves.mk.injEq, and_true]
    funext φ
    refine decide_eq_decide.mpr ?_
    rw [leafHolds_iff_partition hpins hσ₁ hp₁ ha.kind,
      leafHolds_iff_partition hpins hσ₂ hp₂ (he ▸ ha.kind), hpart, he]
  rw [hleaves]

/-- **One caller cannot use up another's quota**: in the rate limit, two traces suited to
partitioned evaluation decide an event of a caller's alike wherever the caller's events up to it,
with their timestamps, are the same, whatever the other callers did. -/
theorem requestLimit_isolated {ι : ImplChoices} {ω : Provider.Providers} {w : Window}
    {n : Int64} {σ₁ σ₂ : Trace} {n₁ n₂ : Nat} {p₁ p₂ : TimePoint}
    (hσ₁ : RateLimit.schema.Partitionable σ₁) (hσ₂ : RateLimit.schema.Partitionable σ₂)
    (hp₁ : σ₁[n₁]? = some p₁) (hp₂ : σ₂[n₂]? = some p₂) (he : p₁.event = p₂.event)
    (hpart : partitionOf RateLimit.schema σ₁ n₁ p₁.event =
      partitionOf RateLimit.schema σ₂ n₂ p₂.event) :
    (RateLimit.requestLimit w n).authorize ι ω σ₁ n₁ =
      (RateLimit.requestLimit w n).authorize ι ω σ₂ n₂ :=
  authorize_eq_of_partitionOf_eq (by rw [show (RateLimit.requestLimit w n).schema =
      RateLimit.schema from rfl, RateLimit.universalPins_schema]; simp)
    hσ₁ hσ₂ hp₁ hp₂ he hpart

end Dogwood.Examples.KeyIsolation
