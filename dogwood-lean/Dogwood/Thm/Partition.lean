import Dogwood.Thm.Slice
import Dogwood.Thm.Temporal
import Dogwood.Spec.Decision

/-!
# Key-local semantics is evaluation over the decision's partition

Under a universal symmetric pin, the specification makes visible to a decision exactly the
events that are *mine* (`EventSchema.Mine`). An implementation that partitions its history files
each event under its partition key (`EventSchema.partitionKey`), the logged values of the pinned
fields, and evaluates a decision over the decision event's partition.

* `mine_iff`: an event is mine exactly when its partition key is the decision event's, when the
  event is of a declared signature and logs every pinned field, and the decision event's logged
  pin fields are its request-side values;
* `visible_iff_partitionKey`: on a `Partitionable` trace, the timepoints visible to a decision
  are those of the decision event's partition;
* `leafHolds_iff_partition`: on such a trace, a temporal leaf holds at a decision exactly when it
  holds at the last timepoint of the decision's partition, read as a trace of its own with every
  timepoint visible.

`leafHolds_iff_partition` reads the partition with the stamps of the single stamped trace.
Partitioned evaluation with each partition's log stamped on its own is
`PolicySet.PartLeafHolds` (`Dogwood.Thm.Partitioned`, `partLeafHolds_iff_leafHolds`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-- **Mine is the same partition.** -/
theorem mine_iff {S : EventSchema} {e ev : Event}
    (hdecl : ∃ s ∈ S, s.action = ev.action ∧ s.kind = ev.kind)
    (hlog : ∀ pin ∈ S.universalPins, (recordPath? ev.logged pin.field).isSome)
    (hsym : ∀ pin ∈ S.universalPins,
      (recordPath? e.logged pin.field).map .val = pin.ref.toTerm.eval? e Valuation.empty) :
    S.Mine e ev ↔ S.partitionKey ev = S.partitionKey e := by
  simp only [EventSchema.Mine, EventSchema.partitionKey]
  rw [List.map_inj_left]
  constructor
  · rintro ⟨_, h⟩ pin hpin
    obtain ⟨w, hw, he⟩ := h pin hpin
    have hs := hsym pin hpin
    rw [he] at hs
    cases hel : recordPath? e.logged pin.field with
    | none => rw [hel] at hs; cases hs
    | some w' =>
      rw [hel] at hs
      simp only [Option.map_some, Option.some.injEq, TVal.val.injEq] at hs
      rw [hw, hs]
  · intro h
    refine ⟨hdecl, fun pin hpin => ?_⟩
    have hp := h pin hpin
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hlog pin hpin)
    refine ⟨w, hw, ?_⟩
    rw [← hsym pin hpin, ← hp, hw]
    rfl

/-- **Visible is the same partition.** On a trace that suits partitioned evaluation, under a
universal symmetric pin, the timepoints visible to a decision are exactly those whose event has
the decision event's partition key. -/
theorem visible_iff_partitionKey {S : EventSchema} {σ : Trace} (hpins : S.universalPins ≠ [])
    (hσ : S.Partitionable σ) {n : Nat} {p : TimePoint} (hp : σ[n]? = some p)
    (hk : S.isDecisionKind p.event.kind = true) (k : Nat) :
    S.Visible σ p.event k ↔
      ∃ q, σ[k]? = some q ∧ S.partitionKey q.event = S.partitionKey p.event := by
  simp only [EventSchema.Visible, hpins, false_or]
  refine exists_congr fun q => ?_
  constructor
  · rintro ⟨hq, hm⟩
    exact ⟨hq, (mine_iff (hσ.declared k q hq) (hσ.logged k q hq) (hσ.symmetric n p hp hk)).mp hm⟩
  · rintro ⟨hq, hkey⟩
    exact ⟨hq, (mine_iff (hσ.declared k q hq) (hσ.logged k q hq) (hσ.symmetric n p hp hk)).mpr hkey⟩

/-- The events of `σ[0] … σ[n]` that share the partition key of the event `e`. -/
def partitionOf (S : EventSchema) (σ : Trace) (n : Nat) (e : Event) : Trace :=
  (σ.take (n + 1)).filter fun q => decide (S.partitionKey q.event = S.partitionKey e)

/-- **Key-local semantics is evaluation over the partition.** On a trace that suits partitioned
evaluation, under a universal symmetric pin, a temporal leaf holds at a decision
exactly when its pinned form holds at the last timepoint of the decision event's partition, read
as a trace of its own with every timepoint visible. -/
theorem leafHolds_iff_partition {ι : ImplChoices} {P : PolicySet} {σ : Trace} {n : Nat}
    {p : TimePoint} {φ : Formula} (hpins : P.schema.universalPins ≠ [])
    (hσ : P.schema.Partitionable σ) (hp : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) :
    P.LeafHolds ι σ n φ ↔
      Sat ι P.tickRate (partitionOf P.schema σ n p.event) p.event (fun _ => True) Valuation.empty
        ((partitionOf P.schema σ n p.event).length - 1) (φ.injectPins P.schema) := by
  have hn : n < σ.length := by
    rcases Nat.lt_or_ge n σ.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hp; cases hp
  have hpn : σ[n] = p := by rw [List.getElem?_eq_getElem hn] at hp; exact Option.some.inj hp
  generalize hP : (fun q : TimePoint => decide (P.schema.partitionKey q.event =
    P.schema.partitionKey p.event)) = inPart
  have hpart : partitionOf P.schema σ n p.event = (σ.take (n + 1)).filter inPart := by
    rw [← hP]; rfl
  obtain ⟨f, hf⟩ := subTrace_filter σ inPart (n + 1) (by omega)
  rw [hpart]
  have hmem : inPart p = true := by rw [← hP]; simp
  have hlen : ((σ.take (n + 1)).filter inPart).length - 1 <
      ((σ.take (n + 1)).filter inPart).length := by
    have : p ∈ (σ.take (n + 1)).filter inPart := by
      rw [List.mem_filter]
      refine ⟨?_, hmem⟩
      rw [take_succ_eq hn, hpn]
      exact List.mem_append_right _ (List.mem_singleton_self p)
    have := List.length_pos_of_mem this
    omega
  rw [sat_slice hf _ Valuation.noTp_empty _ hlen]
  -- The newest event of the partition is the decision event.
  have hfn : f (((σ.take (n + 1)).filter inPart).length - 1) = n := by
    obtain ⟨i, hi, hfi⟩ := (hf.vis_iff n).mp ⟨by omega, p, hp, hmem⟩
    have hlast := ((hf.vis_iff (f (((σ.take (n + 1)).filter inPart).length - 1))).mpr
      ⟨_, hlen, rfl⟩).1
    by_cases hil : i < ((σ.take (n + 1)).filter inPart).length - 1
    · have := hf.mono i _ hil hlen; omega
    · have : i = ((σ.take (n + 1)).filter inPart).length - 1 := by omega
      rw [← this]; exact hfi
  rw [hfn]
  unfold PolicySet.LeafHolds
  constructor
  · rintro ⟨q, hq, hs⟩
    rw [hp] at hq; cases hq
    refine (sat_congr _ _ n ?_).mp hs
    intro k hk'
    refine ⟨rfl, ?_⟩
    rw [visible_iff_partitionKey hpins hσ hp hk k]
    constructor
    · rintro ⟨q, hq, hkey⟩
      exact ⟨by omega, q, hq, by rw [← hP]; simp [hkey]⟩
    · rintro ⟨_, q, hq, hin⟩
      exact ⟨q, hq, by rw [← hP] at hin; simpa using hin⟩
  · intro hs
    refine ⟨p, hp, (sat_congr _ _ n ?_).mp hs⟩
    intro k hk'
    refine ⟨rfl, ?_⟩
    rw [visible_iff_partitionKey hpins hσ hp hk k]
    constructor
    · rintro ⟨_, q, hq, hin⟩
      exact ⟨q, hq, by rw [← hP] at hin; simpa using hin⟩
    · rintro ⟨q, hq, hkey⟩
      exact ⟨by omega, q, hq, by rw [← hP]; simp [hkey]⟩

end Dogwood.Thm
