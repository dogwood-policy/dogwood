import Dogwood.Spec.Partitioned
import Dogwood.Thm.Partition
import Dogwood.Thm.Ingest
import Dogwood.Thm.Decision
import Dogwood.Thm.Scale

/-!
# Partitioned evaluation, with one log per partition key, each stamped on its own

The theorems about `PolicySet.PartLeafHolds` and `PolicySet.authorizePart`
(`Dogwood.Spec.Partitioned`).

* **Stamping** (`stamp_take`, `stamp_append`, `stamp_filter_of_strictlyIncreasing`,
  `eq_stamp_iff`): stamping a prefix is the prefix of the stamped trace; on readings that strictly
  increase, stamping a sublist is filtering the stamped trace; and a trace is the stamping of a log
  exactly when it has the log's events, each stamped after the stamp before it, as `stampAfter`
  stamps.
* **The unfolding over a key's own log** (`partLeafHolds_iff`, `partLeafHolds_iff_keyLog`): the
  value of a leaf at arrival `n` is `Sat` of the pinned leaf over the key's log, stamped on its
  own, at the decision's position in it, every timepoint visible. `partLeafHolds_iff_keyLog` takes
  the key's whole log, so that a later arrival changes no earlier value
  (`partLeafHolds_append`).
* **What the crate computes** (`partLeafHolds_iff_of_strictlyIncreasing`): on a partition whose
  readings strictly increase, stamping changes nothing, and the value is the leaf's over the
  partition with its own timestamps.
* **Agreement with the single stamped log**: without a universal symmetric pin
  (`partLeafHolds_iff_leafHolds_of_noPins`, `authorizePart_eq_authorize_of_noPins`), and when the
  readings strictly increase across the whole stream (`partLeafHolds_iff_leafHolds`,
  `authorizePart_eq_authorize`). Both rest on `leafHolds_iff_partition` and on per-partition
  stamping being the partition of the stamped stream (`stamp_partitionLog_of_strictlyIncreasing`;
  `partLeafHolds_iff_leafHolds_of_stamp` states the agreement under that equation alone).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (EntityUID Response)

/-! ## Stamping -/

/-- **Stamping a prefix** is the prefix of the stamped trace: a stamp depends only on the
readings before it. -/
theorem stamp_go_take : ∀ (σ : Trace) (last : Option Int) (m : Nat),
    Trace.stamp.go last (σ.take m) = (Trace.stamp.go last σ).take m
  | [], _, m => by simp [Trace.stamp.go]
  | _ :: _, _, 0 => by simp [Trace.stamp.go]
  | p :: σ, last, m + 1 => by
    simp only [List.take_succ_cons, Trace.stamp.go]
    rw [stamp_go_take σ _ m]

theorem stamp_take (σ : Trace) (m : Nat) : Trace.stamp (σ.take m) = σ.stamp.take m :=
  stamp_go_take σ none m

/-- **Stamping an extended trace** stamps the extension after the last stamp of the trace. -/
theorem stamp_go_append : ∀ (σ τ : Trace) (last : Option Int),
    Trace.stamp.go last (σ ++ τ) =
      Trace.stamp.go last σ ++ Trace.stamp.go (((Trace.stamp.go last σ).getLast?.map (·.ts)).or last) τ
  | [], τ, last => by simp [Trace.stamp.go, Option.or]
  | p :: σ, τ, last => by
    simp only [List.cons_append, Trace.stamp.go]
    rw [stamp_go_append σ τ, List.getLast?_cons]
    cases (Trace.stamp.go (some (stampAfter last p.ts)) σ).getLast? <;> rfl

theorem stamp_append (σ τ : Trace) :
    (σ ++ τ).stamp = σ.stamp ++ Trace.stamp.go (σ.stamp.getLast?.map (·.ts)) τ := by
  have := stamp_go_append σ τ none
  rw [Option.or_none] at this
  exact this

/-- Stamping keeps the event at every position. -/
theorem stamp_getElem?_event (σ : Trace) (i : Nat) :
    (σ.stamp[i]?).map (·.event) = (σ[i]?).map (·.event) := by
  rw [← List.getElem?_map, ← List.getElem?_map, stamp_events]

/-- Stamping keeps the event at every position. -/
theorem stamp_getElem?_some {σ : Trace} {i : Nat} {p : TimePoint} (h : σ[i]? = some p) :
    ∃ q, σ.stamp[i]? = some q ∧ q.event = p.event := by
  have := stamp_getElem?_event σ i
  rw [h] at this
  cases hs : σ.stamp[i]? with
  | none => rw [hs] at this; cases this
  | some q => rw [hs] at this; exact ⟨q, rfl, Option.some.inj this⟩

/-- Every position of the stamped trace has the event of the same position of the trace. -/
theorem getElem?_of_stamp_some {σ : Trace} {i : Nat} {q : TimePoint} (h : σ.stamp[i]? = some q) :
    ∃ p, σ[i]? = some p ∧ q.event = p.event := by
  have := stamp_getElem?_event σ i
  rw [h] at this
  cases hs : σ[i]? with
  | none => rw [hs] at this; cases this
  | some p => rw [hs] at this; exact ⟨p, rfl, Option.some.inj this⟩

/-- **On readings that strictly increase, stamping a sublist of them is filtering the stamped
trace**: every stamp is its reading, in the whole stream and in every sublist. -/
theorem stamp_filter_of_strictlyIncreasing {ρ : Trace} (h : ρ.StrictlyIncreasing)
    (g : TimePoint → Bool) : Trace.stamp (ρ.filter g) = ρ.stamp.filter g := by
  rw [stamp_of_strictlyIncreasing h, stamp_of_strictlyIncreasing (h.filter g)]

/-- **What stamping is, pointwise.** The trace `τ` is the stamping of the log `L` (each entry
with its clock reading) exactly when it has `L`'s length and, at every position, `L`'s event,
stamped with `stampAfter` after the stamp before it in `τ`. -/
theorem eq_stamp_go_iff : ∀ (L τ : Trace) (last : Option Int),
    τ = Trace.stamp.go last L ↔ τ.length = L.length ∧ ∀ i p q, L[i]? = some p → τ[i]? = some q →
      q.event = p.event ∧ q.ts = stampAfter (((τ.take i).getLast?.map (·.ts)).or last) p.ts
  | [], τ, last => by
    simp only [Trace.stamp.go, List.length_nil, List.getElem?_nil]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
  | p :: L, [], last => by
    simp [Trace.stamp.go]
  | p :: L, q :: τ, last => by
    simp only [Trace.stamp.go, List.cons.injEq, List.length_cons, Nat.add_right_cancel_iff]
    rw [eq_stamp_go_iff L τ]
    constructor
    · rintro ⟨rfl, hlen, h⟩
      refine ⟨hlen, ?_⟩
      intro i p' q' hp' hq'
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hp' hq'
        subst hp' hq'
        simp [Option.or]
      | succ i =>
        simp only [List.getElem?_cons_succ] at hp' hq'
        obtain ⟨he, hts⟩ := h i p' q' hp' hq'
        refine ⟨he, ?_⟩
        rw [hts, List.take_succ_cons, List.getLast?_cons]
        cases (τ.take i).getLast? <;> rfl
    · rintro ⟨hlen, h⟩
      obtain ⟨he₀, hts₀⟩ := h 0 p q rfl rfl
      have hq : q = ⟨stampAfter last p.ts, p.event⟩ := by
        simp [Option.or] at hts₀
        cases q
        simp only at he₀ hts₀
        rw [he₀, hts₀]
      refine ⟨hq, hlen, fun i p' q' hp' hq' => ?_⟩
      obtain ⟨he, hts⟩ := h (i + 1) p' q' (by simpa using hp') (by simpa using hq')
      refine ⟨he, ?_⟩
      rw [hts, List.take_succ_cons, List.getLast?_cons, hq]
      cases (τ.take i).getLast? <;> rfl

theorem eq_stamp_iff {L τ : Trace} :
    τ = L.stamp ↔ τ.length = L.length ∧ ∀ i p q, L[i]? = some p → τ[i]? = some q →
      q.event = p.event ∧ q.ts = stampAfter ((τ.take i).getLast?.map (·.ts)) p.ts := by
  have := eq_stamp_go_iff L τ none
  simp only [Option.or_none] at this
  exact this

/-- Satisfaction at a timepoint of a prefix of the trace is satisfaction in the trace. -/
theorem sat_take {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}
    {v : Valuation} {j m : Nat} (φ : Formula) (hj : j < m) :
    Sat ι rate (σ.take m) e vis v j φ ↔ Sat ι rate σ e vis v j φ :=
  sat_congr φ v j fun _ hk => ⟨List.getElem?_take_of_lt (by omega), Iff.rfl⟩

/-! ## Partition logs -/

/-- The partition log of a stream is `partitionOf` of it. -/
theorem partitionLog_eq_partitionOf (S : EventSchema) (ρ : Trace) (n : Nat) (e : Event) :
    S.partitionLog ρ n e = partitionOf S ρ n e := rfl

/-- **The decision is the last entry of its partition log**: the partition log at arrival `n` is
the log of the key before `n`, followed by arrival `n`. -/
theorem partitionLog_eq {S : EventSchema} {ρ : Trace} {n : Nat} {p : TimePoint}
    (hp : ρ[n]? = some p) :
    S.partitionLog ρ n p.event = S.keyLog (ρ.take n) (S.partitionKey p.event) ++ [p] := by
  obtain ⟨hn, hpn⟩ := List.getElem?_eq_some_iff.mp hp
  unfold EventSchema.partitionLog EventSchema.keyLog
  rw [take_succ_filter ρ _ hn, hpn]
  simp

/-- The decision's position in its partition log is the number of arrivals of its key before
it. -/
theorem length_partitionLog_sub_one {S : EventSchema} {ρ : Trace} {n : Nat} {p : TimePoint}
    (hp : ρ[n]? = some p) :
    (S.partitionLog ρ n p.event).length - 1 = (S.keyLog (ρ.take n) (S.partitionKey p.event)).length := by
  rw [partitionLog_eq hp, List.length_append, List.length_singleton, Nat.add_sub_cancel]

/-- The key's whole log is its partition log at arrival `n`, followed by the later arrivals of
the key. -/
theorem keyLog_eq_partitionLog_append (S : EventSchema) (ρ : Trace) (n : Nat) (e : Event) :
    S.keyLog ρ (S.partitionKey e) =
      S.partitionLog ρ n e ++ S.keyLog (ρ.drop (n + 1)) (S.partitionKey e) := by
  unfold EventSchema.partitionLog EventSchema.keyLog
  rw [← List.filter_append, List.take_append_drop]

/-- Without a universal symmetric pin, every event has the same key: a key's log is the whole
stream. -/
theorem keyLog_of_noPins {S : EventSchema} (h : S.universalPins = []) (ρ : Trace) (e : Event) :
    S.keyLog ρ (S.partitionKey e) = ρ := by
  unfold EventSchema.keyLog EventSchema.partitionKey
  simp [h]

/-- **Per-partition stamping is the partition of the stamped stream, on readings that strictly
increase.** Stamping the partition log of `e` on its own gives the partition of `e` in the
stamped stream. -/
theorem stamp_partitionLog_of_strictlyIncreasing {S : EventSchema} {ρ : Trace}
    (h : ρ.StrictlyIncreasing) (n : Nat) (e : Event) :
    (S.partitionLog ρ n e).stamp = partitionOf S ρ.stamp n e := by
  rw [stamp_of_strictlyIncreasing h, partitionLog_eq_partitionOf]
  exact stamp_of_strictlyIncreasing (σ := partitionOf S ρ n e)
    (by unfold partitionOf; exact (h.take (n + 1)).filter _)

/-- A trace suits partitioned evaluation exactly when its stamping does: stamping changes no
event. -/
theorem partitionable_of_events {S : EventSchema} {σ₁ σ₂ : Trace}
    (hev : ∀ (k : Nat) (q : TimePoint), σ₂[k]? = some q → ∃ p, σ₁[k]? = some p ∧ q.event = p.event)
    (h : S.Partitionable σ₁) : S.Partitionable σ₂ where
  declared k q hq := by
    obtain ⟨p, hp, he⟩ := hev k q hq
    rw [he]; exact h.declared k p hp
  logged k q hq := by
    obtain ⟨p, hp, he⟩ := hev k q hq
    rw [he]; exact h.logged k p hp
  symmetric k q hq := by
    obtain ⟨p, hp, he⟩ := hev k q hq
    rw [he]; exact h.symmetric k p hp

theorem partitionable_stamp_iff {S : EventSchema} {ρ : Trace} :
    S.Partitionable ρ.stamp ↔ S.Partitionable ρ := by
  constructor
  · refine partitionable_of_events fun k q hq => ?_
    obtain ⟨p, hp, he⟩ := stamp_getElem?_some hq
    exact ⟨p, hp, he.symm⟩
  · exact partitionable_of_events fun k q hq => getElem?_of_stamp_some hq

/-! ## The value of a leaf over its key's log -/

variable {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers} {ρ : Trace} {n : Nat}
  {p : TimePoint} {φ : Formula}

/-- **The unfolding**: at arrival `n`, whose arrival is `p`, a leaf's value under partitioned
evaluation is `Sat` of the pinned leaf over the partition log of `p`'s event, stamped on its own,
at its last position, every timepoint visible. -/
theorem partLeafHolds_iff (hp : ρ[n]? = some p) :
    P.PartLeafHolds ι ρ n φ ↔
      Sat ι P.tickRate (P.schema.partitionLog ρ n p.event).stamp p.event (fun _ => True)
        Valuation.empty ((P.schema.partitionLog ρ n p.event).length - 1)
        (φ.injectPins P.schema) := by
  unfold PolicySet.PartLeafHolds
  constructor
  · rintro ⟨q, hq, hs⟩
    rw [hp] at hq
    cases hq
    exact hs
  · exact fun hs => ⟨p, hp, hs⟩

/-- **The unfolding over a key's own log.** Let `L` be the log of the decision event's key: the
arrivals of `ρ` with that key, in order, each with its reading (`EventSchema.keyLog`). At arrival
`n`, whose arrival is `p`, a leaf's value under partitioned evaluation is `Sat` of the pinned leaf
over `L`, stamped on its own, at the decision's position in `L` (the number of arrivals of the key
before `n`), with every timepoint visible. -/
theorem partLeafHolds_iff_keyLog (hp : ρ[n]? = some p) :
    P.PartLeafHolds ι ρ n φ ↔
      Sat ι P.tickRate (P.schema.keyLog ρ (P.schema.partitionKey p.event)).stamp p.event
        (fun _ => True) Valuation.empty
        (P.schema.keyLog (ρ.take n) (P.schema.partitionKey p.event)).length
        (φ.injectPins P.schema) := by
  rw [partLeafHolds_iff hp, length_partitionLog_sub_one hp,
    keyLog_eq_partitionLog_append P.schema ρ n p.event]
  have hlen : (P.schema.keyLog (ρ.take n) (P.schema.partitionKey p.event)).length <
      (P.schema.partitionLog ρ n p.event).length := by
    rw [partitionLog_eq hp, List.length_append, List.length_singleton]
    omega
  have htake : (P.schema.partitionLog ρ n p.event).stamp =
      (Trace.stamp (P.schema.partitionLog ρ n p.event ++
        P.schema.keyLog (ρ.drop (n + 1)) (P.schema.partitionKey p.event))).take
          (P.schema.partitionLog ρ n p.event).length := by
    rw [← stamp_take, List.take_left]
  rw [htake, sat_take _ hlen]

/-- **Past-only.** A later arrival changes no earlier value. -/
theorem partLeafHolds_append (τ : Trace) (hn : n < ρ.length) :
    P.PartLeafHolds ι (ρ ++ τ) n φ ↔ P.PartLeafHolds ι ρ n φ := by
  have hlog : ∀ e, P.schema.partitionLog (ρ ++ τ) n e = P.schema.partitionLog ρ n e := by
    intro e
    unfold EventSchema.partitionLog
    rw [List.take_append_of_le_length (by omega)]
  unfold PolicySet.PartLeafHolds
  simp only [List.getElem?_append_left hn, hlog]

/-- **What the crate's partitioned mode computes.** When the readings of the decision's partition
strictly increase, stamping the partition changes nothing: a leaf's value under partitioned
evaluation is `Sat` of the pinned leaf over the partition with the events' own timestamps, at its
last position, every timepoint visible. That is what an authorizer built with
`AuthorizerBuilder::partition_temporal()` evaluates. -/
theorem partLeafHolds_iff_of_strictlyIncreasing (hp : ρ[n]? = some p)
    (h : (P.schema.partitionLog ρ n p.event).StrictlyIncreasing) :
    P.PartLeafHolds ι ρ n φ ↔
      Sat ι P.tickRate (P.schema.partitionLog ρ n p.event) p.event (fun _ => True)
        Valuation.empty ((P.schema.partitionLog ρ n p.event).length - 1)
        (φ.injectPins P.schema) := by
  rw [partLeafHolds_iff hp, stamp_of_strictlyIncreasing h]

/-! ## Agreement with the single stamped log -/

/-- **Without a universal symmetric pin, partitioned evaluation is the single-log semantics.**
Every event has the same key, so the one partition's log is the whole stream, and its stamping is
the stamped stream. -/
theorem partLeafHolds_iff_leafHolds_of_noPins (h : P.schema.universalPins = []) :
    P.PartLeafHolds ι ρ n φ ↔ P.LeafHolds ι ρ.stamp n φ := by
  have hlog : ∀ e, P.schema.partitionLog ρ n e = ρ.take (n + 1) :=
    fun e => keyLog_of_noPins h _ e
  have hvis : ∀ e k, ((fun _ => True) k ↔ P.schema.Visible ρ.stamp e k) := by
    intro e k
    simp [EventSchema.Visible, h]
  cases hρ : ρ[n]? with
  | none =>
    have hs : ρ.stamp[n]? = none := by
      have := stamp_getElem?_event ρ n
      rw [hρ] at this
      cases hs : ρ.stamp[n]? with
      | none => rfl
      | some q => rw [hs] at this; cases this
    unfold PolicySet.PartLeafHolds PolicySet.LeafHolds
    simp [hρ, hs]
  | some p =>
    obtain ⟨hn, -⟩ := List.getElem?_eq_some_iff.mp hρ
    obtain ⟨q, hq, hqe⟩ := stamp_getElem?_some hρ
    have hlen : (ρ.take (n + 1)).length - 1 = n := by
      rw [List.length_take]
      omega
    rw [partLeafHolds_iff hρ, hlog, hlen, stamp_take, sat_take _ (Nat.lt_succ_self n)]
    unfold PolicySet.LeafHolds
    constructor
    · intro hs
      refine ⟨q, hq, ?_⟩
      rw [hqe]
      exact (sat_congr _ _ n fun k _ => ⟨rfl, hvis p.event k⟩).mp hs
    · rintro ⟨q', hq', hs⟩
      rw [hq] at hq'
      cases hq'
      rw [hqe] at hs
      exact (sat_congr _ _ n fun k _ => ⟨rfl, hvis p.event k⟩).mpr hs

/-- **Agreement when per-partition stamping is the partition of the stamped stream.** On a
stream that suits partitioned evaluation, under a universal symmetric pin, at a decision event
whose partition log, stamped on its own, is its partition in the stamped stream, a leaf's value
under partitioned evaluation is its value in the single-log semantics. -/
theorem partLeafHolds_iff_leafHolds_of_stamp (hpins : P.schema.universalPins ≠ [])
    (hσ : P.schema.Partitionable ρ) (hp : ρ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true)
    (hst : (P.schema.partitionLog ρ n p.event).stamp = partitionOf P.schema ρ.stamp n p.event) :
    P.PartLeafHolds ι ρ n φ ↔ P.LeafHolds ι ρ.stamp n φ := by
  obtain ⟨q, hq, hqe⟩ := stamp_getElem?_some hp
  have hl : (P.schema.partitionLog ρ n p.event).length =
      (partitionOf P.schema ρ.stamp n p.event).length := by
    rw [← hst, stamp_length]
  rw [leafHolds_iff_partition hpins (partitionable_stamp_iff.mpr hσ) hq (by rw [hqe]; exact hk),
    partLeafHolds_iff hp, hl, hst, hqe]

/-- **Agreement when the readings strictly increase across the whole stream.** On a stream that
suits partitioned evaluation, whose readings strictly increase in arrival order, a leaf's value
at a decision event under partitioned evaluation is its value in the single-log semantics. (The
stamped stream is then the stream itself, `stamp_of_strictlyIncreasing`.) -/
theorem partLeafHolds_iff_leafHolds (hinc : ρ.StrictlyIncreasing)
    (hσ : P.schema.Partitionable ρ) (hp : ρ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) :
    P.PartLeafHolds ι ρ n φ ↔ P.LeafHolds ι ρ.stamp n φ := by
  by_cases hpins : P.schema.universalPins = []
  · exact partLeafHolds_iff_leafHolds_of_noPins hpins
  · exact partLeafHolds_iff_leafHolds_of_stamp hpins hσ hp hk
      (stamp_partitionLog_of_strictlyIncreasing hinc n p.event)

/-! ## Decisions -/

/-- **Without a universal symmetric pin, the partitioned decision is the single-log decision.** -/
theorem authorizePart_eq_authorize_of_noPins (h : P.schema.universalPins = []) :
    P.authorizePart ι ω ρ n = P.authorize ι ω ρ.stamp n := by
  unfold PolicySet.authorizePart PolicySet.authorize
  refine decideWith_congr_event (stamp_getElem?_event ρ n).symm fun q pr rs _ _ => ?_
  simp only [PolicySet.respondPart, PolicySet.respond]
  refine supervaluate_congr fun ι' _ => ?_
  have hleaves : P.partLeaves ι' ω ρ n q.event = P.leaves ι' ω ρ.stamp n q.event := by
    simp only [PolicySet.partLeaves, PolicySet.leaves, Leaves.mk.injEq, and_true]
    funext φ
    exact decide_eq_decide.mpr (partLeafHolds_iff_leafHolds_of_noPins h)
  rw [hleaves]

/-- **When the readings strictly increase across the whole stream, the partitioned decision is
the single-log decision**, on a stream that suits partitioned evaluation. -/
theorem authorizePart_eq_authorize (hinc : ρ.StrictlyIncreasing) (hσ : P.schema.Partitionable ρ) :
    P.authorizePart ι ω ρ n = P.authorize ι ω ρ.stamp n := by
  unfold PolicySet.authorizePart PolicySet.authorize
  refine decideWith_congr_event (stamp_getElem?_event ρ n).symm fun q pr rs hq ha => ?_
  simp only [PolicySet.respondPart, PolicySet.respond]
  refine supervaluate_congr fun ι' _ => ?_
  have hleaves : P.partLeaves ι' ω ρ n q.event = P.leaves ι' ω ρ.stamp n q.event := by
    simp only [PolicySet.partLeaves, PolicySet.leaves, Leaves.mk.injEq, and_true]
    funext φ
    exact decide_eq_decide.mpr (partLeafHolds_iff_leafHolds hinc hσ hq ha.kind)
  rw [hleaves]

/-- An admitted decision event is decided by the partitioned response, or fails closed for a
temporal error. -/
theorem authorizePart_of_admits (hp : ρ[n]? = some p) {pr rs : EntityUID}
    (h : P.Admits P.policies ω p pr rs) :
    P.authorizePart ι ω ρ n = match P.respondPart ι ω ρ n p.event pr rs with
      | some r => .decided r
      | none => .failClosed .temporalError :=
  decideWith_of_admits hp h

end Dogwood.Thm
