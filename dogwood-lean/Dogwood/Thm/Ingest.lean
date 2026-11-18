import Dogwood.Spec.Ingest
import Dogwood.Thm.Log
import Dogwood.Thm.Trace

/-!
# Ingestion stamps events, and keeps conformance

* `lt_stampAfter`, `stampAfter_ge`, `stampAfter_of_lt`: a stamp comes after the last stamp, is at
  least its reading, and is its reading when the reading is after the last stamp; `stamps_entry`
  and `stampAfter_le_of_stamps`: ingestion's stamp is the least that `Arrival.Stamps` admits;
  `wellFormed_append_of_stamps`: any such stamp keeps the rule.
* `submit_strictlyIncreasing`, `ingest_strictlyIncreasing`: every log an authorizer builds by
  ingestion keeps the language's timestamp rule, by construction: an accepted event is stamped
  after the last (`wellFormed_append_entry`). Its decisions are made over a trace whose timestamps
  strictly increase.
* `conforming_submit`, `conforming_ingest`: every event of every log an authorizer builds by
  ingestion conforms to the event schema.
* `submit_accepted`, `submit_rejected`: a submission is either stamped, appended, and decided at
  its position, or rejected and left out of the log; `length_ingest` gives every submission a
  reply. `submit_nonconforming` rejects a nonconforming event, whatever the log. No event is
  rejected for its time.
* `ingest_events`: ingesting a trace's events in order, each with its timestamp as its clock
  reading, builds the log of its conforming events, stamped (`Trace.stamp`, the executable form
  of stamping). `ingest_readings` is the same for a recorded trace whose times are in seconds.
* `stamp_strictlyIncreasing`, `stamp_of_strictlyIncreasing`, `stamp_events`, `stamp_ge`:
  stamping makes the timestamps strictly increase, leaves alone readings that already do, keeps
  the events, and never stamps an event before its reading.
* `ingest_of_strictlyIncreasing`: on a trace of conforming events whose timestamps strictly
  increase, ingestion accepts every event at its own timestamp, and the reply to each event
  carries `PolicySet.authorize`'s outcome at its timepoint. Ingestion of such a trace is replay.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

variable {reading : UpdateReading} {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers}

/-! ## Stamps -/

/-- A stamp is at least its clock reading. -/
theorem stampAfter_ge (last : Option Int) (clock : Int) : clock ≤ stampAfter last clock := by
  cases last with
  | none => exact Int.le_refl _
  | some t => exact Int.le_max_left _ _

/-- A stamp comes after the last stamp. -/
theorem lt_stampAfter {last : Option Int} {t : Int} (h : last = some t) (clock : Int) :
    t < stampAfter last clock := by
  subst h
  show t < max clock (t + 1)
  have := Int.le_max_right clock (t + 1)
  omega

/-- A reading after the last stamp is the stamp. -/
theorem stampAfter_of_lt {last : Option Int} {clock : Int} (h : ∀ t, last = some t → t < clock) :
    stampAfter last clock = clock := by
  cases last with
  | none => rfl
  | some t =>
    have := h t rfl
    show max clock (t + 1) = clock
    exact Int.max_eq_left (by omega)

/-- **Ingestion's stamp is a stamp.** The entry ingestion makes of an arrival stamps it. -/
theorem stamps_entry (last : Option Int) (x : Arrival) : x.Stamps last (x.entry last) := by
  cases x with
  | event e clock => exact ⟨rfl, stampAfter_ge last clock, fun t ht => lt_stampAfter ht clock⟩
  | deploy rs => rfl

/-- **Ingestion's stamp is the least.** Every stamp of an event is at least the stamp ingestion
assigns it. -/
theorem stampAfter_le_of_stamps {last : Option Int} {e : Event} {clock : Int} {p : TimePoint}
    (h : (Arrival.event e clock).Stamps last (.event p)) : stampAfter last clock ≤ p.ts := by
  obtain ⟨_, hc, hl⟩ := h
  cases last with
  | none => exact hc
  | some t =>
    have := hl t rfl
    show max clock (t + 1) ≤ p.ts
    omega

/-! ## One submission -/

theorem submit_rejected {log : Log} {x : Arrival} {r : Rejection}
    (h : x.nonconformance? P = some r) :
    Log.submit reading ι P ω log x = (log, .rejected r) := by
  simp [Log.submit, h]

theorem submit_accepted {log : Log} {x : Arrival} (h : x.nonconformance? P = none) :
    Log.submit reading ι P ω log x =
      (log ++ [x.entry log.lastTs?], .accepted log.length
        (Log.decide reading ι P ω (log ++ [x.entry log.lastTs?]) log.length)) := by
  simp [Log.submit, h]

/-- **A nonconforming event is rejected**, whatever the log. -/
theorem submit_nonconforming (log : Log) {e : Event} {clock : Int}
    (h : ¬ e.Conforms P.actionSchema P.schema) :
    Log.submit reading ι P ω log (.event e clock) = (log, .rejected .nonconforming) :=
  submit_rejected (by simp [Arrival.nonconformance?, h])

/-- An event is accepted exactly when it conforms: no event is rejected for its time. -/
theorem nonconformance?_event_eq_none {e : Event} {clock : Int} :
    (Arrival.event e clock).nonconformance? P = none ↔ e.Conforms P.actionSchema P.schema := by
  unfold Arrival.nonconformance?
  by_cases hc : e.Conforms P.actionSchema P.schema <;> simp [hc]

/-- A deployment is never rejected. -/
theorem nonconformance?_deploy (rs : List DeployedRule) :
    (Arrival.deploy rs).nonconformance? P = none := rfl

theorem Log.lastTs?_append_event (log : Log) (p : TimePoint) :
    Log.lastTs? (log ++ [.event p]) = some p.ts := by
  simp [Log.lastTs?, Log.trace, Entry.event?]

theorem Log.lastTs?_append_deploy (log : Log) (rs : List DeployedRule) :
    Log.lastTs? (log ++ [.deploy rs]) = log.lastTs? := by
  simp [Log.lastTs?, Log.trace, Entry.event?]

/-- **Stamping keeps the rule.** Appending an arrival, stamped after the log's last event, keeps
the log's timestamps strictly increasing. -/
theorem wellFormed_append_entry {log : Log} (h : log.WellFormed) (x : Arrival) :
    Log.WellFormed (log ++ [x.entry log.lastTs?]) := by
  unfold Log.WellFormed
  rw [Log.trace_append]
  cases x with
  | deploy rs =>
    simpa [Log.WellFormed, Log.trace, Entry.event?, Arrival.entry, List.filterMap_cons] using h
  | event e clock =>
    have hp : Log.trace [Arrival.entry log.lastTs? (.event e clock)] =
        [⟨stampAfter log.lastTs? clock, e⟩] := rfl
    rw [hp, Trace.strictlyIncreasing_append_singleton]
    refine ⟨h, ?_⟩
    cases hl : log.trace.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at hl
      simp [hl]
    | some q =>
      exact Trace.StrictlyIncreasing.lt_of_getLast? h hl
        (lt_stampAfter (by simp [Log.lastTs?, hl]) clock)

/-- **Any stamp keeps the rule.** Appending an entry that stamps an arrival after the log's
last event keeps the log's timestamps strictly increasing. -/
theorem wellFormed_append_of_stamps {log : Log} (h : log.WellFormed) {x : Arrival} {y : Entry}
    (hs : x.Stamps log.lastTs? y) : Log.WellFormed (log ++ [y]) := by
  unfold Log.WellFormed
  rw [Log.trace_append]
  cases x with
  | deploy rs =>
    cases y with
    | event p => exact hs.elim
    | deploy rs' => simpa [Log.WellFormed, Log.trace, Entry.event?, List.filterMap_cons] using h
  | event e clock =>
    cases y with
    | deploy rs => exact hs.elim
    | event p =>
      obtain ⟨_, _, hl⟩ := hs
      have hp : Log.trace [Entry.event p] = [p] := rfl
      rw [hp, Trace.strictlyIncreasing_append_singleton]
      refine ⟨h, ?_⟩
      cases hlast : log.trace.getLast? with
      | none =>
        rw [List.getLast?_eq_none_iff] at hlast
        simp [hlast]
      | some q =>
        exact Trace.StrictlyIncreasing.lt_of_getLast? h hlast
          (hl q.ts (by simp [Log.lastTs?, hlast]))

/-- **A submission keeps the rule.** -/
theorem submit_strictlyIncreasing {log : Log} (h : log.WellFormed) (x : Arrival) :
    Log.WellFormed (Log.submit reading ι P ω log x).1 := by
  cases hr : x.nonconformance? P with
  | some r => rw [submit_rejected hr]; exact h
  | none => rw [submit_accepted hr]; exact wellFormed_append_entry h x

/-- **Ingestion keeps the rule.** Every log ingestion builds from a log that keeps it keeps it:
its timestamps strictly increase. -/
theorem ingest_strictlyIncreasing (xs : List Arrival) : ∀ {log : Log}, log.WellFormed →
    Log.WellFormed (Log.ingest reading ι P ω log xs).1 := by
  induction xs with
  | nil => intro log h; exact h
  | cons x xs ih =>
    intro log h
    exact ih (submit_strictlyIncreasing h x)

/-- Every log an authorizer builds from an empty log keeps the rule. -/
theorem ingest_strictlyIncreasing_nil (xs : List Arrival) :
    Log.WellFormed (Log.ingest reading ι P ω [] xs).1 :=
  ingest_strictlyIncreasing xs Trace.StrictlyIncreasing.nil

/-- **A submission keeps the log's events conforming.** -/
theorem conforming_submit {log : Log} (h : log.Conforming P) (x : Arrival) :
    Log.Conforming P (Log.submit reading ι P ω log x).1 := by
  cases hr : x.nonconformance? P with
  | some r => rw [submit_rejected hr]; exact h
  | none =>
    rw [submit_accepted hr]
    intro q hq
    rw [Log.trace_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact h q hq
    · cases x with
      | deploy rs => simp [Log.trace, Entry.event?, Arrival.entry] at hq
      | event e clock =>
        have hp : Log.trace [Arrival.entry log.lastTs? (.event e clock)] =
            [⟨stampAfter log.lastTs? clock, e⟩] := rfl
        rw [hp, List.mem_singleton] at hq
        subst hq
        exact nonconformance?_event_eq_none.mp hr

/-- **Ingestion keeps the log's events conforming.** -/
theorem conforming_ingest (xs : List Arrival) : ∀ {log : Log}, log.Conforming P →
    Log.Conforming P (Log.ingest reading ι P ω log xs).1 := by
  induction xs with
  | nil => intro log h; exact h
  | cons x xs ih =>
    intro log h
    exact ih (conforming_submit h x)

/-- Every event of every log an authorizer builds from an empty log conforms. -/
theorem conforming_ingest_nil (xs : List Arrival) :
    Log.Conforming P (Log.ingest reading ι P ω [] xs).1 :=
  conforming_ingest xs (fun _ h => by simp [Log.trace] at h)

/-- Every submission gets a reply. -/
theorem length_ingest (xs : List Arrival) : ∀ (log : Log),
    (Log.ingest reading ι P ω log xs).2.length = xs.length := by
  induction xs with
  | nil => intro log; rfl
  | cons x xs ih => intro log; simp [Log.ingest, ih]

/-! ## Stamping a trace -/

/-- The events `Trace.stamp.go` stamps after the stamp `last` keep the rule, and come after
`last`. -/
theorem stamp_go_strictlyIncreasing : ∀ (τ : Trace) (last : Option Int),
    (Trace.stamp.go last τ).StrictlyIncreasing ∧
      ∀ t, last = some t → ∀ q ∈ Trace.stamp.go last τ, t < q.ts
  | [], _ => ⟨List.Pairwise.nil, fun _ _ _ h => by cases h⟩
  | p :: τ, last => by
    obtain ⟨h₁, h₂⟩ := stamp_go_strictlyIncreasing τ (some (stampAfter last p.ts))
    simp only [Trace.stamp.go]
    refine ⟨List.Pairwise.cons (fun q hq => h₂ _ rfl q hq) h₁, ?_⟩
    intro t ht q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact lt_stampAfter ht p.ts
    · exact Int.lt_trans (lt_stampAfter ht p.ts) (h₂ _ rfl q hq)

/-- **Stamping makes the timestamps strictly increase.** -/
theorem stamp_strictlyIncreasing (σ : Trace) : σ.stamp.StrictlyIncreasing :=
  (stamp_go_strictlyIncreasing σ none).1

/-- **Readings that strictly increase are their own stamps.** -/
theorem stamp_of_strictlyIncreasing {σ : Trace} (h : σ.StrictlyIncreasing) : σ.stamp = σ := by
  suffices ∀ (τ : Trace) (last : Option Int), Trace.StrictlyIncreasing τ →
      (∀ t, last = some t → ∀ q ∈ τ, t < q.ts) → Trace.stamp.go last τ = τ by
    exact this σ none h (by simp)
  intro τ
  induction τ with
  | nil => intro _ _ _; rfl
  | cons p τ ih =>
    intro last hτ hlast
    have hτ' : Trace.StrictlyIncreasing τ := List.Pairwise.of_cons hτ
    have hp : ∀ q ∈ τ, p.ts < q.ts := fun q hq => List.rel_of_pairwise_cons hτ hq
    have hs : stampAfter last p.ts = p.ts :=
      stampAfter_of_lt fun t ht => hlast t ht p (List.mem_cons_self ..)
    simp only [Trace.stamp.go, hs]
    rw [ih (some p.ts) hτ' (by simpa using hp)]

theorem stamp_go_events : ∀ (τ : Trace) (last : Option Int),
    (Trace.stamp.go last τ).map (·.event) = τ.map (·.event)
  | [], _ => rfl
  | p :: τ, last => by
    simp only [Trace.stamp.go, List.map_cons, stamp_go_events τ]

/-- Stamping keeps the events, in order. -/
theorem stamp_events (σ : Trace) : σ.stamp.map (·.event) = σ.map (·.event) :=
  stamp_go_events σ none

theorem stamp_length (σ : Trace) : σ.stamp.length = σ.length := by
  have := congrArg List.length (stamp_events σ)
  simpa using this

theorem stamp_go_ge : ∀ (τ : Trace) (last : Option Int),
    List.Forall₂ (fun p q => q.event = p.event ∧ p.ts ≤ q.ts) τ (Trace.stamp.go last τ)
  | [], _ => .nil
  | p :: τ, last => by
    simp only [Trace.stamp.go]
    exact .cons ⟨rfl, stampAfter_ge last p.ts⟩ (stamp_go_ge τ _)

/-- **No event is stamped before its reading.** Each stamped event is the event at the same
position, with a timestamp at least its reading. -/
theorem stamp_ge (σ : Trace) :
    List.Forall₂ (fun p q => q.event = p.event ∧ p.ts ≤ q.ts) σ σ.stamp :=
  stamp_go_ge σ none

/-! ## Ingesting a trace's events -/

theorem lastTs?_events (τ : Trace) : Log.lastTs? (τ.map Entry.event) = τ.getLast?.map (·.ts) := by
  simp [Log.lastTs?, Log.trace_events]

/-- From a log `L`, ingesting the arrivals of `σ` appends its conforming events, stamped after
`L`'s last event. -/
theorem ingest_events_go (σ : Trace) : ∀ (L : Log),
    (Log.ingest reading ι P ω L σ.arrivals).1 =
      L ++ (Trace.stamp.go L.lastTs? (Trace.conforming P σ)).map Entry.event := by
  induction σ with
  | nil => intro L; simp [Log.ingest, Trace.arrivals, Trace.conforming, Trace.stamp.go]
  | cons p σ ih =>
    intro L
    have harr : Trace.arrivals (p :: σ) = Arrival.event p.event p.ts :: Trace.arrivals σ := rfl
    rw [harr]
    simp only [Log.ingest]
    by_cases hc : p.event.Conforms P.actionSchema P.schema
    · have hcons : Trace.conforming P (p :: σ) = p :: Trace.conforming P σ := by
        simp [Trace.conforming, hc]
      rw [hcons, submit_accepted (nonconformance?_event_eq_none.mpr hc)]
      have hentry : Arrival.entry L.lastTs? (.event p.event p.ts) =
          .event ⟨stampAfter L.lastTs? p.ts, p.event⟩ := rfl
      rw [hentry, ih, Log.lastTs?_append_event]
      simp [Trace.stamp.go]
    · have hcons : Trace.conforming P (p :: σ) = Trace.conforming P σ := by
        simp [Trace.conforming, hc]
      rw [hcons, submit_nonconforming L hc, ih]

/-- **Ingestion stamps the conforming events.** Ingesting a trace's events in order, each with
its timestamp as its clock reading, from an empty log, builds the log of its conforming events,
stamped. -/
theorem ingest_events (σ : Trace) :
    (Log.ingest reading ι P ω [] σ.arrivals).1 = (Trace.conforming P σ).stamp.map Entry.event := by
  rw [ingest_events_go]
  rfl

/-- **Ingestion of a recorded trace.** Ingesting the events of a trace recorded in seconds, each
with its recorded time in ticks of the policy set's rate as its clock reading, builds the log of
its conforming events at that rate, stamped. -/
theorem ingest_readings (σ : Trace) :
    (Log.ingest reading ι P ω [] (σ.readings P.tickRate)).1 =
      (Trace.conforming P (σ.scale P.tickRate.perSecond)).stamp.map Entry.event :=
  ingest_events _

/-- **Ingestion of a trace of conforming events whose timestamps strictly increase is replay.**
Ingesting its events in order, each with its timestamp as its clock reading, from an empty log,
stamps every event with its own timestamp and accepts it, as timepoint `n` of the log, with
`PolicySet.authorize`'s outcome at timepoint `n`. -/
theorem ingest_of_strictlyIncreasing (σ : Trace) (h : σ.StrictlyIncreasing)
    (hc : ∀ p ∈ σ, p.event.Conforms P.actionSchema P.schema) :
    Log.ingest reading ι P ω [] σ.arrivals =
      (σ.map Entry.event,
        (List.range σ.length).map fun n => .accepted n (P.authorize ι ω σ n)) := by
  suffices ∀ (τ : Trace) (ρ : Trace), Trace.StrictlyIncreasing (τ ++ ρ) →
      (∀ p ∈ ρ, p.event.Conforms P.actionSchema P.schema) →
      Log.ingest reading ι P ω (τ.map Entry.event) ρ.arrivals =
        ((τ ++ ρ).map Entry.event,
          (List.range' τ.length ρ.length).map fun n => .accepted n (P.authorize ι ω (τ ++ ρ) n)) by
    have := this [] σ (by simpa using h) hc
    simpa [List.range_eq_range'] using this
  intro τ ρ
  induction ρ generalizing τ with
  | nil => intro _ _; simp [Log.ingest, Trace.arrivals]
  | cons p ρ ih =>
    intro hτρ hcρ
    have hlt : ∀ q ∈ τ, q.ts < p.ts := by
      intro q hq
      have := List.pairwise_append.mp hτρ
      exact this.2.2 q hq p (List.mem_cons_self ..)
    have hr : (Arrival.event p.event p.ts).nonconformance? P = none :=
      nonconformance?_event_eq_none.mpr (hcρ p (List.mem_cons_self ..))
    -- The reading is after the last stamp, so it is the stamp.
    have hstamp : Arrival.entry (Log.lastTs? (τ.map Entry.event)) (.event p.event p.ts) =
        .event p := by
      show Entry.event ⟨stampAfter _ p.ts, p.event⟩ = .event p
      rw [stampAfter_of_lt]
      intro t ht
      rw [lastTs?_events] at ht
      cases hl : τ.getLast? with
      | none => rw [hl] at ht; cases ht
      | some q =>
        rw [hl] at ht
        simp only [Option.map_some, Option.some.injEq] at ht
        rw [← ht]
        exact hlt q (List.mem_of_getLast? hl)
    have harr : Trace.arrivals (p :: ρ) = Arrival.event p.event p.ts :: Trace.arrivals ρ := rfl
    rw [harr]
    simp only [Log.ingest]
    rw [submit_accepted hr, hstamp]
    have happ : τ.map Entry.event ++ [Entry.event p] = (τ ++ [p]).map Entry.event := by simp
    have hih := ih (τ ++ [p]) (by simpa using hτρ) (fun q hq => hcρ q (List.mem_cons_of_mem _ hq))
    simp only [happ, hih, List.length_map, List.length_append, List.length_singleton,
      List.append_assoc, List.singleton_append]
    refine Prod.ext rfl ?_
    simp only [List.length_cons, List.range'_succ, List.map_cons, List.cons.injEq]
    refine ⟨?_, trivial⟩
    rw [decide_events]
    have := authorize_append (ι := ι) (P := P) (ω := ω) (σ := τ ++ [p]) (n := τ.length) ρ (by simp)
    simp only [List.append_assoc, List.singleton_append] at this
    rw [this]

end Dogwood.Thm
