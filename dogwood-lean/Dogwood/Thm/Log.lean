import Dogwood.Spec.Log
import Dogwood.Thm.Decision
import Dogwood.Thm.Horizon

/-!
# Properties of decisions over a log

* `decide_events`: the log of an authorizer that only ingests events decides as
  `PolicySet.authorize` does over the trace of those events, under either reading.
* `decide_append`: **past-only decisions over a log.** Entries appended later never change the
  outcome of an earlier entry, deployments included.
* `decide_retrospective`: under the retrospective reading, an event is decided by
  `PolicySet.authorize`, over the whole trace, with the rules in force before it.
* `startOf_kept`, `startOf_new`: a rule that keeps its monitor instance keeps its start; a rule
  with a new instance starts at the next event.
* `leafHoldsFrom_iff_drop`: under the prospective reading, a leaf of a rule whose instance started
  at timepoint `s` holds as it would for an authorizer that had seen only the events from `s` on.
  This is the reading of an implementation that installs a rule with an empty monitor.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-! ## The trace and the state of a log -/

theorem Log.trace_append (a b : Log) : Log.trace (a ++ b) = a.trace ++ b.trace :=
  List.filterMap_append

theorem Log.trace_events (σ : Trace) : Log.trace (σ.map Entry.event) = σ := by
  simp [Log.trace, List.filterMap_map, Function.comp_def, Entry.event?]

theorem Log.foldl_events (log : Log) (st : Log.State) :
    (log.foldl Log.State.step st).events = st.events + log.trace.length := by
  induction log generalizing st with
  | nil => simp [Log.trace]
  | cons x log ih =>
    rw [List.foldl_cons, ih]
    cases x <;> (simp [Log.State.step, Log.trace, Entry.event?, List.filterMap_cons]; try omega)

/-- The state after a prefix counts the events of the prefix. -/
theorem Log.state_events (P : PolicySet) (log : Log) :
    (Log.state P log).events = log.trace.length := by
  simp [Log.state, Log.foldl_events, Log.State.initial]

/-- A log of events alone leaves the initial rules in force. -/
theorem Log.foldl_events_rules (σ : Trace) (st : Log.State) :
    ((σ.map Entry.event).foldl Log.State.step st).rules = st.rules := by
  induction σ generalizing st with
  | nil => rfl
  | cons p σ ih => simp only [List.map_cons, List.foldl_cons]; rw [ih]; rfl

/-- The event at log position `i` is timepoint `(state of the first i entries).events` of the
trace. -/
theorem Log.trace_getElem?_state {P : PolicySet} {log : Log} {i : Nat} {p : TimePoint}
    (h : log[i]? = some (.event p)) :
    log.trace[(Log.state P (log.take i)).events]? = some p := by
  have hi : i < log.length := by
    rcases Nat.lt_or_ge i log.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at h; cases h
  rw [Log.state_events]
  have hdrop : log.drop i = .event p :: log.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi]
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at h
    rw [h]
  have htr : log.trace = Log.trace (log.take i) ++ p :: Log.trace (log.drop (i + 1)) := by
    have := Log.trace_append (log.take i) (log.drop i)
    rw [List.take_append_drop, hdrop] at this
    rw [this]
    simp [Log.trace, Entry.event?]
  rw [htr, List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem Log.state_lt_length {P : PolicySet} {log : Log} {i : Nat} {p : TimePoint}
    (h : log[i]? = some (.event p)) : (Log.state P (log.take i)).events < log.trace.length := by
  have := Log.trace_getElem?_state (P := P) h
  rcases Nat.lt_or_ge (Log.state P (log.take i)).events log.trace.length with hl | hl
  · exact hl
  · rw [List.getElem?_eq_none hl] at this; cases this

/-! ## Monitor instances -/

/-- A rule whose monitor instance was in force keeps the instance's start. -/
theorem startOf_kept {st : Log.State} {r : DeployedRule} {r' : DeployedRule} {s : Nat}
    (h : st.rules.find? (·.1.monitor == r.monitor) = some (r', s)) : st.startOf r = s := by
  simp [Log.State.startOf, h]

/-- A rule whose monitor instance was not in force starts at the next event. -/
theorem startOf_new {st : Log.State} {r : DeployedRule}
    (h : ∀ x ∈ st.rules, x.1.monitor ≠ r.monitor) : st.startOf r = st.events := by
  have : st.rules.find? (·.1.monitor == r.monitor) = none := by
    rw [List.find?_eq_none]
    intro x hx
    simpa using h x hx
  simp [Log.State.startOf, this]

/-! ## Decisions over a log -/

section

variable {reading : UpdateReading} {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers}

/-- **A log of events alone decides as `authorize` does.** -/
theorem decide_events (σ : Trace) (n : Nat) :
    Log.decide reading ι P ω (σ.map Entry.event) n = P.authorize ι ω σ n := by
  unfold Log.decide
  rcases Nat.lt_or_ge n σ.length with hn | hn
  · rw [List.getElem?_map, List.getElem?_eq_getElem hn, Option.map_some]
    simp only
    rw [Log.trace_events, ← List.map_take]
    have hst : Log.state P ((σ.take n).map Entry.event) =
        ⟨n, (Log.State.initial P).rules⟩ := by
      have hev := Log.state_events P ((σ.take n).map Entry.event)
      rw [Log.trace_events, List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] at hev
      have hr := Log.foldl_events_rules (σ.take n) (Log.State.initial P)
      cases hs : Log.state P ((σ.take n).map Entry.event) with
      | mk events rules =>
        rw [hs] at hev
        unfold Log.state at hs
        rw [hs] at hr
        simp only at hev hr
        rw [hev, hr]
    rw [hst]
    have hrules :
        ((Log.State.initial P).rules.map fun r => (r.1.policy, reading.observesFrom r.2)) =
        P.policies.map fun q => (q, 0) := by
      have hz : (P.policies.zipIdx.map fun x => (x.1, (0 : Nat))) =
          P.policies.map fun q => (q, 0) := by
        conv => rhs; rw [← List.zipIdx_map_fst 0 P.policies]
        rw [List.map_map]
        rfl
      cases reading <;>
        simp [Log.State.initial, UpdateReading.observesFrom, List.map_map, Function.comp_def, hz]
    simp only
    rw [hrules, ← authorize_eq_authorizeDeployed]
  · rw [List.getElem?_eq_none (by simpa using hn)]
    simp [PolicySet.authorize, PolicySet.decideWith, List.getElem?_eq_none hn]

/-- **Past-only decisions over a log.** -/
theorem decide_append (log more : Log) {i : Nat} (hi : i < log.length) :
    Log.decide reading ι P ω (log ++ more) i = Log.decide reading ι P ω log i := by
  unfold Log.decide
  rw [List.getElem?_append_left hi, List.take_append_of_le_length (Nat.le_of_lt hi)]
  cases h : log[i]? with
  | none => rfl
  | some x =>
    cases x with
    | deploy _ => rfl
    | event p =>
      simp only
      rw [Log.trace_append]
      exact authorizeDeployed_append _ _ (Log.state_lt_length h)

/-- Under the retrospective reading, an event is decided by `authorize`, over the whole trace,
with the rules in force before it. -/
theorem decide_retrospective {log : Log} {i : Nat} {p : TimePoint}
    (h : log[i]? = some (.event p)) :
    Log.decide .retrospective ι P ω log i =
      ({ P with policies := (Log.state P (log.take i)).rules.map (·.1.policy) } :
        PolicySet).authorize
        ι ω log.trace (Log.state P (log.take i)).events := by
  unfold Log.decide
  rw [h]
  simp only [UpdateReading.observesFrom]
  rw [authorize_eq_authorizeDeployed]
  simp only [List.map_map, Function.comp_def]
  rfl

end

/-! ## The prospective reading is a fresh monitor -/

/-- **A rule that observes from `s` is a rule installed at `s`.** For a leaf, holding
at timepoint `n ≥ s` while observing the trace from `s` on is holding at timepoint `n − s` of the
trace's suffix from `s`: the trace an authorizer started at the rule's deployment would have
seen. -/
theorem leafHoldsFrom_iff_drop {ι : ImplChoices} {P : PolicySet} {σ : Trace} {s n : Nat}
    {φ : Formula} (hs : s ≤ n) (hn : n < σ.length) :
    P.LeafHoldsFrom ι σ s n φ ↔ P.LeafHolds ι (σ.drop s) (n - s) φ := by
  have hget : (σ.drop s)[n - s]? = σ[n]? := by
    rw [List.getElem?_drop, Nat.add_sub_cancel' hs]
  unfold PolicySet.LeafHoldsFrom PolicySet.LeafHolds
  rw [hget]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  have hsub := subsequence_drop σ s (P.schema.Visible σ p.event)
  have h1 := sat_subseq_noTp (ι := ι) (rate := P.tickRate) (e := p.event) hsub (φ.injectPins P.schema)
    Valuation.noTp_empty (n - s) (by simp; omega)
  rw [Nat.add_sub_cancel' hs] at h1
  have h2 : Sat ι P.tickRate σ p.event (fun k => s ≤ k ∧ P.schema.Visible σ p.event k) Valuation.empty n
      (φ.injectPins P.schema) ↔
      Sat ι P.tickRate σ p.event (fun K => P.schema.Visible σ p.event K ∧ s ≤ K ∧ K < σ.length)
        Valuation.empty n (φ.injectPins P.schema) :=
    sat_congr _ _ n fun k hk => ⟨rfl, ⟨fun h => ⟨h.2, h.1, by omega⟩, fun h => ⟨h.2.1, h.1⟩⟩⟩
  have h3 : Sat ι P.tickRate (σ.drop s) p.event (P.schema.Visible (σ.drop s) p.event) Valuation.empty (n - s)
      (φ.injectPins P.schema) ↔
      Sat ι P.tickRate (σ.drop s) p.event (fun i => P.schema.Visible σ p.event (s + i)) Valuation.empty
        (n - s) (φ.injectPins P.schema) :=
    sat_congr _ _ _ fun k _ => ⟨rfl, by simp only [EventSchema.Visible, List.getElem?_drop]⟩
  rw [h2, h3, h1]

end Dogwood.Thm
