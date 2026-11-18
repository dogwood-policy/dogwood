import Dogwood.Spec.Decision

/-!
# Policy updates: decisions over a log of events and deployments

An authorizer's rules can change while events flow: an operator installs,
replaces, or removes rules through a control plane. The specification states
such changes in the semantics. An authorizer's history is a **log**: its
entries are the accepted events and the control-plane changes, in one order
(`Entry`). A control-plane change, a **deployment**, names exactly the rules in
force from that entry on (`Entry.deploy`). The events of the log, in order, are
its trace (`Log.trace`); a deployment takes no timepoint. An authorizer built
with a policy set `P` starts with the rules of `P` in force.

## Monitor instances

A rule observes the trace through its **monitor instance**: the state an
implementation keeps for the rule's temporal leaves. A deployment names the
instance of each rule it puts in force (`DeployedRule.monitor`). A rule whose
instance was in force just before the deployment keeps that instance, and with
it the timepoint its instance started at. Any other rule gets a new instance,
which starts at the deployment: at the timepoint of the next event. The
timepoint an instance started at is its rule's *start* (`Log.State.startOf`).

An instance belongs to one rule. When a rule changes, the deployment must give
it a new instance, so that the changed rule does not read state kept for the old
one. `Log.InstancesStable` states the requirement: across the log, every rule in
force under one instance is the same rule. An implementation that keeps a leaf's
state under an id that survives a change of its rule breaks it: the changed rule
reads the old rule's state. A rule whose instance leaves the set and returns later
starts afresh at its return, even under the same instance: state kept for an
instance while it was not in force is never read.

## What a rule deployed while events flow sees

An implementation gives one of two readings (`UpdateReading`):

* **retrospective**: a rule observes the whole trace, including the events
  accepted before its deployment. The crate's reference interpreter gives this
  reading: `Authorizer::update_policies` keeps the history, and its built-in
  temporal engine evaluates every leaf of the new set over the whole of it.
  Under this reading, instances do not matter.
* **prospective**: a rule observes only the events from its start on, as an
  implementation does that starts an empty monitor for a rule at its
  installation and keeps the monitors of the rules a change leaves alone.

Under the prospective reading, timepoint indices remain global: a `tp`
variable binds the index of the timepoint in the whole trace. An implementation
may number the timepoints of a new rule's monitor from its installation instead.
The two numberings agree for every leaf, because a condition observes a
timepoint's index only through equality
(`Dogwood.Thm.leafHoldsFrom_iff_drop`).
-/

namespace Dogwood.Spec

/-- A rule as a deployment puts it in force: the rule, and the identity of the
monitor instance that keeps the state of its temporal leaves. -/
structure DeployedRule where
  monitor : Nat
  policy : Policy
deriving Inhabited

/-- One entry of an authorizer's log. -/
inductive Entry where
  /-- An accepted event. -/
  | event (p : TimePoint)
  /-- A deployment: from this entry on, exactly the rules `rules` are in
  force. -/
  | deploy (rules : List DeployedRule)

/-- An authorizer's log: its accepted events and its deployments, in the one
order of the log. -/
abbrev Log := List Entry

/-- The event of an entry, if it is an event. -/
def Entry.event? : Entry → Option TimePoint
  | .event p => some p
  | .deploy _ => none

/-- The events of the log, in order: the trace that decisions are made over. -/
def Log.trace (log : Log) : Trace := log.filterMap Entry.event?

/-- What a prefix of the log determines: how many events it holds, and the
rules in force after it, each with the timepoint its monitor instance started
at. -/
structure Log.State where
  events : Nat
  rules : List (DeployedRule × Nat)

/-- The start of a rule that a deployment puts in force: the start of its
instance, if that instance is in force before the deployment; otherwise the
timepoint of the next event. -/
def Log.State.startOf (st : Log.State) (r : DeployedRule) : Nat :=
  match st.rules.find? (·.1.monitor == r.monitor) with
  | some (_, s) => s
  | none => st.events

/-- The state after one more entry. -/
def Log.State.step (st : Log.State) : Entry → Log.State
  | .event _ => { st with events := st.events + 1 }
  | .deploy rs => { st with rules := rs.map fun r => (r, st.startOf r) }

/-- The state an authorizer built with the policy set `P` starts from: no
events, and the rules of `P` in force from the first timepoint on, as the
instances `0, 1, …` in the order of `P.policies`. -/
def Log.State.initial (P : PolicySet) : Log.State :=
  ⟨0, P.policies.zipIdx.map fun pk => (⟨pk.2, pk.1⟩, 0)⟩

/-- The state after the entries of `log`, for an authorizer built with `P`. -/
def Log.state (P : PolicySet) (log : Log) : Log.State :=
  log.foldl Log.State.step (Log.State.initial P)

/-- How a rule deployed while events flow reads the history from before its
deployment. -/
inductive UpdateReading where
  /-- A rule observes the whole trace. -/
  | retrospective
  /-- A rule observes only the events from the start of its monitor instance
  on. -/
  | prospective
deriving Repr, DecidableEq

/-- The timepoint from which a rule whose instance started at `start`
observes the trace. -/
def UpdateReading.observesFrom : UpdateReading → Nat → Nat
  | .retrospective, _ => 0
  | .prospective, start => start

/-- The outcome of the entry at position `i` of the log of an authorizer built
with `P`. An event is decided against the rules in force before it, each
observing the trace from the timepoint the reading gives it; a deployment
decides nothing. Besides its initial rules, `P` supplies the schema, the action
entities, and entity conformance, which a deployment does not change. For a log
of events alone, the outcome is `PolicySet.authorize`'s
(`Dogwood.Thm.decide_events`). The answer to a retry of the event at position
`i` is this outcome too (`Dogwood.Spec.Run.Meets.retried`): it depends only on
the log up to `i` (`Dogwood.Thm.decide_append`), so a later entry, a deployment
included, does not change it. -/
noncomputable def Log.decide (reading : UpdateReading) (ι : Temporal.ImplChoices)
    (P : PolicySet) (ω : Provider.Providers) (log : Log) (i : Nat) : Outcome :=
  match log[i]? with
  | some (.event _) =>
    let st := Log.state P (log.take i)
    P.authorizeDeployed ι ω log.trace st.events
      (st.rules.map fun r => (r.1.policy, reading.observesFrom r.2))
  | _ => .noDecision

/-- An instance names one rule: whenever a rule of some instance is in force,
at any point of the log, it is the same rule. -/
def Log.InstancesStable (P : PolicySet) (log : Log) : Prop :=
  ∀ i j, i ≤ log.length → j ≤ log.length →
    ∀ r ∈ (Log.state P (log.take i)).rules, ∀ r' ∈ (Log.state P (log.take j)).rules,
      r.1.monitor = r'.1.monitor → r.1.policy = r'.1.policy

end Dogwood.Spec
