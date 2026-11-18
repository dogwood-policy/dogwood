import Dogwood.Spec.Log

/-!
# Ingestion: stamping and conformance

An authorizer assigns the timestamp of every event it accepts. A submission carries no
timestamp. It carries the event, and arrives with a **clock reading** (`Arrival.event`): the
authorizer's clock when the event arrived, in ticks of its rate (`PolicySet.tickRate`). When a
recorded trace is replayed, the reading is the recorded time in ticks: `s × rate.perSecond` for a
time of `s` seconds (`Trace.readings`). The crate's reference interpreter does not stamp: it keeps
the caller's timestamps (`Dogwood.Spec.Event`).

The authorizer **stamps** the event with its reading, or with one tick after the last event's
stamp when the reading is not later (`stampAfter`): `max(reading, last + 1)`. So the stamps of a
log strictly increase by construction (`Dogwood.Thm.ingest_strictlyIncreasing`), and an
authorizer never rejects an event for its time. On readings that already strictly increase,
every event is stamped with its reading (`Dogwood.Thm.stamp_of_strictlyIncreasing`).

Under partitioned evaluation (`Dogwood.Spec.Partitioned`), an implementation keeps one log per
partition key, and stamps each log on its own: `last` is the stamp of the last event of the event's
own partition. The single log's stamps and the per-partition stamps agree when the readings strictly
increase across all partitions (`Dogwood.Thm.stamp_partitionLog_of_strictlyIncreasing`).

`Log.submit` is the ingestion step, and `Log.ingest` ingests a sequence of arrivals in order.
`Trace.stamp` computes the trace that ingestion builds from a sequence of events with their
readings, when every event conforms.

## Readings far from the last stamp

A reading at or behind the last stamp, from a burst of events within one tick or a clock that
stepped back, gets one tick more than the last stamp. A reading far ahead of the last stamp is the
stamp; the stamps then run ahead of the clock, and each later reading behind them gets one tick
more than the last, until the clock catches up. The specification bounds neither. An
implementation may bound the second, refusing a submission when its last stamp is too far ahead of
its clock, and refuse one when the stamps reach `i64::MAX`. The event-log contract admits both
refusals as `Rejection.unavailable` (`Dogwood.Spec.Contract`).

A submitter cannot choose an event's timestamp: the reading is the authorizer's own. If the
timestamp came from the submission, and one not after the last were rejected, a submitter could
push the clock forward with an event stamped far in the future, so that every later event, a
revocation included, would be rejected as stale. Stamping closes that attack.

## Nonconforming events

An authorizer rejects an event that does not conform to the event schema
(`Rejection.nonconforming`, `Event.Conforms`): an event of no declared signature, an event whose
logged record is not an instance of its signature, or one whose logged caller or symmetrically
pinned field contradicts its own request (`Arrival.nonconformance?`). This is the only reason an
authorizer rejects an event for what it carries. The event-log contract adds one for the event id
a submission carries with it: a submission that reuses the event id of an accepted event, and is
not a retry of it, is rejected as a duplicate (`Rejection.duplicate`, `Dogwood.Spec.Contract`).

`Log.submit` ingests a new submission. A retry of an accepted submission, recognized by its event
id, is not ingested again: the contract answers it at the accepted submission's position
(`Dogwood.Spec.Run.Meets`).

The check is made at ingestion, not at the decisions that read the event, because a logged event
is history for every later decision:

* checking it at each decision would fail closed every later decision that can see it, a denial
  of service any submitter could cause, or ignore it, which fails open: a `forbid`'s evidence would
  be dropped because it was logged badly;
* a rejection is reported to the submitter (`Reply.rejected`), never silent, so the submitter can
  correct the event and submit it again. A rejection is not a decision: in particular it is not a
  `Deny`;
* every log that ingestion builds holds only conforming events
  (`Dogwood.Thm.conforming_ingest`), which is the hypothesis the soundness theorem needs of a
  trace (`Dogwood.Thm.soundness`).

A decision still checks its own event (`FailClosed.nonconformingEvent`), and the request and
entity data that only a decision reads, because `authorize` is also used over traces that
ingestion did not build, such as an engine's replay. A deployment is never rejected. The
crate's `Authorizer::update_policies` can refuse one (an engine without live update, or changed
partition keys), and then leaves the rules in force unchanged.
-/

namespace Dogwood.Spec

/-- Why a submission was rejected. -/
inductive Rejection where
  /-- The event does not conform to the event schema (`Event.Conforms`). -/
  | nonconforming
  /-- The implementation could not place the submission in its log: a serialization conflict
  between its instances, a store it could not write, a connection it lost, a clock it does not
  trust, or a timestamp space it has exhausted. The
  submitter may submit the entry again, as a new submission. -/
  | unavailable
  /-- The submission has the retry key of an accepted submission, its event id among them, but
  is not a retry of it: its content differs, or it comes after the retry window
  (`Dogwood.Spec.Submission.RetryOf`). -/
  | duplicate
deriving Repr, DecidableEq

/-- What the submitter of a log entry is told. -/
inductive Reply where
  /-- The entry was accepted at position `pos` of the log, with the outcome of
  ingesting it there. -/
  | accepted (pos : Nat) (outcome : Outcome)
  /-- The entry was rejected, and did not enter the log. -/
  | rejected (reason : Rejection)

/-- An entry as it arrives at an authorizer, before it is stamped. -/
inductive Arrival where
  /-- An event, with the authorizer's clock reading when it arrived, in ticks. The submitter
  supplies the event, never its timestamp. -/
  | event (e : Event) (clock : Int)
  /-- A deployment: from this entry on, exactly the rules `rules` are in force. -/
  | deploy (rules : List DeployedRule)

/-- The log's events keep the language's timestamp rule: their timestamps
strictly increase. Stamping makes every log that ingestion builds keep it
(`Dogwood.Thm.ingest_strictlyIncreasing`). -/
def Log.WellFormed (log : Log) : Prop := log.trace.StrictlyIncreasing

/-- Every event of the log conforms to the event schema of `P`. -/
def Log.Conforming (P : PolicySet) (log : Log) : Prop :=
  ∀ p ∈ log.trace, p.event.Conforms P.actionSchema P.schema

/-- The timestamp of the last event of the log, if it has an event. -/
def Log.lastTs? (log : Log) : Option Int := log.trace.getLast?.map (·.ts)

/-! ## Stamping -/

/-- **The stamp** of an event whose clock reading is `clock`, after the stamp `last` of the last
accepted event, if there is one: the reading, or one tick after `last` when the reading is not
after it. -/
def stampAfter : Option Int → Int → Int
  | none, clock => clock
  | some last, clock => max clock (last + 1)

/-- The log entry an arrival becomes as the next entry of a log whose last stamp is `last`: its
event, stamped after `last`, or its deployment. -/
def Arrival.entry (last : Option Int) : Arrival → Entry
  | .event e clock => .event ⟨stampAfter last clock, e⟩
  | .deploy rs => .deploy rs

/-- The log entry `y` is the arrival stamped after the last stamp `last`: the arrival's event,
stamped at or after its clock reading and after `last`, or the arrival's deployment. Ingestion's
entry `Arrival.entry last x` is the one with the least stamp (`Dogwood.Thm.stamps_entry`,
`Dogwood.Thm.stampAfter_le_of_stamps`). The event-log contract asks this of an implementation's
log (`Run.Meets.stamped`), which lets an implementation stamp later than ingestion does: one
that stamps its deployments from the same sequence as its events stamps an event after a
deployment one tick after the deployment's stamp. -/
def Arrival.Stamps (last : Option Int) : Arrival → Entry → Prop
  | .event e clock, .event p => p.event = e ∧ clock ≤ p.ts ∧ ∀ t, last = some t → t < p.ts
  | .deploy rs, .deploy rs' => rs' = rs
  | _, _ => False

/-- Why an authorizer built with `P` rejects an arrival for what it carries: an event that does
not conform to the event schema. A deployment is never rejected. -/
def Arrival.nonconformance? (P : PolicySet) : Arrival → Option Rejection
  | .event e _ => if e.Conforms P.actionSchema P.schema then none else some .nonconforming
  | .deploy _ => none

/-! ## Ingestion -/

/-- Submitting the arrival `x` to an authorizer built with `P` whose log is `log`: the log
afterwards, and the reply to the submitter. An accepted arrival is stamped after the log's last
event, appended, and decided at its position. -/
noncomputable def Log.submit (reading : UpdateReading) (ι : Temporal.ImplChoices)
    (P : PolicySet) (ω : Provider.Providers) (log : Log) (x : Arrival) : Log × Reply :=
  match x.nonconformance? P with
  | some r => (log, .rejected r)
  | none =>
    let y := x.entry log.lastTs?
    (log ++ [y], .accepted log.length (Log.decide reading ι P ω (log ++ [y]) log.length))

/-- Submitting the arrivals `xs` in order, from the log `log`: the log afterwards, and the reply to
each submission, in order. -/
noncomputable def Log.ingest (reading : UpdateReading) (ι : Temporal.ImplChoices)
    (P : PolicySet) (ω : Provider.Providers) : Log → List Arrival → Log × List Reply
  | log, [] => (log, [])
  | log, x :: xs =>
    let s := Log.submit reading ι P ω log x
    let t := Log.ingest reading ι P ω s.1 xs
    (t.1, s.2 :: t.2)

/-- The arrivals of a trace's events, in order, each with its timestamp as its clock reading. -/
def Trace.arrivals (σ : Trace) : List Arrival := σ.map fun p => .event p.event p.ts

/-- The arrivals of a recorded trace whose times are in seconds, at the rate `rate`: each event,
with its recorded time in ticks as its clock reading. -/
def Trace.readings (rate : TickRate) (σ : Trace) : List Arrival := (σ.scale rate.perSecond).arrivals

/-- The trace an authorizer builds when the events of `σ` arrive in order, each with its timestamp
as its clock reading, at an empty log, and none is rejected: each event stamped after the one
before it (`Dogwood.Thm.ingest_events`). On a trace whose timestamps strictly increase, the stamps
are the timestamps (`Dogwood.Thm.stamp_of_strictlyIncreasing`). Executable. -/
def Trace.stamp (σ : Trace) : Trace := go none σ
where
  /-- The stamped events of `σ`, after accepted events whose last stamp is `last`. -/
  go : Option Int → Trace → Trace
    | _, [] => []
    | last, p :: σ => ⟨stampAfter last p.ts, p.event⟩ :: go (some (stampAfter last p.ts)) σ

/-- The events of `σ` that conform to the event schema of `P`. -/
def Trace.conforming (P : PolicySet) (σ : Trace) : Trace :=
  σ.filter fun p => decide (p.event.Conforms P.actionSchema P.schema)

end Dogwood.Spec
