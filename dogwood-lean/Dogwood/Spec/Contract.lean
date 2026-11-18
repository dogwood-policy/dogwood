import Dogwood.Spec.Ingest

/-!
# The event-log contract

The semantics decides over one totally ordered log of events and deployments
(`Dogwood.Spec.Log`). An implementation that runs several instances, on several
machines or as several processes over one database, or that retries a step
after a conflict, must still decide as if it had built one such log. This
module states the contract every run of an implementation must meet
(`Run.Meets`):

* every submission is either accepted exactly once, at one position of the one
  log, or answered as a retry of an accepted submission, or rejected, and its
  submitter is told which;
* no submission is lost silently, and none is accepted twice;
* every instance observes the same order: the entries an instance had observed
  when it decided an entry are a prefix of the log;
* an accepted event's outcome is the specification's decision at the event's
  position in the log, and so is the answer to a retry of it;
* each logged event is its submission's event, stamped at or after its clock
  reading and after the event before it (`Arrival.Stamps`), so the log keeps
  the timestamp rule (`Dogwood.Spec.Run.Meets.trace_strictlyIncreasing`).
  Ingestion stamps exactly `max(reading, last + 1)` (`Log.submit`); the
  contract also admits a later stamp, as an implementation assigns to an event
  after a deployment when its deployments take stamps from the same sequence;
* every event of the log conforms to the event schema (`Log.Conforming`), and a
  rejection for nonconformance is truthful.

A submission carries no timestamp, only the clock reading the implementation
took when it arrived (`Arrival.event`). The contract does not relate readings
to real time: nothing in it can, since a reading is what the implementation's
clock said.

The contract does not require an implementation to accept every submission it
could accept: it may reject one it cannot place (`Rejection.unavailable`), as
long as it says so. Refusing a submission whose clock reading is too far behind
the last stamp is such a rejection.

## Retries

A client that loses the reply to a submission submits the event again. So that
the event is not logged twice, and the client is told what it would have been
told the first time, a submission may carry an **event id** (`Submission.eventId`)
that its submitter chose. The contract is parameterized by a **retry window**
`W`, in ticks of the authorizer's clock; its default is five minutes
(`defaultRetryWindow`).

A submission is a **retry** of an accepted submission (`Submission.RetryOf`)
when all of these hold:

* it has the same **retry key** (`Submission.retryKey?`): it is on the same
  partition key, so in the same log of an implementation that keeps one log per
  partition key (`EventSchema.partitionKey`), and it has the same event id and
  the same action and kind;
* its content is identical: the same logged record, and the same request (its
  principal, resource, context, and entity data). With the action and kind,
  that makes it the same event. Values are compared as values, not as
  spellings (`Dogwood.Spec.Canonical`);
* its time is at most `W` after the accepted submission's stamp. Its time is
  the clock reading it arrived with (`Arrival.event`); where an implementation
  has no reading for a submission, it is the implementation's own clock when
  the submission arrived.

A retry is not ingested again: it is not in the log. It is answered at the
accepted submission's position, with the specification's decision there
(`Run.Meets.retried`). The decision at a position depends only on the log up to
it (`Dogwood.Thm.decide_append`), so the answer is the accepted submission's
own, even when a deployment came between the two
(`Dogwood.Spec.Run.Meets.retry_reply`).

A submission that has the retry key of an accepted submission but is not a
retry of it, because its content differs or it comes more than `W` after the
accepted submission's stamp, is **rejected** (`Rejection.duplicate`): it is not
ingested, and not decided. So no two entries of the log share a retry key
(`Run.Meets.keyed`). A submission without an event id, and a deployment, has no
retry key: it is never a retry, and never a duplicate. When no two submissions
share a retry key, the contract is the contract without retries, whatever the
window (`Dogwood.Spec.Run.meets_iff_withoutRetries`).

## Runs that break the contract

Two kinds of run break the contract. In one, a second instance reuses the
event ids the first instance assigned, so its event is taken for a replay of the
first instance's event: the submission is answered with another submission's
position, and is not in the log. The colliding id is the implementation's own,
not an event id the submitter gave, so the submission is not a retry of the
other one (`Submission.RetryOf`), and the answer breaks `Run.Meets.answered`,
which answers a submission at another's position only when it is a retry. In
the other, a step aborted by a conflict between instances loses a history-only
event, and the error is not reported: the submission is neither in the log nor
rejected.

`Dogwood.Spec.Run.Meets.outcome_eq` shows that an accepted outcome is the
decision over the whole log, not only over the prefix its instance observed,
and `Dogwood.Thm.sequential_meets` that a single instance ingesting the
submissions in arrival order (`Run.sequential`) meets the contract, for every
retry window.
-/

namespace Dogwood.Spec

open Cedar.Spec (EntityUID Value)

/-- An event id: the identity a submitter gives an event, so that it can submit the event again
after a lost reply and be answered as the first time. -/
abbrev EventId := String

/-- The default retry window of an authorizer whose clock runs at `rate`: five minutes, in its
ticks. -/
def defaultRetryWindow (rate : TickRate) : Nat := 300 * rate.perSecond

/-- A submission: an unstamped entry that a client hands to an implementation, with the clock
reading the implementation took when it arrived, and an identity that distinguishes it from every
other submission. Submitting the entry again, after a rejection or a lost reply, is a new
submission. It may carry the event id its submitter gave the event, by which a submission of an
event already accepted is recognized as a retry. -/
structure Submission where
  id : Nat
  arrival : Arrival
  /-- The event id its submitter gave the event, if any. -/
  eventId : Option EventId := none

/-- What a resubmission is recognized by: the partition key of the event, its event id, and its
action and kind. -/
structure RetryKey where
  partition : List (Option Value)
  eventId : EventId
  action : EntityUID
  kind : String
deriving DecidableEq

/-- The retry key of a submission under the event schema `S`: the partition key of its event
(`EventSchema.partitionKey`), its event id, and its event's action and kind. A deployment, and an
event submitted without an event id, has none. -/
def Submission.retryKey? (S : EventSchema) (s : Submission) : Option RetryKey :=
  match s.eventId, s.arrival with
  | some k, .event e _ => some ⟨S.partitionKey e, k, e.action, e.kind⟩
  | _, _ => none

/-- Two submissions have the same retry key. -/
def Submission.SameKey (S : EventSchema) (s s' : Submission) : Prop :=
  ∃ K, s.retryKey? S = some K ∧ s'.retryKey? S = some K

/-- An accepted submission, as the implementation logged it: the submission, and the log entry it
became, its event stamped. -/
structure Logged where
  submission : Submission
  entry : Entry

/-- **A retry.** The submission `s` is a retry of the accepted submission `x`, under the retry
window `W`: it has the retry key of `x`, it is the same event, and its clock reading is at most `W`
after the stamp `x` was logged with. -/
def Submission.RetryOf (S : EventSchema) (W : Nat) (s : Submission) (x : Logged) : Prop :=
  s.SameKey S x.submission ∧
    ∃ e clock clock₀ p, s.arrival = .event e clock ∧ x.submission.arrival = .event e clock₀ ∧
      x.entry = .event p ∧ clock ≤ p.ts + W

/-- What a run of an implementation did with the submissions it received. -/
structure Run where
  /-- The submissions the implementation received. -/
  submitted : List Submission
  /-- The accepted submissions, in the order of the one log, with their log entries. -/
  log : List Logged
  /-- The reply each submission's submitter got, by submission identity. -/
  reply : Nat → Option Reply
  /-- For each accepted submission, and each retry, the log the instance that answered it had
  observed when it decided it. -/
  observed : Nat → List Logged

/-- The run's log, as log entries. -/
def Run.entries (r : Run) : Log := r.log.map (·.entry)

/-- The accepted submissions, in the order of the log. -/
def Run.submissions (r : Run) : List Submission := r.log.map (·.submission)

/-- **The event-log contract**, for an implementation of the reading `reading`
with the implementation choices `ι`, built with the policy set `P`, whose
information providers mean `ω`, with the retry window `W`. -/
structure Run.Meets (reading : UpdateReading) (ι : Temporal.ImplChoices) (P : PolicySet)
    (ω : Provider.Providers) (W : Nat) (r : Run) : Prop where
  /-- Submissions are told apart by their identities. -/
  distinct : (r.submitted.map (·.id)).Nodup
  /-- The log holds only submitted entries. -/
  submitted : ∀ s ∈ r.submissions, s ∈ r.submitted
  /-- No submission is accepted twice. -/
  once : (r.submissions.map (·.id)).Nodup
  /-- Every submission is accepted, and its submitter is told its position in the log; or it is
  absent from the log, and either it is a retry of an accepted submission and its submitter is
  told that submission's position, or it is rejected and its submitter is told why. -/
  answered : ∀ s ∈ r.submitted,
    (∃ i, r.submissions[i]? = some s ∧ ∃ o, r.reply s.id = some (.accepted i o)) ∨
    ((∀ s' ∈ r.submissions, s'.id ≠ s.id) ∧
      ((∃ i x, r.log[i]? = some x ∧ s.RetryOf P.schema W x ∧
          ∃ o, r.reply s.id = some (.accepted i o)) ∨
        ∃ why, r.reply s.id = some (.rejected why)))
  /-- Every instance observes the one order: what the instance that ingested an
  entry had observed is a prefix of the log, and contains the entry. -/
  observedPrefix : ∀ (i : Nat) (x : Logged), r.log[i]? = some x →
    r.observed x.submission.id <+: r.log ∧ i < (r.observed x.submission.id).length
  /-- An accepted submission's outcome is the specification's, at its position,
  over the entries its instance had observed. -/
  decided : ∀ (i : Nat) (x : Logged) o, r.log[i]? = some x →
    r.reply x.submission.id = some (.accepted i o) →
    o = Log.decide reading ι P ω ((r.observed x.submission.id).map (·.entry)) i
  /-- **Retries.** A submission absent from the log that is answered with a position is answered
  with the specification's decision at that position, over the entries the instance that answered
  it had observed, a prefix of the log that contains the position. -/
  retried : ∀ s ∈ r.submitted, (∀ s' ∈ r.submissions, s'.id ≠ s.id) → ∀ (i : Nat) o,
    r.reply s.id = some (.accepted i o) →
    r.observed s.id <+: r.log ∧ i < (r.observed s.id).length ∧
      o = Log.decide reading ι P ω ((r.observed s.id).map (·.entry)) i
  /-- **One entry per retry key.** No two entries of the log have the same retry key: a retry,
  and a duplicate, is not ingested. -/
  keyed : ∀ (i j : Nat) (x y : Logged), r.log[i]? = some x → r.log[j]? = some y →
    x.submission.SameKey P.schema y.submission → i = j
  /-- **Stamping.** Each logged entry is its submission, stamped after the log before it: its
  event, stamped at or after its clock reading and after the stamp of the event before it, or
  the submitted deployment. -/
  stamped : ∀ (i : Nat) (x : Logged), r.log[i]? = some x →
    x.submission.arrival.Stamps (Log.lastTs? ((r.log.take i).map (·.entry))) x.entry
  /-- Every event of the log conforms to the event schema. -/
  conforming : Log.Conforming P r.entries
  /-- A rejection for nonconformance is truthful: the submission is an event that does not
  conform. -/
  nonconforming : ∀ s ∈ r.submitted, r.reply s.id = some (.rejected .nonconforming) →
    ∃ e clock, s.arrival = .event e clock ∧ ¬ e.Conforms P.actionSchema P.schema
  /-- A rejection as a duplicate is truthful: an entry of the log has the submission's retry key,
  and the submission is not a retry of it. -/
  duplicate : ∀ s ∈ r.submitted, r.reply s.id = some (.rejected .duplicate) →
    ∃ x ∈ r.log, s.SameKey P.schema x.submission ∧ ¬ s.RetryOf P.schema W x

/-- **The contract without retries**: the event-log contract for submissions without event ids,
under which every submission is a new one. Its clauses are those of `Run.Meets` without the
retry alternative of `answered`, and without `retried`, `keyed`, and `duplicate`. When no two
submissions share a retry key, `Run.Meets` is this contract, with no rejection as a duplicate,
for every retry window (`Dogwood.Spec.Run.meets_iff_withoutRetries`). -/
structure Run.MeetsWithoutRetries (reading : UpdateReading) (ι : Temporal.ImplChoices)
    (P : PolicySet) (ω : Provider.Providers) (r : Run) : Prop where
  distinct : (r.submitted.map (·.id)).Nodup
  submitted : ∀ s ∈ r.submissions, s ∈ r.submitted
  once : (r.submissions.map (·.id)).Nodup
  answered : ∀ s ∈ r.submitted,
    (∃ i, r.submissions[i]? = some s ∧ ∃ o, r.reply s.id = some (.accepted i o)) ∨
    ((∀ s' ∈ r.submissions, s'.id ≠ s.id) ∧ ∃ why, r.reply s.id = some (.rejected why))
  observedPrefix : ∀ (i : Nat) (x : Logged), r.log[i]? = some x →
    r.observed x.submission.id <+: r.log ∧ i < (r.observed x.submission.id).length
  decided : ∀ (i : Nat) (x : Logged) o, r.log[i]? = some x →
    r.reply x.submission.id = some (.accepted i o) →
    o = Log.decide reading ι P ω ((r.observed x.submission.id).map (·.entry)) i
  stamped : ∀ (i : Nat) (x : Logged), r.log[i]? = some x →
    x.submission.arrival.Stamps (Log.lastTs? ((r.log.take i).map (·.entry))) x.entry
  conforming : Log.Conforming P r.entries
  nonconforming : ∀ s ∈ r.submitted, r.reply s.id = some (.rejected .nonconforming) →
    ∃ e clock, s.arrival = .event e clock ∧ ¬ e.Conforms P.actionSchema P.schema

/-- The submissions of the run have **fresh event ids** under the event schema `S`: no two of
them share a retry key. A run whose submissions carry no event ids has fresh ones. -/
def Run.FreshIds (S : EventSchema) (r : Run) : Prop :=
  ∀ s ∈ r.submitted, ∀ s' ∈ r.submitted, s.SameKey S s' → s.id = s'.id

/-! ## A single instance -/

/-- The state of a single instance that ingests submissions in arrival order:
the accepted submissions so far, with their log entries, and the reply to each submission so
far. -/
structure Sequential where
  log : List Logged
  replies : List (Nat × Reply)

open Classical in
/-- The entry of the log `L` that has the retry key of the submission `s`, with its position, if
there is one. Since no two entries of a log share a retry key (`Run.Meets.keyed`), there is at
most one. -/
noncomputable def Sequential.original? (S : EventSchema) (L : List Logged) (s : Submission) :
    Option (Nat × Logged) :=
  if h : ∃ i x, L[i]? = some x ∧ s.SameKey S x.submission then
    some (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else none

open Classical in
/-- A single instance ingests one more submission. A submission with the retry key of an entry of
its log is a retry of it, answered at its position with the decision there over the log so far,
or a duplicate, rejected; neither changes the log. Any other submission is ingested by
`Log.submit` on its log, which stamps an accepted event after the log's last. -/
noncomputable def Sequential.step (reading : UpdateReading) (ι : Temporal.ImplChoices)
    (P : PolicySet) (ω : Provider.Providers) (W : Nat) (st : Sequential) (s : Submission) :
    Sequential :=
  let log : Log := st.log.map (·.entry)
  match Sequential.original? P.schema st.log s with
  | some (i, x) =>
    if s.RetryOf P.schema W x then
      ⟨st.log, st.replies ++ [(s.id, .accepted i (Log.decide reading ι P ω log i))]⟩
    else ⟨st.log, st.replies ++ [(s.id, .rejected .duplicate)]⟩
  | none =>
    let r := Log.submit reading ι P ω log s.arrival
    match r.2 with
    | .accepted pos o =>
      ⟨st.log ++ [⟨s, s.arrival.entry log.lastTs?⟩], st.replies ++ [(s.id, .accepted pos o)]⟩
    | .rejected why => ⟨st.log, st.replies ++ [(s.id, .rejected why)]⟩

/-- The run of a single instance that ingests the submissions `subs` in arrival
order, from an empty log, with the retry window `W`. Every entry it accepts, and every retry it
answers, is decided over the log it has built so far, which is a prefix of its final log. -/
noncomputable def Run.sequential (reading : UpdateReading) (ι : Temporal.ImplChoices)
    (P : PolicySet) (ω : Provider.Providers) (W : Nat) (subs : List Submission) : Run :=
  let st := subs.foldl (Sequential.step reading ι P ω W) ⟨[], []⟩
  { submitted := subs
    log := st.log
    reply := fun id => st.replies.lookup id
    observed := fun id => st.log.take ((st.log.findIdx (·.submission.id == id)) + 1) }

end Dogwood.Spec
