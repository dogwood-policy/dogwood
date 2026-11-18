import Dogwood.Spec.Contract
import Dogwood.Thm.Ingest

/-!
# Using the event-log contract

What a run that meets the contract (`Run.Meets`) guarantees, stated over the one log:

* `Run.Meets.outcome_eq`: an accepted event's outcome is the specification's decision at its
  position in the whole log, whichever instance decided it and whatever prefix of the log it had
  observed (by `decide_append`);
* `Run.Meets.position_unique`: a submission has at most one position in the log;
* `Run.Meets.logged_retried_or_rejected`: no submission is lost: it is in the log, answered as a
  retry of an entry of the log, or its submitter was told it was rejected;
* `Run.Meets.logged_event`: a logged event is its submission's event, stamped at or after its
  clock reading and after the event before it (`Arrival.Stamps`); ingestion's stamp is the least
  such (`stampAfter_le_of_stamps`);
* `Run.Meets.trace_strictlyIncreasing`: the decisions are made over a trace whose timestamps
  strictly increase, because the log is stamped (`wellFormed_of_stamped`);
* `sequential_meets`: a single instance that ingests the submissions in arrival order meets the
  contract, for every retry window, so the contract is consistent, and `Log.ingest` is an
  implementation of it.

And about retries (`Submission.RetryOf`):

* `Run.Meets.not_logged_of_sameKey`, `Run.Meets.retry_not_logged`: a retry, and any other
  submission with the retry key of an entry of the log, is not in the log;
  `sequential_retry_log`: a single instance's log is the same after a retry as before it;
* `Run.Meets.retry_accepted`, `Run.Meets.retry_reply`: the answer to a retry is its original's,
  the decision at the original's position, whatever came after it in the log, deployments
  included; a retry is otherwise rejected only as unavailable, never as a duplicate or as
  nonconforming; `sequential_retry_reply`: a single instance answers a retry as it answered the
  original;
* `Run.Meets.duplicate_rejected`: a submission with the retry key of an entry of the log that is
  not a retry of it is rejected;
* `Run.meets_iff_withoutRetries`, `Run.meets_zero_iff_withoutRetries`: when no two submissions
  share a retry key, the contract is the contract without retries, with no rejection as a
  duplicate, whatever the window; in particular with the window `0`.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

variable {reading : UpdateReading} {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers}
  {W : Nat} {r : Run}

/-! ## Lists -/

private theorem lookup_append_of_ne {l : List (Nat × Reply)} {k k' : Nat} {v : Reply}
    (hne : k ≠ k') : (l ++ [(k', v)]).lookup k = l.lookup k := by
  have hb : (k == k') = false := by simpa using hne
  induction l with
  | nil => simp only [List.nil_append, List.lookup, hb]
  | cons x l ih =>
    obtain ⟨a, b⟩ := x
    simp only [List.cons_append, List.lookup]
    cases (k == a)
    · exact ih
    · rfl

private theorem lookup_append_new {l : List (Nat × Reply)} {k : Nat} {v : Reply}
    (hnew : k ∉ l.map Prod.fst) : (l ++ [(k, v)]).lookup k = some v := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨a, b⟩ := x
    have ha : (k == a) = false := by
      have : k ≠ a := fun h => hnew (by simp [h])
      simpa using this
    simp only [List.cons_append, List.lookup, ha]
    exact ih (fun h => hnew (by simp [h]))

private theorem eq_of_mem_of_nodup_map {l : List Submission} (hnd : (l.map Submission.id).Nodup)
    {a b : Submission} (ha : a ∈ l) (hb : b ∈ l) (h : a.id = b.id) : a = b := by
  induction l with
  | nil => cases ha
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hx, hnd⟩ := hnd
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [ha', hb']
      · subst ha'; exact absurd ⟨b, hb', h.symm⟩ hx
    · rcases List.mem_cons.mp hb with hb' | hb'
      · subst hb'; exact absurd ⟨a, ha', h⟩ hx
      · exact ih hnd ha' hb'

private theorem getElem?_append_last {α : Type} {l : List α} {a : α} {i : Nat} {x : α}
    (h : (l ++ [a])[i]? = some x) : (i < l.length ∧ l[i]? = some x) ∨ (i = l.length ∧ x = a) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getElem?_append_left hi] at h
    exact .inl ⟨hi, h⟩
  · have hlt : i < (l ++ [a]).length := by
      rcases Nat.lt_or_ge i (l ++ [a]).length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at h; cases h
    have hieq : i = l.length := by simp at hlt; omega
    subst hieq
    rw [List.getElem?_append_right (Nat.le_refl _)] at h
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h
    exact .inr ⟨rfl, h.symm⟩

private theorem lt_length_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α}
    (h : l[i]? = some x) : i < l.length := by
  rcases Nat.lt_or_ge i l.length with hl | hl
  · exact hl
  · rw [List.getElem?_eq_none hl] at h; cases h

/-- Two positions of a list whose values have distinct identities hold the same identity only if
they are the same position. -/
private theorem pos_eq_of_nodup {l : List Submission} (hnd : (l.map Submission.id).Nodup)
    {i j : Nat} {s s' : Submission} (hi : l[i]? = some s) (hj : l[j]? = some s')
    (hid : s.id = s'.id) : i = j := by
  have hil : i < (l.map Submission.id).length := by simpa using lt_length_of_getElem? hi
  have h2 : (l.map Submission.id)[i]? = (l.map Submission.id)[j]? := by
    simp [List.getElem?_map, hi, hj, hid]
  exact (List.getElem?_inj hil hnd).mp h2

/-! ## Retry keys -/

theorem _root_.Dogwood.Spec.Submission.SameKey.symm {S : EventSchema} {s s' : Submission}
    (h : s.SameKey S s') : s'.SameKey S s := by
  obtain ⟨K, h₁, h₂⟩ := h
  exact ⟨K, h₂, h₁⟩

theorem _root_.Dogwood.Spec.Submission.SameKey.trans {S : EventSchema} {a b c : Submission}
    (h₁ : a.SameKey S b) (h₂ : b.SameKey S c) : a.SameKey S c := by
  obtain ⟨K, ha, hb⟩ := h₁
  obtain ⟨K', hb', hc⟩ := h₂
  obtain rfl : K = K' := Option.some.inj (hb.symm.trans hb')
  exact ⟨K, ha, hc⟩

/-- A submission with a retry key carries an event id, and an event. -/
theorem _root_.Dogwood.Spec.Submission.retryKey?_eq_some {S : EventSchema} {s : Submission}
    {K : RetryKey} (h : s.retryKey? S = some K) :
    ∃ e clock, s.eventId = some K.eventId ∧ s.arrival = .event e clock := by
  unfold Submission.retryKey? at h
  split at h
  · rename_i k e clock he ha
    cases h
    exact ⟨e, clock, he, ha⟩
  · cases h

/-- A submission without an event id has no retry key: it is never a retry, nor a duplicate. -/
theorem _root_.Dogwood.Spec.Submission.retryKey?_of_eventId_none {S : EventSchema}
    {s : Submission} (h : s.eventId = none) : s.retryKey? S = none := by
  unfold Submission.retryKey?
  rw [h]

/-! ## The contract -/

/-- **A decision is the specification's at its position in the log.** -/
theorem _root_.Dogwood.Spec.Run.Meets.outcome_eq (h : r.Meets reading ι P ω W) {i : Nat}
    {x : Logged} {o : Outcome} (hs : r.log[i]? = some x)
    (hr : r.reply x.submission.id = some (.accepted i o)) :
    o = Log.decide reading ι P ω r.entries i := by
  rw [h.decided i x o hs hr]
  obtain ⟨hpre, hi⟩ := h.observedPrefix i x hs
  obtain ⟨rest, hrest⟩ := hpre
  have : r.entries = (r.observed x.submission.id).map Logged.entry ++ rest.map Logged.entry := by
    simp [Run.entries, ← hrest]
  rw [this, decide_append _ _ (by simpa using hi)]

/-- A submission has at most one position in the log. -/
theorem _root_.Dogwood.Spec.Run.Meets.position_unique (h : r.Meets reading ι P ω W) {i j : Nat}
    {s s' : Submission} (hi : r.submissions[i]? = some s) (hj : r.submissions[j]? = some s')
    (hid : s.id = s'.id) : i = j :=
  pos_eq_of_nodup h.once hi hj hid

/-- The submission of the entry at position `i` of the log is at position `i` of the
submissions. -/
private theorem submissions_getElem? {i : Nat} {x : Logged} (hx : r.log[i]? = some x) :
    r.submissions[i]? = some x.submission := by
  simp [Run.submissions, List.getElem?_map, hx]

/-- **The reply to a logged submission.** The submission of the entry at position `i` of the log
was told it was accepted at `i`, with the specification's decision there. -/
theorem _root_.Dogwood.Spec.Run.Meets.logged_reply (h : r.Meets reading ι P ω W) {i : Nat}
    {x : Logged} (hx : r.log[i]? = some x) :
    r.reply x.submission.id =
      some (.accepted i (Log.decide reading ι P ω r.entries i)) := by
  have hsub : x.submission ∈ r.submissions := List.mem_of_getElem? (submissions_getElem? hx)
  rcases h.answered x.submission (h.submitted _ hsub) with ⟨i', hi', o, hr⟩ | ⟨hnot, _⟩
  · obtain rfl := h.position_unique hi' (submissions_getElem? hx) rfl
    rw [hr, h.outcome_eq hx hr]
  · exact absurd rfl (hnot _ hsub)

/-- **No submission is lost.** A submission is in the log, or it is a retry of an entry of the
log and was told that entry's position, or its submitter was told it was rejected. -/
theorem _root_.Dogwood.Spec.Run.Meets.logged_retried_or_rejected (h : r.Meets reading ι P ω W)
    {s : Submission} (hs : s ∈ r.submitted) :
    (∃ i : Nat, r.submissions[i]? = some s) ∨
    (∃ i x, r.log[i]? = some x ∧ s.RetryOf P.schema W x ∧
      ∃ o, r.reply s.id = some (.accepted i o)) ∨
    ∃ why, r.reply s.id = some (.rejected why) := by
  rcases h.answered s hs with ⟨i, hi, _⟩ | ⟨_, hretry | hrej⟩
  · exact .inl ⟨i, hi⟩
  · exact .inr (.inl hretry)
  · exact .inr (.inr hrej)

/-- An accepted submission is in the log at the position its submitter was told, or is a retry
of the entry at that position. -/
theorem _root_.Dogwood.Spec.Run.Meets.accepted_position (h : r.Meets reading ι P ω W)
    {s : Submission} (hs : s ∈ r.submitted) {i : Nat} {o : Outcome}
    (hr : r.reply s.id = some (.accepted i o)) :
    r.submissions[i]? = some s ∨
      ((∀ s' ∈ r.submissions, s'.id ≠ s.id) ∧ ∃ x, r.log[i]? = some x ∧ s.RetryOf P.schema W x) := by
  rcases h.answered s hs with ⟨j, hj, o', hr'⟩ | ⟨hnot, ⟨j, x, hx, hk, o', hr'⟩ | ⟨why, hw⟩⟩
  · rw [hr] at hr'
    cases hr'
    exact .inl hj
  · rw [hr] at hr'
    cases hr'
    exact .inr ⟨hnot, x, hx, hk⟩
  · rw [hr] at hw; cases hw

/-- **A logged event is its submission's event, stamped.** Its stamp is at least its clock
reading, and after the stamp of the event before it in the log. -/
theorem _root_.Dogwood.Spec.Run.Meets.logged_event (h : r.Meets reading ι P ω W) {i : Nat}
    {x : Logged} (hx : r.log[i]? = some x) {e : Event} {clock : Int}
    (ha : x.submission.arrival = .event e clock) :
    ∃ t, x.entry = .event ⟨t, e⟩ ∧ clock ≤ t ∧
      ∀ last, Log.lastTs? ((r.log.take i).map Logged.entry) = some last → last < t := by
  have hs := h.stamped i x hx
  rw [ha] at hs
  cases hy : x.entry with
  | deploy rs => rw [hy] at hs; exact hs.elim
  | event p =>
    rw [hy] at hs
    obtain ⟨he, hc, hl⟩ := hs
    exact ⟨p.ts, by rw [← he], hc, hl⟩

/-- **A stamped log keeps the rule.** A list of logged entries, each of which stamps its
submission after the entries before it, has timestamps that strictly increase. -/
theorem wellFormed_of_stamped (L : List Logged)
    (h : ∀ (i : Nat) (x : Logged), L[i]? = some x →
      x.submission.arrival.Stamps (Log.lastTs? ((L.take i).map Logged.entry)) x.entry) :
    Log.WellFormed (L.map Logged.entry) := by
  suffices ∀ n, Log.WellFormed ((L.take n).map Logged.entry) by
    simpa using this L.length
  intro n
  induction n with
  | zero => exact Trace.StrictlyIncreasing.nil
  | succ n ih =>
    rcases Nat.lt_or_ge n L.length with hn | hn
    · have hx : L[n]? = some L[n] := List.getElem?_eq_getElem hn
      rw [List.take_add_one, hx]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
      exact wellFormed_append_of_stamps ih (h n L[n] hx)
    · rw [List.take_of_length_le (by omega)]
      rw [List.take_of_length_le hn] at ih
      exact ih

/-- The decisions of a run that meets the contract are made over a trace whose timestamps
strictly increase. -/
theorem _root_.Dogwood.Spec.Run.Meets.trace_strictlyIncreasing (h : r.Meets reading ι P ω W) :
    r.entries.trace.StrictlyIncreasing :=
  wellFormed_of_stamped r.log h.stamped

/-! ## Retries -/

/-- The entry of the log with the retry key of another entry is that entry. -/
theorem _root_.Dogwood.Spec.Run.Meets.keyed_eq (h : r.Meets reading ι P ω W) {i j : Nat}
    {x y : Logged} (hx : r.log[i]? = some x) (hy : r.log[j]? = some y)
    (hk : x.submission.SameKey P.schema y.submission) : i = j ∧ x = y := by
  obtain rfl := h.keyed i j x y hx hy hk
  rw [hx] at hy
  exact ⟨rfl, Option.some.inj hy⟩

/-- **A submission that shares a retry key with an entry of the log is not in the log**, unless
it is that entry's submission: a retry is not ingested again, and neither is a duplicate. -/
theorem _root_.Dogwood.Spec.Run.Meets.not_logged_of_sameKey (h : r.Meets reading ι P ω W)
    {s : Submission} (hs : s ∈ r.submitted) {i : Nat} {x : Logged} (hx : r.log[i]? = some x)
    (hk : s.SameKey P.schema x.submission) (hne : x.submission.id ≠ s.id) :
    ∀ s' ∈ r.submissions, s'.id ≠ s.id := by
  intro s' hs' heq
  have hss : s' = s := eq_of_mem_of_nodup_map h.distinct (h.submitted _ hs') hs heq
  subst hss
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hs'
  simp only [Run.submissions, List.getElem?_map, Option.map_eq_some_iff] at hj
  obtain ⟨y, hy, rfl⟩ := hj
  obtain ⟨_, rfl⟩ := h.keyed_eq hy hx hk
  exact hne rfl

/-- **A retry is not ingested again.** A retry of an entry of the log, other than the entry's own
submission, is not in the log. -/
theorem _root_.Dogwood.Spec.Run.Meets.retry_not_logged (h : r.Meets reading ι P ω W)
    {s : Submission} (hs : s ∈ r.submitted) {i : Nat} {x : Logged} (hx : r.log[i]? = some x)
    (hk : s.RetryOf P.schema W x) (hne : x.submission.id ≠ s.id) :
    ∀ s' ∈ r.submissions, s'.id ≠ s.id :=
  h.not_logged_of_sameKey hs hx hk.1 hne

/-- **An accepted retry is answered as its original.** A retry of the entry at position `i` of
the log, other than the entry's own submission, that was told it was accepted, was told it was
accepted at `i`, with the specification's decision there over the whole log: the outcome the
entry's submission was told (`Run.Meets.logged_reply`). The decision at `i` depends only on the log
up to `i` (`decide_append`), so an entry after it, a deployment included, does not change the
answer. -/
theorem _root_.Dogwood.Spec.Run.Meets.retry_accepted (h : r.Meets reading ι P ω W)
    {s : Submission} (hs : s ∈ r.submitted) {i : Nat} {x : Logged} (hx : r.log[i]? = some x)
    (hk : s.RetryOf P.schema W x) (hne : x.submission.id ≠ s.id) {j : Nat} {o : Outcome}
    (hr : r.reply s.id = some (.accepted j o)) :
    j = i ∧ o = Log.decide reading ι P ω r.entries i := by
  have hnot := h.retry_not_logged hs hx hk hne
  rcases h.accepted_position hs hr with hj | ⟨_, y, hy, hky⟩
  · exact absurd rfl (hnot s (List.mem_of_getElem? hj))
  · obtain ⟨rfl, rfl⟩ := h.keyed_eq hy hx (hky.1.symm.trans hk.1)
    refine ⟨rfl, ?_⟩
    obtain ⟨⟨rest, hrest⟩, hlt, ho⟩ := h.retried s hs hnot j o hr
    have : r.entries = (r.observed s.id).map Logged.entry ++ rest.map Logged.entry := by
      simp [Run.entries, ← hrest]
    rw [ho, this, decide_append _ _ (by simpa using hlt)]

/-- **The answer to a retry is its original's.** A retry of an entry of the log, other than the
entry's own submission, is told what the entry's submission was told: accepted at the entry's
position, with the decision there. Otherwise it was rejected as unavailable, which the contract
allows of any submission; it is never rejected as a duplicate, nor as nonconforming, since it is
the entry's event. -/
theorem _root_.Dogwood.Spec.Run.Meets.retry_reply (h : r.Meets reading ι P ω W)
    {s : Submission} (hs : s ∈ r.submitted) {i : Nat} {x : Logged} (hx : r.log[i]? = some x)
    (hk : s.RetryOf P.schema W x) (hne : x.submission.id ≠ s.id) :
    r.reply s.id = r.reply x.submission.id ∨ r.reply s.id = some (.rejected .unavailable) := by
  have hnot := h.retry_not_logged hs hx hk hne
  rw [h.logged_reply hx]
  rcases h.answered s hs with ⟨j, hj, _⟩ | ⟨_, ⟨j, y, hy, hky, o, hr⟩ | ⟨why, hw⟩⟩
  · exact absurd rfl (hnot s (List.mem_of_getElem? hj))
  · obtain ⟨rfl, rfl⟩ := h.retry_accepted hs hx hk hne hr
    exact .inl hr
  · cases why with
    | unavailable => exact .inr hw
    | nonconforming =>
      obtain ⟨e, clock, hse, hnc⟩ := h.nonconforming s hs hw
      obtain ⟨_, e', clock', clock₀, p, hse', hxe, hxp, _⟩ := hk
      rw [hse] at hse'
      obtain ⟨rfl, rfl⟩ : e = e' ∧ clock = clock' := by
        cases hse'; exact ⟨rfl, rfl⟩
      have hst := h.stamped i x hx
      rw [hxe, hxp] at hst
      exfalso
      apply hnc
      have hmem : p ∈ r.entries.trace := by
        simp only [Run.entries, Log.trace, List.mem_filterMap, List.mem_map]
        exact ⟨.event p, ⟨x, List.mem_of_getElem? hx, hxp⟩, rfl⟩
      have := h.conforming p hmem
      rwa [hst.1] at this
    | duplicate =>
      obtain ⟨y, hy, hky, hnr⟩ := h.duplicate s hs hw
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hy
      obtain ⟨rfl, rfl⟩ := h.keyed_eq hj hx (hky.symm.trans hk.1)
      exact absurd hk hnr

/-- **A duplicate is rejected.** A submission with the retry key of an entry of the log, other
than the entry's own submission, that is not a retry of it, is not in the log, and its submitter
was told it was rejected. -/
theorem _root_.Dogwood.Spec.Run.Meets.duplicate_rejected (h : r.Meets reading ι P ω W)
    {s : Submission} (hs : s ∈ r.submitted) {i : Nat} {x : Logged} (hx : r.log[i]? = some x)
    (hk : s.SameKey P.schema x.submission) (hne : x.submission.id ≠ s.id)
    (hnr : ¬ s.RetryOf P.schema W x) :
    ∃ why, r.reply s.id = some (.rejected why) := by
  have hnot := h.not_logged_of_sameKey hs hx hk hne
  rcases h.answered s hs with ⟨j, hj, _⟩ | ⟨_, ⟨j, y, hy, hky, _⟩ | hrej⟩
  · exact absurd rfl (hnot s (List.mem_of_getElem? hj))
  · obtain ⟨rfl, rfl⟩ := h.keyed_eq hy hx (hky.1.symm.trans hk)
    exact absurd hky hnr
  · exact hrej

/-! ## Fresh event ids -/

/-- **With fresh event ids, the contract is the contract without retries.** When no two
submissions of a run share a retry key (`Run.FreshIds`), as when no submission carries an event
id, the run meets the contract, whatever the retry window, exactly when it meets the contract
without retries and no submission is rejected as a duplicate. -/
theorem _root_.Dogwood.Spec.Run.meets_iff_withoutRetries (hf : r.FreshIds P.schema) :
    r.Meets reading ι P ω W ↔
      r.MeetsWithoutRetries reading ι P ω ∧
        ∀ s ∈ r.submitted, r.reply s.id ≠ some (.rejected .duplicate) := by
  constructor
  · intro h
    refine ⟨⟨h.distinct, h.submitted, h.once, ?_, h.observedPrefix, h.decided, h.stamped,
      h.conforming, h.nonconforming⟩, ?_⟩
    · intro s hs
      rcases h.answered s hs with ha | ⟨hnot, ⟨i, x, hx, hk, _⟩ | hrej⟩
      · exact .inl ha
      · have hxs : x.submission ∈ r.submissions :=
          List.mem_of_getElem? (submissions_getElem? hx)
        exact absurd (hf s hs _ (h.submitted _ hxs) hk.1).symm (hnot _ hxs)
      · exact .inr ⟨hnot, hrej⟩
    · intro s hs hd
      obtain ⟨y, hy, hky, _⟩ := h.duplicate s hs hd
      have hys : y.submission ∈ r.submissions := List.mem_map_of_mem hy
      have hid := hf s hs _ (h.submitted _ hys) hky
      rcases h.answered s hs with ⟨_, _, o, hr⟩ | ⟨hnot, _⟩
      · rw [hd] at hr; cases hr
      · exact hnot _ hys hid.symm
  · rintro ⟨h, hd⟩
    refine ⟨h.distinct, h.submitted, h.once, ?_, h.observedPrefix, h.decided, ?_, ?_,
      h.stamped, h.conforming, h.nonconforming, ?_⟩
    · intro s hs
      rcases h.answered s hs with ha | ⟨hnot, hrej⟩
      · exact .inl ha
      · exact .inr ⟨hnot, .inr hrej⟩
    · intro s hs hnot i o hr
      rcases h.answered s hs with ⟨j, hj, _⟩ | ⟨_, why, hw⟩
      · exact absurd rfl (hnot s (List.mem_of_getElem? hj))
      · rw [hr] at hw; cases hw
    · intro i j x y hx hy hk
      have hxs := List.mem_of_getElem? (submissions_getElem? (r := r) hx)
      have hys := List.mem_of_getElem? (submissions_getElem? (r := r) hy)
      exact pos_eq_of_nodup h.once (submissions_getElem? hx) (submissions_getElem? hy)
        (hf _ (h.submitted _ hxs) _ (h.submitted _ hys) hk)
    · intro s hs hdup
      exact absurd hdup (hd s hs)

/-- **With the window `0` and fresh event ids, the contract is the contract without retries**:
`Run.meets_iff_withoutRetries`, at the window `0`. When ids are fresh, no window plays a part. -/
theorem _root_.Dogwood.Spec.Run.meets_zero_iff_withoutRetries (hf : r.FreshIds P.schema) :
    r.Meets reading ι P ω 0 ↔
      r.MeetsWithoutRetries reading ι P ω ∧
        ∀ s ∈ r.submitted, r.reply s.id ≠ some (.rejected .duplicate) :=
  Run.meets_iff_withoutRetries hf

/-! ## A single instance meets the contract -/

theorem _root_.Dogwood.Spec.Sequential.original?_some {S : EventSchema} {L : List Logged} {s : Submission} {i : Nat}
    {x : Logged} (h : Sequential.original? S L s = some (i, x)) :
    L[i]? = some x ∧ s.SameKey S x.submission := by
  unfold Sequential.original? at h
  split at h
  · rename_i hex
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Classical.choose_spec (Classical.choose_spec hex)
  · cases h

theorem _root_.Dogwood.Spec.Sequential.original?_none {S : EventSchema} {L : List Logged} {s : Submission}
    (h : Sequential.original? S L s = none) :
    ∀ (i : Nat) (x : Logged), L[i]? = some x → ¬ s.SameKey S x.submission := by
  intro i x hx hk
  unfold Sequential.original? at h
  split at h
  · cases h
  · rename_i hex
    exact hex ⟨i, x, hx, hk⟩

theorem _root_.Dogwood.Spec.Sequential.step_retry {st : Sequential} {s : Submission} {i : Nat} {x : Logged}
    (ho : Sequential.original? P.schema st.log s = some (i, x)) (hr : s.RetryOf P.schema W x) :
    Sequential.step reading ι P ω W st s =
      ⟨st.log, st.replies ++
        [(s.id, .accepted i (Log.decide reading ι P ω (st.log.map Logged.entry) i))]⟩ := by
  simp only [Sequential.step, ho, hr, if_true]

theorem _root_.Dogwood.Spec.Sequential.step_duplicate {st : Sequential} {s : Submission} {i : Nat} {x : Logged}
    (ho : Sequential.original? P.schema st.log s = some (i, x)) (hr : ¬ s.RetryOf P.schema W x) :
    Sequential.step reading ι P ω W st s =
      ⟨st.log, st.replies ++ [(s.id, .rejected .duplicate)]⟩ := by
  simp only [Sequential.step, ho, hr, if_false]

theorem _root_.Dogwood.Spec.Sequential.step_fresh {st : Sequential} {s : Submission}
    (ho : Sequential.original? P.schema st.log s = none) :
    Sequential.step reading ι P ω W st s =
      match (Log.submit reading ι P ω (st.log.map Logged.entry) s.arrival).2 with
      | .accepted pos o =>
        ⟨st.log ++ [⟨s, s.arrival.entry (Log.lastTs? (st.log.map Logged.entry))⟩],
          st.replies ++ [(s.id, .accepted pos o)]⟩
      | .rejected why => ⟨st.log, st.replies ++ [(s.id, .rejected why)]⟩ := by
  simp only [Sequential.step, ho]
  rfl

/-- **A retry, and a duplicate, does not change a single instance's log.** -/
theorem _root_.Dogwood.Spec.Sequential.step_log_of_sameKey {st : Sequential} {s : Submission} {i : Nat} {x : Logged}
    (hx : st.log[i]? = some x) (hk : s.SameKey P.schema x.submission) :
    (Sequential.step reading ι P ω W st s).log = st.log := by
  cases ho : Sequential.original? P.schema st.log s with
  | none => exact absurd hk (Sequential.original?_none ho i x hx)
  | some ix =>
    obtain ⟨j, y⟩ := ix
    by_cases hr : s.RetryOf P.schema W y
    · rw [Sequential.step_retry ho hr]
    · rw [Sequential.step_duplicate ho hr]

/-- Ingestion rejects an arrival only as nonconforming. -/
theorem nonconformance?_eq_some {x : Arrival} {why : Rejection}
    (h : x.nonconformance? P = some why) : why = .nonconforming := by
  cases x with
  | deploy rs => cases h
  | event e clock =>
    by_cases hc : e.Conforms P.actionSchema P.schema
    · rw [Arrival.nonconformance?, if_pos hc] at h
      cases h
    · rw [Arrival.nonconformance?, if_neg hc] at h
      exact (Option.some.inj h).symm

/-- What a single instance's state records after the submissions `done`: its log's submissions
are a sublist of them; it replied to each, in order; each logged submission was stamped after
the log before it, and decided over the log up to it; no two logged submissions share a retry
key; each submission absent from the log is a retry of an entry of the log, answered at its
position with the decision there over the log, or was rejected, truthfully for nonconformance and
for a duplicate; and the log holds only conforming events. -/
structure SeqInv (reading : UpdateReading) (ι : ImplChoices) (P : PolicySet)
    (ω : Provider.Providers) (W : Nat) (done : List Submission) (st : Sequential) : Prop where
  sublist : (st.log.map Logged.submission).Sublist done
  ids : st.replies.map Prod.fst = done.map Submission.id
  logged : ∀ (i : Nat) (x : Logged), st.log[i]? = some x → ∃ o,
    st.replies.lookup x.submission.id = some (.accepted i o) ∧
    o = Log.decide reading ι P ω ((st.log.take (i + 1)).map Logged.entry) i
  stamped : ∀ (i : Nat) (x : Logged), st.log[i]? = some x →
    x.entry = x.submission.arrival.entry (Log.lastTs? ((st.log.take i).map Logged.entry))
  keyed : ∀ (i j : Nat) (x y : Logged), st.log[i]? = some x → st.log[j]? = some y →
    x.submission.SameKey P.schema y.submission → i = j
  unlogged : ∀ s ∈ done, (∀ x ∈ st.log, x.submission.id ≠ s.id) →
    (∃ i x, st.log[i]? = some x ∧ s.RetryOf P.schema W x ∧
      st.replies.lookup s.id =
        some (.accepted i (Log.decide reading ι P ω (st.log.map Logged.entry) i))) ∨
    ∃ why, st.replies.lookup s.id = some (.rejected why) ∧
      (why = .nonconforming → ∃ e clock, s.arrival = .event e clock ∧
        ¬ e.Conforms P.actionSchema P.schema) ∧
      (why = .duplicate → ∃ x ∈ st.log, s.SameKey P.schema x.submission ∧
        ¬ s.RetryOf P.schema W x)
  conforming : Log.Conforming P (st.log.map Logged.entry)

/-- A step that leaves the log alone and replies `v` to `s` keeps the invariant, given that `v`
is a truthful reply for a submission absent from the log. -/
private theorem seqInv_keep {done : List Submission} {st : Sequential} {s : Submission}
    {v : Reply} (hinv : SeqInv reading ι P ω W done st) (hnew : s.id ∉ done.map Submission.id)
    (hv : (∃ i x, st.log[i]? = some x ∧ s.RetryOf P.schema W x ∧
        v = .accepted i (Log.decide reading ι P ω (st.log.map Logged.entry) i)) ∨
      ∃ why, v = .rejected why ∧
        (why = .nonconforming → ∃ e clock, s.arrival = .event e clock ∧
          ¬ e.Conforms P.actionSchema P.schema) ∧
        (why = .duplicate → ∃ x ∈ st.log, s.SameKey P.schema x.submission ∧
          ¬ s.RetryOf P.schema W x)) :
    SeqInv reading ι P ω W (done ++ [s]) ⟨st.log, st.replies ++ [(s.id, v)]⟩ := by
  have hnew' : s.id ∉ st.replies.map Prod.fst := by rw [hinv.ids]; exact hnew
  have hlogid : ∀ x ∈ st.log, x.submission.id ≠ s.id := by
    intro x hx heq
    exact hnew (heq ▸ List.mem_map_of_mem (hinv.sublist.subset (List.mem_map_of_mem hx)))
  refine ⟨hinv.sublist.trans (List.sublist_append_left _ _), by simp [hinv.ids], ?_,
    hinv.stamped, hinv.keyed, ?_, hinv.conforming⟩
  · intro i x hx
    obtain ⟨o, hl, ho⟩ := hinv.logged i x hx
    have hne : x.submission.id ≠ s.id := hlogid x (List.mem_of_getElem? hx)
    exact ⟨o, by simp only [lookup_append_of_ne hne, hl], ho⟩
  · intro s' hs' hnotin
    rcases List.mem_append.mp hs' with hs' | hs'
    · have hne : s'.id ≠ s.id := by
        intro h
        apply hnew
        rw [← h]
        exact List.mem_map_of_mem hs'
      simp only [lookup_append_of_ne hne]
      exact hinv.unlogged s' hs' hnotin
    · simp only [List.mem_singleton] at hs'
      subst hs'
      simp only [lookup_append_new hnew', Option.some.injEq]
      rcases hv with ⟨i, x, hx, hk, rfl⟩ | ⟨why, rfl, hw⟩
      · exact .inl ⟨i, x, hx, hk, rfl⟩
      · exact .inr ⟨why, rfl, hw⟩

theorem seqInv_step {done : List Submission} {st : Sequential} {s : Submission}
    (hinv : SeqInv reading ι P ω W done st) (hnew : s.id ∉ done.map Submission.id) :
    SeqInv reading ι P ω W (done ++ [s]) (Sequential.step reading ι P ω W st s) := by
  have hnew' : s.id ∉ st.replies.map Prod.fst := by rw [hinv.ids]; exact hnew
  have hlogid : ∀ x ∈ st.log, x.submission.id ≠ s.id := by
    intro x hx heq
    exact hnew (heq ▸ List.mem_map_of_mem (hinv.sublist.subset (List.mem_map_of_mem hx)))
  have hlen : (st.log.map Logged.entry).length = st.log.length := by simp
  cases ho : Sequential.original? P.schema st.log s with
  | some ix =>
    obtain ⟨i, x⟩ := ix
    obtain ⟨hx, hk⟩ := Sequential.original?_some ho
    by_cases hr : s.RetryOf P.schema W x
    · rw [Sequential.step_retry ho hr]
      exact seqInv_keep hinv hnew (.inl ⟨i, x, hx, hr, rfl⟩)
    · rw [Sequential.step_duplicate ho hr]
      exact seqInv_keep hinv hnew
        (.inr ⟨.duplicate, rfl, (fun h => Rejection.noConfusion h),
          fun _ => ⟨x, List.mem_of_getElem? hx, hk, hr⟩⟩)
  | none =>
    rw [Sequential.step_fresh ho]
    cases hr : s.arrival.nonconformance? P with
    | some why =>
      simp only [submit_rejected hr]
      have hwhy := nonconformance?_eq_some hr
      subst hwhy
      refine seqInv_keep hinv hnew
        (.inr ⟨.nonconforming, rfl, fun _ => ?_, (fun h => Rejection.noConfusion h)⟩)
      cases hx : s.arrival with
      | deploy rs => rw [hx] at hr; cases hr
      | event e clock =>
        rw [hx] at hr
        refine ⟨e, clock, rfl, fun hc => ?_⟩
        rw [nonconformance?_event_eq_none.mpr hc] at hr
        cases hr
    | none =>
      let y : Logged := ⟨s, s.arrival.entry (Log.lastTs? (st.log.map Logged.entry))⟩
      simp only [submit_accepted hr, hlen]
      have hmap : (st.log ++ [y]).map Logged.entry = st.log.map Logged.entry ++ [y.entry] := by
        simp
      refine ⟨?_, by simp [hinv.ids], ?_, ?_, ?_, ?_, ?_⟩
      · simpa [y] using hinv.sublist.append (List.Sublist.refl [s])
      · intro i x hx
        rcases getElem?_append_last hx with ⟨hi, hx⟩ | ⟨rfl, rfl⟩
        · obtain ⟨o, hl, ho⟩ := hinv.logged i x hx
          have hne : x.submission.id ≠ s.id := hlogid x (List.mem_of_getElem? hx)
          refine ⟨o, by simp only [lookup_append_of_ne hne, hl], ?_⟩
          rw [ho, List.take_append_of_le_length (by omega)]
        · refine ⟨_, lookup_append_new hnew', ?_⟩
          rw [List.take_of_length_le (by simp), hmap]
      · intro i x hx
        rcases getElem?_append_last hx with ⟨hi, hx⟩ | ⟨rfl, rfl⟩
        · rw [List.take_append_of_le_length (by omega)]
          exact hinv.stamped i x hx
        · rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      · intro i j x x' hx hx' hk
        rcases getElem?_append_last hx with ⟨hi, hx⟩ | ⟨rfl, rfl⟩ <;>
          rcases getElem?_append_last hx' with ⟨hj, hx'⟩ | ⟨rfl, rfl⟩
        · exact hinv.keyed i j x x' hx hx' hk
        · exact absurd hk.symm (Sequential.original?_none ho i x hx)
        · exact absurd hk (Sequential.original?_none ho j x' hx')
        · rfl
      · intro s' hs' hnotin
        have hne : s'.id ≠ s.id := fun h => hnotin y (by simp [y]) (by simp [y, h])
        rcases List.mem_append.mp hs' with hs' | hs'
        · simp only [lookup_append_of_ne hne]
          rcases hinv.unlogged s' hs' fun x hx => hnotin x (List.mem_append_left _ hx) with
            ⟨i, x, hx, hk, hl⟩ | ⟨why, hl, hwn, hwd⟩
          · have hi := lt_length_of_getElem? hx
            refine .inl ⟨i, x, by rw [List.getElem?_append_left hi]; exact hx, hk, ?_⟩
            rw [hl, hmap, decide_append _ _ (by rw [hlen]; exact hi)]
          · refine .inr ⟨why, hl, hwn, fun hd => ?_⟩
            obtain ⟨x, hx, hk, hnr⟩ := hwd hd
            exact ⟨x, List.mem_append_left _ hx, hk, hnr⟩
        · simp only [List.mem_singleton] at hs'
          exact absurd hs' (fun h => hne (h ▸ rfl))
      · have := conforming_submit (reading := reading) (ι := ι) (P := P) (ω := ω)
          hinv.conforming s.arrival
        rw [submit_accepted hr] at this
        rw [hmap]
        exact this

theorem seqInv_foldl : ∀ (subs : List Submission) (done : List Submission) (st : Sequential),
    ((done ++ subs).map Submission.id).Nodup → SeqInv reading ι P ω W done st →
    SeqInv reading ι P ω W (done ++ subs) (subs.foldl (Sequential.step reading ι P ω W) st)
  | [], done, st, _, hinv => by simpa using hinv
  | s :: subs, done, st, hnd, hinv => by
    simp only [List.foldl_cons]
    have hnew : s.id ∉ done.map Submission.id := by
      intro hm
      have hnd' : ((done ++ [s]).map Submission.id).Nodup := by
        apply List.Nodup.sublist _ hnd
        simp only [List.map_append]
        exact (List.Sublist.refl _).append (by simp)
      simp only [List.map_append, List.map_cons, List.map_nil] at hnd'
      exact (List.nodup_append.mp hnd').2.2 _ hm _ (List.mem_singleton_self _) rfl
    have := seqInv_foldl subs (done ++ [s]) _ (by simpa using hnd) (seqInv_step hinv hnew)
    simpa using this

/-- **A single instance meets the contract.** Ingesting submissions with distinct identities
in arrival order, one at a time, answering a retry of an entry of the log at its position and
rejecting a duplicate, and ingesting any other submission with `Log.submit`, meets the event-log
contract, for every retry window. -/
theorem sequential_meets (W : Nat) (subs : List Submission)
    (hnd : (subs.map Submission.id).Nodup) :
    (Run.sequential reading ι P ω W subs).Meets reading ι P ω W := by
  have hinv := seqInv_foldl (reading := reading) (ι := ι) (P := P) (ω := ω) (W := W) subs []
    ⟨[], []⟩ (by simpa using hnd)
    ⟨List.nil_sublist _, rfl, by simp, by simp, by simp, fun s hs => by simp at hs,
      fun _ h => by simp [Log.trace] at h⟩
  simp only [List.nil_append] at hinv
  generalize hst : subs.foldl (Sequential.step reading ι P ω W) ⟨[], []⟩ = st at hinv
  have hlogids : ((st.log.map Logged.submission).map Submission.id).Nodup :=
    (hinv.sublist.map _).nodup hnd
  -- The position of a logged submission is where `findIdx` finds its identity.
  have hfind : ∀ (i : Nat) (x : Logged), st.log[i]? = some x →
      st.log.findIdx (·.submission.id == x.submission.id) = i := by
    intro i x hx
    have hi := lt_length_of_getElem? hx
    rw [List.findIdx_eq hi]
    have hxi : st.log[i] = x := by rw [List.getElem?_eq_getElem hi] at hx; exact Option.some.inj hx
    refine ⟨by simp [hxi], fun j hji => ?_⟩
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro heq
    have := (List.getElem?_inj (l := (st.log.map Logged.submission).map Submission.id) (i := j)
      (j := i) (by simp; omega) hlogids).mp
      (by simp [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem
        (Nat.lt_trans hji hi), hxi, heq])
    omega
  -- An absent submission's instance had observed the whole log.
  have hwhole : ∀ s : Submission, (∀ x ∈ st.log, x.submission.id ≠ s.id) →
      st.log.take ((st.log.findIdx (·.submission.id == s.id)) + 1) = st.log := by
    intro s hs
    rw [List.findIdx_eq_length_of_false (fun x hx => by simpa using hs x hx)]
    exact List.take_of_length_le (by omega)
  have hsub : ∀ (i : Nat) (x : Logged), st.log[i]? = some x →
      (st.log.map Logged.submission)[i]? = some x.submission := by
    intro i x hx
    simp [List.getElem?_map, hx]
  -- A submission absent from the log, as `Run.Meets` states it, is absent from the state's log.
  have habsent : ∀ s : Submission, (∀ s' ∈ st.log.map Logged.submission, s'.id ≠ s.id) →
      ∀ x ∈ st.log, x.submission.id ≠ s.id :=
    fun s h x hx => h _ (List.mem_map_of_mem hx)
  unfold Run.sequential
  dsimp only
  rw [hst]
  refine ⟨hnd, fun s hs => hinv.sublist.subset hs, hlogids, ?_, ?_, ?_, ?_, hinv.keyed,
    fun i x hx => by rw [hinv.stamped i x hx]; exact stamps_entry _ _, hinv.conforming, ?_, ?_⟩
  · intro s hs
    by_cases hin : ∃ x ∈ st.log, x.submission.id = s.id
    · obtain ⟨x, hx, hid⟩ := hin
      -- `x` is the log entry of `s`: identities are distinct among the submissions.
      have hxs : x.submission = s := by
        have h1 : x.submission ∈ subs :=
          hinv.sublist.subset (List.mem_map_of_mem hx)
        exact eq_of_mem_of_nodup_map hnd h1 hs hid
      obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
      have hget : st.log[i]? = some x := by rw [List.getElem?_eq_getElem hi, hxi]
      obtain ⟨o, hl, _⟩ := hinv.logged i x hget
      exact .inl ⟨i, by show (st.log.map Logged.submission)[i]? = some s; rw [hsub i x hget, hxs],
        o, by rw [← hxs]; exact hl⟩
    · simp only [not_exists, not_and] at hin
      have hnot : ∀ s' ∈ st.log.map Logged.submission, s'.id ≠ s.id := by
        intro s' hs' heq
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs'
        exact hin x hx heq
      refine .inr ⟨hnot, ?_⟩
      rcases hinv.unlogged s hs hin with ⟨i, x, hx, hk, hl⟩ | ⟨why, hl, _⟩
      · exact .inl ⟨i, x, hx, hk, _, hl⟩
      · exact .inr ⟨why, hl⟩
  · intro (i : Nat) (x : Logged) hx
    dsimp only at hx ⊢
    rw [hfind i x hx]
    refine ⟨List.take_prefix _ _, ?_⟩
    have hi := lt_length_of_getElem? hx
    simp; omega
  · intro (i : Nat) (x : Logged) o hx hr
    dsimp only at hx hr ⊢
    obtain ⟨o', hl, ho'⟩ := hinv.logged i x hx
    rw [hl, Option.some.injEq, Reply.accepted.injEq] at hr
    rw [← hr.2, ho', hfind i x hx]
  · intro s hs hnot i o hr
    dsimp only at hs hnot hr ⊢
    have hin := habsent s hnot
    rw [hwhole s hin]
    rcases hinv.unlogged s hs hin with ⟨j, x, hx, _, hl⟩ | ⟨why, hl, _⟩
    · rw [hl, Option.some.injEq, Reply.accepted.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨List.prefix_refl _, lt_length_of_getElem? hx, rfl⟩
    · rw [hl] at hr; cases hr
  · intro s hs hr
    dsimp only at hs hr
    by_cases hin : ∃ x ∈ st.log, x.submission.id = s.id
    · obtain ⟨x, hx, hid⟩ := hin
      obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
      obtain ⟨o, hl, _⟩ := hinv.logged i x (by rw [List.getElem?_eq_getElem hi, hxi])
      rw [hid] at hl
      rw [hl] at hr; cases hr
    · simp only [not_exists, not_and] at hin
      rcases hinv.unlogged s hs hin with ⟨_, _, _, _, hl⟩ | ⟨why, hl, hwc, _⟩
      · rw [hl] at hr; cases hr
      · rw [hl, Option.some.injEq, Reply.rejected.injEq] at hr
        exact hwc hr
  · intro s hs hr
    dsimp only at hs hr
    by_cases hin : ∃ x ∈ st.log, x.submission.id = s.id
    · obtain ⟨x, hx, hid⟩ := hin
      obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
      obtain ⟨o, hl, _⟩ := hinv.logged i x (by rw [List.getElem?_eq_getElem hi, hxi])
      rw [hid] at hl
      rw [hl] at hr; cases hr
    · simp only [not_exists, not_and] at hin
      rcases hinv.unlogged s hs hin with ⟨_, _, _, _, hl⟩ | ⟨why, hl, _, hwd⟩
      · rw [hl] at hr; cases hr
      · rw [hl, Option.some.injEq, Reply.rejected.injEq] at hr
        exact hwd hr

/-- **A retry does not change the log.** A single instance that has ingested the submissions
`subs` has the same log after a retry of one of its entries as before it. -/
theorem sequential_retry_log (W : Nat) (subs : List Submission) {s : Submission} {x : Logged}
    (hx : x ∈ (Run.sequential reading ι P ω W subs).log) (hk : s.RetryOf P.schema W x) :
    (Run.sequential reading ι P ω W (subs ++ [s])).log =
      (Run.sequential reading ι P ω W subs).log := by
  unfold Run.sequential at hx ⊢
  dsimp only at hx ⊢
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  exact Sequential.step_log_of_sameKey hi hk.1

/-- **A single instance answers a retry as it answered the original.** After the submissions
`subs`, a retry of an entry of the log they built gets the reply the entry's submission got. -/
theorem sequential_retry_reply (W : Nat) (subs : List Submission) {s : Submission} {x : Logged}
    (hnd : ((subs ++ [s]).map Submission.id).Nodup)
    (hx : x ∈ (Run.sequential reading ι P ω W subs).log) (hk : s.RetryOf P.schema W x) :
    (Run.sequential reading ι P ω W (subs ++ [s])).reply s.id =
      (Run.sequential reading ι P ω W subs).reply x.submission.id := by
  have hinv := seqInv_foldl (reading := reading) (ι := ι) (P := P) (ω := ω) (W := W) subs []
    ⟨[], []⟩ (by simpa using List.Nodup.sublist (by simp) hnd)
    ⟨List.nil_sublist _, rfl, by simp, by simp, by simp, fun s hs => by simp at hs,
      fun _ h => by simp [Log.trace] at h⟩
  simp only [List.nil_append] at hinv
  unfold Run.sequential at hx ⊢
  dsimp only at hx ⊢
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  generalize subs.foldl (Sequential.step reading ι P ω W) ⟨[], []⟩ = st at hinv hx ⊢
  have hnew : s.id ∉ subs.map Submission.id := by
    simp only [List.map_append, List.map_cons, List.map_nil] at hnd
    exact fun hm => (List.nodup_append.mp hnd).2.2 _ hm _ (List.mem_singleton_self _) rfl
  have hnew' : s.id ∉ st.replies.map Prod.fst := by rw [hinv.ids]; exact hnew
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  cases ho : Sequential.original? P.schema st.log s with
  | none => exact absurd hk.1 (Sequential.original?_none ho i x hi)
  | some jy =>
    obtain ⟨j, y⟩ := jy
    obtain ⟨hj, hky⟩ := Sequential.original?_some ho
    have hij := hinv.keyed i j x y hi hj (hk.1.symm.trans hky)
    subst hij
    rw [hi] at hj
    obtain rfl := Option.some.inj hj
    rw [Sequential.step_retry ho hk]
    dsimp only
    rw [lookup_append_new hnew']
    obtain ⟨o, hl, ho'⟩ := hinv.logged i x hi
    rw [hl, ho']
    have hlt := lt_length_of_getElem? hi
    have hsplit : st.log.map Logged.entry =
        (st.log.take (i + 1)).map Logged.entry ++ (st.log.drop (i + 1)).map Logged.entry := by
      rw [← List.map_append, List.take_append_drop]
    rw [hsplit, decide_append _ _ (by simp; omega)]

end Dogwood.Thm
