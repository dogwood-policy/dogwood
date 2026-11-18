import Dogwood.Examples.Common
import Dogwood.Thm.TemporalLaws
import Dogwood.Thm.Readings

/-!
# Worked example: rate limits

A rate limit built on the windowed count of the examples (`temporal_count_formerly_login`,
`cap_open_agent_prs_windowed`): a `permit` that counts, per key, the events of a kind in a window.

```text
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    (count for (t: Timepoint). where (
        formerly within W (Drupe::Action::"Read"::<kind>{} && tp(t))
    )) < N
};
```

under the default (pinned) event schema, so the count is of the caller's own events. Unlike the
other worked examples, which replay one trace, this file proves guarantees over every trace.

* **Counting requests** (`allowed_requests_lt`): on every trace whose timestamps never decrease,
  fewer than `N` of a caller's `Read` requests in any interval of length `W` are allowed. The
  bound is `N − 1`, not `N`: the request being decided is in the trace, and counts itself.
  Denied requests count too, so the policy limits attempts. Nothing is assumed of the service.
* **Counting responses** (`responses_le`), the idiom of `cap_open_agent_prs_windowed`, which
  counts completed operations so that denials use up nothing: at most `N` of a caller's `Read`
  responses fall in any interval of length `W`, under two assumptions about the service that
  logs the responses, stated in this file and nowhere in the semantics:
  - **responses follow allows** (`ResponsesFollowAllows`): each response answers an earlier
    allowed request of the same caller, and no two answer the same request;
  - **no race** (`NoRace`): a response is logged before the caller's next request.
* **The race is real** (`race_exceeds`): without `NoRace`, a cap of one response an hour admits
  two, when the second request is decided before the first one's response is logged.

The cap of the race, and a request limit of three an hour, are valid policy sets (`cap_valid`,
`requestLimit_valid`).

The semantics links no response to its request: `request` and `response` are kinds of events
that the service submits. The two assumptions are about the service, not the language.
-/

namespace Dogwood.Examples.RateLimit

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Cedar.Spec (EntityUID Value)

def read : EntityUID := action "Read"

def actions : List ActionDecl := [(read, [("doc", .string)])]

def schema : EventSchema := defaultSchema true actions

/-- `count for (t: Timepoint). where (formerly within w (Read::<kind>{} && tp(t)))` -/
def countOf (w : Window) (kind : String) : Aggregate :=
  .count [⟨"t", .timepoint⟩] (.formerly w (.and (.pred read kind []) (.tp "t")))

/-- The condition: fewer than `n` such events. -/
def limit (w : Window) (n : Int64) (kind : String) : Formula :=
  .cmp .lt (.agg (countOf w kind)) (.long n)

/-- `Read` is allowed while the caller has made fewer than `n` requests within `w`. -/
def requestLimit (w : Window) (n : Int64) : PolicySet :=
  onePolicy read (limit w n "request") schema actions

/-- `Read` is allowed while the caller has had fewer than `n` responses within `w`. -/
def responseLimit (w : Window) (n : Int64) : PolicySet :=
  onePolicy read (limit w n "response") schema actions

/-! ## After pin injection -/

/-- The predicate after pin injection: the event's logged caller is the decision's principal. -/
def pinnedPred (kind : String) : Formula :=
  .pred read kind [(["callerPrincipal"], .scope .principal [])]

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

theorem pinsOf_read {kind : String} (hk : kind = "request" ∨ kind = "response") :
    schema.pinsOf read kind = [callerPin] := by
  rcases hk with rfl | rfl <;> decide

theorem limit_injected {w : Window} {n : Int64} {kind : String}
    (hk : kind = "request" ∨ kind = "response") :
    (limit w n kind).injectPins schema =
      .cmp .lt (.agg (.count [⟨"t", .timepoint⟩]
        (.formerly w (.and (pinnedPred kind) (.tp "t"))))) (.long n) := by
  simp [limit, countOf, pinnedPred, Formula.injectPins, Term.injectPins, Aggregate.injectPins,
    pinsOf_read hk, callerPin, PinRef.toTerm]

/-! ## A caller's events -/

/-- The timepoint `p` is a `Read` event of kind `kind` that logs `u` as its caller. -/
def ByCaller (u : EntityUID) (kind : String) (p : TimePoint) : Prop :=
  p.event.action = read ∧ p.event.kind = kind ∧
    recordPath? p.event.logged ["callerPrincipal"] = some (.prim (.entityUID u))

section

variable {ι : ImplChoices} {σ : Trace} {e : Event} {vis : Nat → Prop}

/-- At a decision of `u`'s, the pinned predicate matches exactly `u`'s events of the kind. -/
theorem sat_pinnedPred {u : EntityUID} (he : e.principal = some u) (kind : String)
    (v : Valuation) (k : Nat) :
    Sat ι .seconds σ e vis v k (pinnedPred kind) ↔ ∃ p, σ[k]? = some p ∧ ByCaller u kind p := by
  simp only [Sat, pinnedPred, ArgsMatch, List.mem_singleton, forall_eq]
  simp only [Term.Matches, Term.eval?, Event.scopePath?, Event.scope, he, Option.map_some,
    Option.some.injEq, TVal.val.injEq, ByCaller]
  constructor
  · rintro ⟨p, hp, ha, hk, w, hw, rfl⟩
    exact ⟨p, hp, ha, hk, hw⟩
  · rintro ⟨p, hp, ha, hk, hw⟩
    exact ⟨p, hp, ha, hk, _, hw, rfl⟩

/-- `u`'s `Read` requests and responses are visible to a decision of `u`'s: they are `u`'s on the
universal pin. -/
theorem visible_of_byCaller {u : EntityUID} (he : e.principal = some u) {kind : String}
    (hk : kind = "request" ∨ kind = "response") {k : Nat} {p : TimePoint}
    (hp : σ[k]? = some p) (hb : ByCaller u kind p) : schema.Visible σ e k := by
  obtain ⟨ha, hkind, hpin⟩ := hb
  refine Or.inr ⟨p, hp, ⟨?_, ?_⟩⟩
  · rcases hk with rfl | rfl
    · exact ⟨⟨read, "request", true, [callerPin], actionFields [("doc", .string)]⟩,
        List.mem_cons_self .., ha.symm, hkind.symm⟩
    · exact ⟨⟨read, "response", false, [callerPin], actionFields [("doc", .string)]⟩,
        List.mem_cons_of_mem _ (List.mem_cons_self ..), ha.symm, hkind.symm⟩
  · rw [universalPins_schema]
    intro pin hpin'
    simp only [List.mem_singleton] at hpin'
    subst hpin'
    exact ⟨_, hpin, by simp [callerPin, PinRef.toTerm, Term.eval?, Event.scopePath?, Event.scope,
      he]⟩

end

/-! ## Traces and intervals -/

theorem ts_le_of_le {σ : Trace} (hσ : σ.Nondecreasing) {i j : Nat} {pi pj : TimePoint}
    (hij : i ≤ j) (hi : σ[i]? = some pi) (hj : σ[j]? = some pj) : pi.ts ≤ pj.ts := by
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
    exact List.pairwise_iff_getElem.mp hσ i j hi' hj' hlt
  · rw [hi] at hj
    cases hj
    exact Int.le_refl _

/-- Timepoint `j` of `σ` lies in the closed interval of length `w` from `t₀`. -/
def InInterval (σ : Trace) (t₀ : Int) (w : Window) (j : Nat) : Prop :=
  ∃ p, σ[j]? = some p ∧ t₀ ≤ p.ts ∧ p.ts ≤ t₀ + w.ticks .seconds

/-- A nonempty list of naturals has a largest element. -/
theorem exists_max {J : List Nat} (h : J ≠ []) : ∃ m ∈ J, ∀ j ∈ J, j ≤ m := by
  induction J with
  | nil => exact absurd rfl h
  | cons x xs ih =>
    by_cases hx : xs = []
    · subst hx; exact ⟨x, List.mem_singleton_self _, fun j hj => by simp at hj; omega⟩
    · obtain ⟨m, hm, hle⟩ := ih hx
      by_cases hxm : x ≤ m
      · exact ⟨m, List.mem_cons_of_mem _ hm, fun j hj => by
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hxm
          · exact hle j hj⟩
      · exact ⟨x, List.mem_cons_self .., fun j hj => by
          rcases List.mem_cons.mp hj with rfl | hj
          · exact Nat.le_refl _
          · have := hle j hj; omega⟩

/-! ## An allow means the limit's leaf held -/

/-- Where a one-rule temporal permit allows, the event is of its action and its leaf holds under
some completion of the reading. -/
theorem leafHolds_of_allow {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace} {m : Nat}
    {a : EntityUID} {φ : Formula} {S : EventSchema} {acts : List ActionDecl}
    (h : ((onePolicy a φ S acts).authorize ι ω σ m).decision? = some .allow) :
    ∃ ι₀, ι₀.Completes ι ∧ (onePolicy a φ S acts).LeafHolds ι₀ σ m φ := by
  obtain ⟨p, pr, rs, r, hσ, _, hr, hdec⟩ := decideWith_decision?_allow h
  obtain ⟨ι₀, h₀⟩ := exists_completes ι
  have hr₀ := supervaluate_eq_some_iff.mp hr ι₀ h₀
  rw [← hr₀, response_temporalPermit] at hdec
  refine ⟨ι₀, h₀, ?_⟩
  by_contra hno
  simp [PolicySet.leaves, hno] at hdec

/-! ## Counting requests -/

/-- **A request limit admits fewer than `n` of a caller's requests in any interval of length
`w`**: on every trace whose timestamps never decrease, under every admissible reading. The bound
is `n − 1`: the request being decided counts itself. Denied requests count too. -/
theorem allowed_requests_lt {ι : ImplChoices} (hι : ι.Admissible) {ω : Provider.Providers}
    {σ : Trace} (hσ : σ.Nondecreasing) {w : Window} {n : Int64} {u : EntityUID} {t₀ : Int}
    {J : List Nat} (hJ : J.Nodup) (hne : J ≠ [])
    (hall : ∀ j ∈ J, ((requestLimit w n).authorize ι ω σ j).decision? = some .allow ∧
      ∃ p, σ[j]? = some p ∧ ByCaller u "request" p ∧ p.event.principal = some u ∧
        t₀ ≤ p.ts ∧ p.ts ≤ t₀ + w.ticks .seconds) :
    (J.length : Int) < n.toInt := by
  obtain ⟨m, hm, hmax⟩ := exists_max hne
  obtain ⟨hallow, pm, hpm, -, hu, -, hm₂⟩ := hall m hm
  obtain ⟨ι₀, hc, hleaf⟩ := leafHolds_of_allow hallow
  obtain ⟨pm', hpm', hsat⟩ := hleaf
  rw [hpm] at hpm'
  cases hpm'
  change Sat ι₀ .seconds σ pm.event (schema.Visible σ pm.event) Valuation.empty m
    ((limit w n "request").injectPins schema) at hsat
  rw [limit_injected (.inl rfl)] at hsat
  have := sat_count_lt_rows (hc.admissible hι) hsat (J.map fun j => [tpValue j])
    (by rw [List.Nodup, List.pairwise_map]; exact hJ.imp fun hne heq => hne (by
      simpa [tpValue] using heq)) (fun row hrow => ?_)
  · simpa using this
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨-, pj, hpj, hbj, -, hj₁, -⟩ := hall j hj
  refine ⟨rfl, j, hmax j hj, visible_of_byCaller hu (.inl rfl) hpj hbj,
    ⟨pm, pj, hpm, hpj, ?_, ?_⟩, ?_, ?_⟩
  · have := ts_le_of_le hσ (hmax j hj) hpj hpm; omega
  · omega
  · exact (sat_pinnedPred hu "request" _ j).mpr ⟨pj, hpj, hbj⟩
  · simp only [Sat, domainNames]
    rfl

/-! ## Counting responses

Two assumptions about the service that logs responses, for one caller `u`, with `answers r` the
request that the response at `r` answers. Neither is part of the semantics, which links no response
to a request. -/

section

variable (P : PolicySet) (ι : ImplChoices) (ω : Provider.Providers) (σ : Trace) (u : EntityUID)

/-- **Responses follow allows**: each of `u`'s `Read` responses answers an earlier `Read` request
of `u`'s that was allowed, and no two answer the same request. -/
structure ResponsesFollowAllows (answers : Nat → Nat) : Prop where
  before : ∀ r p, σ[r]? = some p → ByCaller u "response" p → answers r < r
  request : ∀ r p, σ[r]? = some p → ByCaller u "response" p →
    ∃ q, σ[answers r]? = some q ∧ ByCaller u "request" q ∧ q.event.principal = some u
  allowed : ∀ r p, σ[r]? = some p → ByCaller u "response" p →
    (P.authorize ι ω σ (answers r)).decision? = some .allow
  injective : ∀ r r' p p', σ[r]? = some p → ByCaller u "response" p → σ[r']? = some p' →
    ByCaller u "response" p' → answers r = answers r' → r = r'

/-- **No race**: each of `u`'s responses is logged before `u`'s next `Read` request after the one
it answers. -/
def NoRace (answers : Nat → Nat) : Prop :=
  ∀ r p, σ[r]? = some p → ByCaller u "response" p →
    ∀ q pq, σ[q]? = some pq → ByCaller u "request" pq → answers r < q → r < q

end

/-- **A response limit admits at most `n` of a caller's responses in any interval of length
`w`**, when responses follow allows and there is no race: on every trace whose timestamps never
decrease, under every admissible reading. The response of the latest request answered in the
interval is not yet logged at that request's decision, so the bound is `n`. -/
theorem responses_le {ι : ImplChoices} (hι : ι.Admissible) {ω : Provider.Providers}
    {σ : Trace} (hσ : σ.Nondecreasing) {w : Window} {n : Int64} {u : EntityUID}
    {answers : Nat → Nat}
    (hfollow : ResponsesFollowAllows (responseLimit w n) ι ω σ u answers)
    (hrace : NoRace σ u answers) {t₀ : Int} {R : List Nat} (hR : R.Nodup) (hne : R ≠ [])
    (hall : ∀ r ∈ R, ∃ p, σ[r]? = some p ∧ ByCaller u "response" p ∧
      t₀ ≤ p.ts ∧ p.ts ≤ t₀ + w.ticks .seconds) :
    (R.length : Int) ≤ n.toInt := by
  -- The latest request answered in the interval, and its response `r₀`.
  have hne' : R.map answers ≠ [] := fun h => hne (List.map_eq_nil_iff.mp h)
  obtain ⟨q₀, hq₀, hqmax⟩ := exists_max hne'
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hq₀
  obtain ⟨p₀, hp₀, hb₀, -, hp₀₂⟩ := hall r₀ hr₀
  obtain ⟨pq, hpq, hbq, hu⟩ := hfollow.request r₀ p₀ hp₀ hb₀
  have hallow := hfollow.allowed r₀ p₀ hp₀ hb₀
  have hqts : pq.ts ≤ p₀.ts := ts_le_of_le hσ (Nat.le_of_lt (hfollow.before r₀ p₀ hp₀ hb₀)) hpq hp₀
  obtain ⟨ι₀, hc, hleaf⟩ := leafHolds_of_allow hallow
  obtain ⟨pq', hpq', hsat⟩ := hleaf
  rw [hpq] at hpq'
  cases hpq'
  change Sat ι₀ .seconds σ pq.event (schema.Visible σ pq.event) Valuation.empty (answers r₀)
    ((limit w n "response").injectPins schema) at hsat
  rw [limit_injected (.inr rfl)] at hsat
  -- Every other response in the interval is logged before that request, within `w` of it.
  have hlt := sat_count_lt_rows (hc.admissible hι) hsat ((R.erase r₀).map fun r => [tpValue r])
    (by rw [List.Nodup, List.pairwise_map]; exact (hR.erase r₀).imp fun hne heq => hne (by
      simpa [tpValue] using heq)) (fun row hrow => ?_)
  · rw [List.length_map, List.length_erase_of_mem hr₀] at hlt
    have := List.length_pos_of_mem hr₀
    omega
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
  have hrR : r ∈ R := List.mem_of_mem_erase hr
  have hrne : r ≠ r₀ := fun h => by subst h; exact (hR.not_mem_erase) hr
  obtain ⟨p, hp, hb, hp₁, -⟩ := hall r hrR
  have hans : answers r < answers r₀ := by
    rcases Nat.lt_or_eq_of_le (hqmax _ (List.mem_map_of_mem hrR)) with h | h
    · exact h
    · exact absurd (hfollow.injective r r₀ p p₀ hp hb hp₀ hb₀ h) hrne
  have hrq : r < answers r₀ := hrace r p hp hb _ pq hpq hbq hans
  refine ⟨rfl, r, Nat.le_of_lt hrq, visible_of_byCaller hu (.inr rfl) hp hb,
    ⟨pq, p, hpq, hp, ?_, ?_⟩, ?_, ?_⟩
  · have := ts_le_of_le hσ (Nat.le_of_lt hrq) hp hpq; omega
  · omega
  · exact (sat_pinnedPred hu "response" _ r).mpr ⟨p, hp, hb⟩
  · simp only [Sat, domainNames]
    rfl

/-! ## The race

A cap of one response an hour. Alice requests at `@1` and `@2`, and the two responses are logged
at `@3` and `@4`. At each request no response is logged yet, so both are allowed; the hour from
`@1` then holds two responses. Responses follow allows, but the response to `@1` comes after the
request at `@2`: there is a race. -/

def alice : EntityUID := oauthUser "alice"

def ev (kind requestId : String) : Event :=
  logEvent alice read kind requestId [("doc", .prim (.string "d"))]

def raceTrace : Trace :=
  [⟨1, ev "request" "q1"⟩, ⟨2, ev "request" "q2"⟩, ⟨3, ev "response" "q1"⟩,
   ⟨4, ev "response" "q2"⟩]

def hour : Window := ⟨1, .hours⟩

def cap : PolicySet := responseLimit hour 1

/-- The response at `@3` answers the request at `@1`, the one at `@4` the request at `@2`. -/
def raceAnswers (r : Nat) : Nat := r - 2

/-- The cap, and a request limit of three an hour, are valid policy sets. -/
theorem cap_valid : cap.Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem requestLimit_valid : (requestLimit hour 3).Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem raceTrace_nondecreasing : raceTrace.Nondecreasing := by
  simp [Trace.Nondecreasing, raceTrace]

/-- Where no response is logged up to `j`, the cap's leaf holds: the count is `0 < 1`. -/
theorem cap_leaf {ι : ImplChoices} (hι : ι.Admissible) {j : Nat} {p : TimePoint}
    (hp : raceTrace[j]? = some p) (hu : p.event.principal = some alice)
    (hno : ∀ k ≤ j, ∀ pk, raceTrace[k]? = some pk → pk.event.kind ≠ "response") :
    cap.LeafHolds ι raceTrace j (limit hour 1 "response") := by
  refine ⟨p, hp, ?_⟩
  change Sat ι .seconds raceTrace p.event (schema.Visible raceTrace p.event) Valuation.empty j
    ((limit hour 1 "response").injectPins schema)
  rw [limit_injected (.inr rfl),
    sat_agg_cmp_down_iff hι (fun _ h => by obtain ⟨_, _, _, rfl⟩ := h; exact Int.natCast_nonneg _)
      (.inl rfl)]
  refine ⟨0, ⟨[], List.nodup_nil, fun row => ?_, rfl⟩, by simp only [CmpOp.Holds]; decide⟩
  simp only [List.not_mem_nil, false_iff, not_and]
  intro _ hs
  obtain ⟨k, hk, -, -, hpred, -⟩ := hs
  obtain ⟨pk, hpk, -, hkind, -⟩ := (sat_pinnedPred hu "response" _ k).mp hpred
  exact hno k hk pk hpk hkind

theorem cap_allows_at {ι : ImplChoices} (hι : ι.Admissible) (ω : Provider.Providers) {j : Nat}
    (hj : j = 0 ∨ j = 1) : (cap.authorize ι ω raceTrace j).decision? = some .allow := by
  have hno : ∀ k ≤ j, ∀ pk, raceTrace[k]? = some pk → pk.event.kind ≠ "response" := by
    intro k hk pk hpk
    rcases hj with rfl | rfl <;>
    · rcases Nat.lt_or_eq_of_le hk with h | rfl
      · obtain rfl : k = 0 := by omega
        simp [raceTrace] at hpk; subst hpk; decide
      · simp [raceTrace] at hpk; subst hpk; decide
  rcases hj with rfl | rfl
  · refine (decision_temporalPermit (b := true) rfl
      (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel))
      fun ι' hc => ⟨fun _ => rfl, fun _ => cap_leaf (hc.admissible hι) rfl rfl hno⟩).trans ?_
    decide
  · refine (decision_temporalPermit (b := true) rfl
      (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel))
      fun ι' hc => ⟨fun _ => rfl, fun _ => cap_leaf (hc.admissible hι) rfl rfl hno⟩).trans ?_
    decide

/-- On the race trace, a timepoint holding one of alice's `Read` responses is `@3` or `@4`. -/
theorem raceTrace_response {r : Nat} {p : TimePoint} (hp : raceTrace[r]? = some p)
    (hb : ByCaller alice "response" p) : r = 2 ∨ r = 3 := by
  obtain ⟨-, hk, -⟩ := hb
  rcases r with _ | _ | _ | _ | r
  · simp [raceTrace] at hp; subst hp; simp [ev, logEvent] at hk
  · simp [raceTrace] at hp; subst hp; simp [ev, logEvent] at hk
  · exact .inl rfl
  · exact .inr rfl
  · simp [raceTrace] at hp

/-- **Without `NoRace`, a response limit can be exceeded**: on the race trace, under every
admissible reading, responses follow allows, the cap of one response an hour admits two in the
hour from `@1`, and there is a race. -/
theorem race_exceeds {ι : ImplChoices} (hι : ι.Admissible) (ω : Provider.Providers) :
    ResponsesFollowAllows cap ι ω raceTrace alice raceAnswers ∧
      ¬ NoRace raceTrace alice raceAnswers ∧
      (∀ r ∈ [2, 3], ∃ p, raceTrace[r]? = some p ∧ ByCaller alice "response" p ∧
        1 ≤ p.ts ∧ p.ts ≤ 1 + hour.ticks .seconds) ∧
      (([2, 3] : List Nat).length : Int) > (1 : Int64).toInt := by
  refine ⟨⟨fun r p hp hb => ?_, fun r p hp hb => ?_, fun r p hp hb => ?_,
    fun r r' p p' hp hb hp' hb' h => ?_⟩, fun h => ?_, fun r hr => ?_, by decide⟩
  · rcases raceTrace_response hp hb with rfl | rfl <;> decide
  · rcases raceTrace_response hp hb with rfl | rfl
    · exact ⟨_, rfl, ⟨rfl, rfl, by decide⟩, rfl⟩
    · exact ⟨_, rfl, ⟨rfl, rfl, by decide⟩, rfl⟩
  · rcases raceTrace_response hp hb with rfl | rfl
    · exact cap_allows_at hι ω (.inl rfl)
    · exact cap_allows_at hι ω (.inr rfl)
  · rcases raceTrace_response hp hb with rfl | rfl <;>
      rcases raceTrace_response hp' hb' with rfl | rfl <;> simp_all [raceAnswers]
  · have := h 2 _ rfl ⟨rfl, rfl, by decide⟩ 1 _ rfl ⟨rfl, rfl, by decide⟩ (by decide)
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, rfl, ⟨rfl, rfl, by decide⟩, by decide, by decide⟩
    · exact ⟨_, rfl, ⟨rfl, rfl, by decide⟩, by decide, by decide⟩

end Dogwood.Examples.RateLimit
