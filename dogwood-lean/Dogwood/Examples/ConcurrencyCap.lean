import Dogwood.Examples.Callers
import Dogwood.Examples.RateLimit

/-!
# Worked example: a cap on open pull requests

The concurrency-cap example (`cap_open_agent_prs_windowed`), with the caller pin:

```text
permit (principal, action == Repo::Action::"OpenPullRequest", resource)
when temporal {
    (count for (t: Timepoint). where (
        formerly within 24h (Repo::Action::"OpenPullRequest"::response{} && tp(t))))
    - (count for (t: Timepoint). where (
        formerly within 24h (Repo::Action::"CompleteReview"::response{} && tp(t)))) < 3
};
```

under the default (pinned) event schema. Its comment reads it as "a coding agent may hold at most
3 open pull requests at once", measured as opens minus completed reviews in the 24h window.

* **What an allow means** (`allowed_open_counts`): at an allowed open, the caller's opens in the
  window outnumber the caller's reviews in it by less than 3, counted exactly (`windowCount`), on
  every trace, under every reading, provided the counts are within the `Long` range. Even an
  admissible reading may read a count beyond it as any integer from `Int64.MAX` up
  (`ImplChoices.Admissible`), and two such counts can subtract to `0`, hiding any difference, so
  the result keeps the proviso. A trace of fewer than 2⁶³ events meets it
  (`allowed_open_counts_of_length`).
* **The window is not the PRs open** (`six_open`): the cap bounds opens minus reviews *in the
  window*, not the pull requests open. On a trace where a caller opens three pull requests, waits
  a day, and opens three more, without a review, all six opens are allowed, though six pull
  requests are open. Each response answers an allowed request, and is logged before the next one,
  so the service assumptions of `Dogwood.Examples.RateLimit` hold: the gap is the policy's.
-/

namespace Dogwood.Examples.ConcurrencyCap

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Dogwood.Examples.RateLimit (leafHolds_of_allow)
open Cedar.Spec (EntityUID Value)

/-! ## Exact counts of a caller's events in a window -/

/-- Whether the event at `k` is `u`'s, of action `a` and kind `kind`, within `w` before `j`. -/
def inWindowB (σ : Trace) (u a : EntityUID) (kind : String) (w : Window) (j k : Nat) : Bool :=
  match σ[j]?, σ[k]? with
  | some pj, some pk =>
    pk.event.action == a && pk.event.kind == kind &&
      recordPath? pk.event.logged ["callerPrincipal"] == some (.prim (.entityUID u)) &&
      decide (0 ≤ pj.ts - pk.ts) && decide (pj.ts - pk.ts ≤ w.ticks .seconds)
  | _, _ => false

/-- The number of `u`'s events of action `a` and kind `kind` within `w` before `j`. -/
def windowCount (σ : Trace) (u a : EntityUID) (kind : String) (w : Window) (j : Nat) : Nat :=
  ((List.range (j + 1)).filter (inWindowB σ u a kind w j)).length

theorem inWindowB_iff {σ : Trace} {u a : EntityUID} {kind : String} {w : Window} {j k : Nat} :
    inWindowB σ u a kind w j k = true ↔
      ∃ pk, σ[k]? = some pk ∧ ByCaller u a kind pk ∧ InWindow .seconds σ j k w := by
  unfold inWindowB InWindow ByCaller
  cases hj : σ[j]? with
  | none => simp
  | some pj =>
    cases hk : σ[k]? with
    | none => simp
    | some pk =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.some.injEq]
      constructor
      · rintro ⟨⟨⟨⟨ha, hkd⟩, hpin⟩, h₀⟩, h₁⟩
        exact ⟨pk, rfl, ⟨ha, hkd, hpin⟩, pj, pk, rfl, rfl, h₀, h₁⟩
      · rintro ⟨_, rfl, ⟨ha, hkd, hpin⟩, pj', pk', hpj', hpk', h₀, h₁⟩
        cases hpj'
        cases hpk'
        exact ⟨⟨⟨⟨ha, hkd⟩, hpin⟩, h₀⟩, h₁⟩

/-- **The count of a pinned predicate in a window is the number of the caller's events in it.** -/
theorem total_count_eq {ι : ImplChoices} {σ : Trace} {S : EventSchema}
    (hpins : S.universalPins = [callerPin]) {u a : EntityUID} {kind : String}
    (hsig : ∃ s ∈ S, s.action = a ∧ s.kind = kind) {w : Window} {j : Nat} {e : Event}
    (he : e.principal = some u) :
    Total ι .seconds σ e (S.Visible σ e) Valuation.empty j
      (.count [⟨"t", .timepoint⟩] (.formerly w (.and (callerPred a kind) (.tp "t"))))
      (windowCount σ u a kind w j) := by
  refine ⟨((List.range (j + 1)).filter (inWindowB σ u a kind w j)).map fun k => [tpValue k],
    ?_, fun row => ?_, by simp [windowCount]⟩
  · rw [List.Nodup, List.pairwise_map]
    refine (List.nodup_range.sublist List.filter_sublist).imp fun hne heq => hne ?_
    simpa [tpValue] using heq
  · constructor
    · intro hrow
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hrow
      obtain ⟨hkr, hb⟩ := List.mem_filter.mp hk
      obtain ⟨pk, hpk, hbk, hin⟩ := inWindowB_iff.mp hb
      refine ⟨rfl, k, Nat.le_of_lt_succ (List.mem_range.mp hkr),
        visible_of_byCaller hpins hsig he hpk hbk, hin,
        (sat_callerPred he a kind _ k).mpr ⟨pk, hpk, hbk⟩, ?_⟩
      simp only [Sat, domainNames]
      rfl
    · rintro ⟨hl, k, hk, -, hin, hpred, ht⟩
      obtain ⟨pk, hpk, hbk⟩ := (sat_callerPred he a kind _ k).mp hpred
      match row, hl with
      | [r], _ =>
        have hd : domainNames [⟨"t", .timepoint⟩] = ["t"] := rfl
        have hr : r = tpValue k := by
          simp only [Sat, hd, Valuation.bindAll, Valuation.bind, ↓reduceIte,
            Option.some.injEq] at ht
          exact ht
        subst hr
        exact List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
          inWindowB_iff.mpr ⟨pk, hpk, hbk, hin⟩⟩, rfl⟩

/-! ## The policy -/

def openPR : EntityUID := action "OpenPullRequest"
def review : EntityUID := action "CompleteReview"

def actions : List ActionDecl := [(openPR, [("doc", .string)]), (review, [("doc", .string)])]

def schema : EventSchema := defaultSchema true actions

def day : Window := ⟨24, .hours⟩

def countOf (a : EntityUID) : Aggregate :=
  .count [⟨"t", .timepoint⟩] (.formerly day (.and (.pred a "response" []) (.tp "t")))

def capφ : Formula :=
  .cmp .lt (.arith .sub (.agg (countOf openPR)) (.agg (countOf review))) (.long 3)

def policySet : PolicySet := onePolicy openPR capφ schema actions

theorem policySet_valid : policySet.Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

def pinnedCount (a : EntityUID) : Aggregate :=
  .count [⟨"t", .timepoint⟩] (.formerly day (.and (callerPred a "response") (.tp "t")))

theorem capφ_injected :
    capφ.injectPins schema =
      .cmp .lt (.arith .sub (.agg (pinnedCount openPR)) (.agg (pinnedCount review))) (.long 3) := by
  have h₁ : schema.pinsOf openPR "response" = [callerPin] := by decide
  have h₂ : schema.pinsOf review "response" = [callerPin] := by decide
  simp [capφ, countOf, pinnedCount, callerPred, Formula.injectPins, Term.injectPins,
    Aggregate.injectPins, h₁, h₂, callerPin, PinRef.toTerm]

theorem sig_response {a : EntityUID} (ha : a = openPR ∨ a = review) :
    ∃ s ∈ schema, s.action = a ∧ s.kind = "response" := by
  rcases ha with rfl | rfl
  · exact sig_defaultSchema (ins := [("doc", .string)]) (by simp [actions]) (.inr (.inl rfl))
  · exact sig_defaultSchema (ins := [("doc", .string)]) (by simp [actions]) (.inr (.inl rfl))

theorem readLong_of_range {f : Int → Option Int} {n : Int} (h₁ : Int64.MIN ≤ n)
    (h₂ : n ≤ Int64.MAX) : readLong f n = some (.num n) := by
  simp [readLong, h₁, h₂]

/-! ## What an allow means -/

/-- **At an allowed open, the caller's opens in the window outnumber the caller's reviews in it
by less than 3**, counted exactly, on every trace, under every reading, when the counts are
within the `Long` range. -/
theorem allowed_open_counts {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace} {q : Nat}
    {pq : TimePoint} {u : EntityUID}
    (h : (policySet.authorize ι ω σ q).decision? = some .allow)
    (hpq : σ[q]? = some pq) (hu : pq.event.principal = some u)
    (ho : (windowCount σ u openPR "response" day q : Int) ≤ Int64.MAX)
    (hr : (windowCount σ u review "response" day q : Int) ≤ Int64.MAX) :
    (windowCount σ u openPR "response" day q : Int) - windowCount σ u review "response" day q
      < 3 := by
  obtain ⟨ι₀, -, pq', hpq', hsat⟩ := leafHolds_of_allow h
  rw [hpq] at hpq'
  cases hpq'
  change Sat ι₀ .seconds σ pq.event (schema.Visible σ pq.event) Valuation.empty q
    (capφ.injectPins schema) at hsat
  rw [capφ_injected] at hsat
  obtain ⟨x, y, ⟨m, n, ⟨t₁, ht₁, hm⟩, ⟨t₂, ht₂, hn⟩, hx⟩, ⟨_, hy, rfl⟩, hh⟩ := hsat
  simp only [Term.eval?, Option.some.injEq] at hy
  subst hy
  have e₁ := total_unique ht₁ (total_count_eq universalPins_schema (sig_response (.inl rfl)) hu)
  have e₂ := total_unique ht₂ (total_count_eq universalPins_schema (sig_response (.inr rfl)) hu)
  subst e₁ e₂
  have hmin : Int64.MIN ≤ 0 := by decide
  simp only [ImplChoices.aggregateValue] at hm hn
  rw [readLong_of_range (by omega) ho, Option.some.injEq, CVal.num.injEq] at hm
  rw [readLong_of_range (by omega) hr, Option.some.injEq, CVal.num.injEq] at hn
  subst hm hn
  simp only [ImplChoices.arithValue, ArithOp.apply] at hx
  have hmax : (0 : Int) ≤ Int64.MAX := by decide
  rw [readLong_of_range (by simp only [Int64.MIN, Int64.MAX] at *; omega) (by omega),
    Option.some.injEq] at hx
  subst hx
  simpa [CVal.ofTVal, CVal.ofValue, CmpOp.Holds] using hh

/-- A window's count is at most the number of timepoints up to its end. -/
theorem windowCount_le (σ : Trace) (u a : EntityUID) (kind : String) (w : Window) (q : Nat) :
    windowCount σ u a kind w q ≤ q + 1 := by
  unfold windowCount
  have := List.length_filter_le (inWindowB σ u a kind w q) (List.range (q + 1))
  simp only [List.length_range] at this
  exact this

/-- **The same, on a trace of fewer than 2⁶³ events**: the counts are then within the `Long`
range. (2⁶⁴ would not do: a count could reach `2⁶⁴ − 1`.) -/
theorem allowed_open_counts_of_length {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace}
    {q : Nat} {pq : TimePoint} {u : EntityUID}
    (h : (policySet.authorize ι ω σ q).decision? = some .allow)
    (hpq : σ[q]? = some pq) (hu : pq.event.principal = some u)
    (hlen : (σ.length : Int) ≤ Int64.MAX) :
    (windowCount σ u openPR "response" day q : Int) - windowCount σ u review "response" day q
      < 3 := by
  have hq : q < σ.length := (List.getElem?_eq_some_iff.mp hpq).1
  have h₁ := windowCount_le σ u openPR "response" day q
  have h₂ := windowCount_le σ u review "response" day q
  exact allowed_open_counts h hpq hu (by omega) (by omega)

/-- The cap's leaf holds wherever the window's counts are small enough, under every reading. -/
theorem leaf_of_counts {ι : ImplChoices} {σ : Trace} {q : Nat} {pq : TimePoint} {u : EntityUID}
    (hpq : σ[q]? = some pq) (hu : pq.event.principal = some u)
    (ho : (windowCount σ u openPR "response" day q : Int) ≤ Int64.MAX)
    (hr : (windowCount σ u review "response" day q : Int) ≤ Int64.MAX)
    (hlt : (windowCount σ u openPR "response" day q : Int) -
      windowCount σ u review "response" day q < 3) :
    policySet.LeafHolds ι σ q capφ := by
  refine ⟨pq, hpq, ?_⟩
  change Sat ι .seconds σ pq.event (schema.Visible σ pq.event) Valuation.empty q
    (capφ.injectPins schema)
  rw [capφ_injected]
  have hmin : Int64.MIN ≤ 0 := by decide
  refine ⟨_, _, ⟨_, _, ⟨_, total_count_eq universalPins_schema (sig_response (.inl rfl)) hu,
      readLong_of_range (by omega) ho⟩,
    ⟨_, total_count_eq universalPins_schema (sig_response (.inr rfl)) hu,
      readLong_of_range (by omega) hr⟩,
    readLong_of_range (by simp only [ArithOp.apply, Int64.MIN, Int64.MAX] at *; omega)
      (by simp only [ArithOp.apply]; omega)⟩, ⟨_, rfl, rfl⟩, ?_⟩
  simpa [ArithOp.apply, CVal.ofTVal, CVal.ofValue, CmpOp.Holds] using hlt

/-! ## The window is not the pull requests open

Alice opens three pull requests two seconds apart, waits a day, and opens three more; nothing is
reviewed. Each open's response is logged one second after its request. -/

def alice : EntityUID := oauthUser "alice"

def ev (kind requestId : String) : Event :=
  logEvent alice openPR kind requestId [("doc", .prim (.string "d"))]

def prTrace : Trace :=
  [⟨0, ev "request" "1"⟩, ⟨1, ev "response" "1"⟩, ⟨2, ev "request" "2"⟩,
   ⟨3, ev "response" "2"⟩, ⟨4, ev "request" "3"⟩, ⟨5, ev "response" "3"⟩,
   ⟨90000, ev "request" "4"⟩, ⟨90001, ev "response" "4"⟩, ⟨90002, ev "request" "5"⟩,
   ⟨90003, ev "response" "5"⟩, ⟨90004, ev "request" "6"⟩, ⟨90005, ev "response" "6"⟩]

/-- The positions of alice's six open requests. -/
def opens : List Nat := [0, 2, 4, 6, 8, 10]

theorem counts_at : ∀ q ∈ opens,
    windowCount prTrace alice openPR "response" day q < 3 ∧
      windowCount prTrace alice review "response" day q = 0 := by
  decide +kernel

theorem open_allowed {ι : ImplChoices} (ω : Provider.Providers) {q : Nat} (hq : q ∈ opens) :
    (policySet.authorize ι ω prTrace q).decision? = some .allow := by
  obtain ⟨ho, hr⟩ := counts_at q hq
  have hmax : (3 : Int) ≤ Int64.MAX := by decide
  have hleaf : ∀ {pq : TimePoint}, prTrace[q]? = some pq → pq.event.principal = some alice →
      ∀ ι', policySet.LeafHolds ι' prTrace q capφ := fun hpq hu ι' =>
    leaf_of_counts hpq hu (by omega) (by rw [hr]; decide) (by rw [hr]; omega)
  simp only [opens, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · refine (decision_temporalPermit (b := true) rfl
      (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel))
      fun ι' _ => ⟨fun _ => rfl, fun _ => hleaf rfl rfl ι'⟩).trans ?_
    decide

/-- **The cap bounds the window, not the pull requests open**: on the trace above, under every
reading, all six of alice's opens are allowed, six open responses are logged, and no review. -/
theorem six_open {ι : ImplChoices} (ω : Provider.Providers) :
    (∀ q ∈ opens, (policySet.authorize ι ω prTrace q).decision? = some .allow) ∧
      (prTrace.filter fun p => p.event.action == openPR && p.event.kind == "response").length
        = 6 ∧
      (prTrace.filter fun p => p.event.action == review).length = 0 :=
  ⟨fun _ hq => open_allowed ω hq, by decide, by decide⟩

end Dogwood.Examples.ConcurrencyCap
