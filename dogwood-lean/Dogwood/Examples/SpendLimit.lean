import Dogwood.Examples.RateLimit

/-!
# Worked example: spending limits

A per-caller spending limit, built on the windowed sum of the examples
(`refund_budget_settled_plus_current`, `temporal_sum_formerly_transfer`):

```text
permit (principal, action == Drupe::Action::"Refund", resource)
when temporal {
    (sum a for (a: Long), (t: Timepoint). where (
        formerly within W (Drupe::Action::"Refund"::request{ input.amount: a } && tp(t))
    )) <= B
};
```

under the default (pinned) event schema, so the sum is of the caller's own requests. As in
`Dogwood.Examples.RateLimit`, the guarantee is over every trace.

* **The limit holds** (`allowed_spend_le`): on every trace whose timestamps never decrease, under
  every admissible reading, the amounts of a caller's allowed `Refund` requests in any interval of
  length `W` sum to at most `B`. The request being decided is in the trace, so its own amount
  counts against the budget it is checked against, and denied requests count too.
* **Two hypotheses are assumed**, stated here and nowhere in the semantics:
  - **amounts are not negative** (`NonnegAmounts`): a negative request lowers the window's sum,
    so it lets more through. `negative_exceeds` shows it: after a request for `−100`, two
    requests for `90` are both allowed under a budget of `100`;
  - **the budget is below `Int64.MAX`**: an out-of-range sum is read as `Int64.MAX` or above
    (`ImplChoices.Admissible`), and `≤ Int64.MAX` could let it through. A count has no such
    caveat (`Dogwood.Examples.RateLimit`), since its limit is a strict `<`.

* **Summing only nonnegative amounts removes the first hypothesis** (`allowed_spend_le_filtered`):
  with `&& a >= 0` in the sum's body, the bound holds whatever the amounts. A Cedar check on the
  request being decided would not do: denied requests are logged, and the sum ranges over them.

The budgets are valid policy sets (`cap_valid`, `filteredSpendLimit_valid`).
-/

namespace Dogwood.Examples.SpendLimit

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Dogwood.Examples.RateLimit (exists_max ts_le_of_le leafHolds_of_allow)
open Cedar.Spec (EntityUID Value)

def refund : EntityUID := action "Refund"

def actions : List ActionDecl := [(refund, [("amount", .int)])]

def schema : EventSchema := defaultSchema true actions

def domain : List Binder := [⟨"a", .named ["Long"]⟩, ⟨"t", .timepoint⟩]

def spentPred : Formula := .pred refund "request" [(["input", "amount"], .var "a")]

/-- `sum a for (a: Long), (t: Timepoint). where (formerly within w (Refund::request{ input.amount:
a } && tp(t)))` -/
def spent (w : Window) : Aggregate := .sum "a" domain (.formerly w (.and spentPred (.tp "t")))

def budget (w : Window) (b : Int64) : Formula := .cmp .le (.agg (spent w)) (.long b)

def spendLimit (w : Window) (b : Int64) : PolicySet := onePolicy refund (budget w b) schema actions

/-! ## After pin injection -/

def pinnedPred : Formula :=
  .pred refund "request"
    [(["input", "amount"], .var "a"), (["callerPrincipal"], .scope .principal [])]

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

theorem budget_injected {w : Window} {b : Int64} :
    (budget w b).injectPins schema =
      .cmp .le (.agg (.sum "a" domain (.formerly w (.and pinnedPred (.tp "t"))))) (.long b) := by
  have h : schema.pinsOf refund "request" = [callerPin] := by decide
  simp [budget, spent, spentPred, pinnedPred, Formula.injectPins, Term.injectPins,
    Aggregate.injectPins, h, callerPin, PinRef.toTerm]

/-! ## A caller's requests -/

/-- The timepoint `p` is a `Refund` request that logs `u` as its caller. -/
def ByCaller (u : EntityUID) (p : TimePoint) : Prop :=
  p.event.action = refund ∧ p.event.kind = "request" ∧
    recordPath? p.event.logged ["callerPrincipal"] = some (.prim (.entityUID u))

/-- The amount a timepoint's event logs, or `0` when it logs no `Long` amount. -/
def amountAt (σ : Trace) (k : Nat) : Int :=
  match (σ[k]?.bind fun p => recordPath? p.event.logged ["input", "amount"]) with
  | some (.prim (.int i)) => i.toInt
  | _ => 0

/-- **Amounts are not negative**: none of `u`'s `Refund` requests logs a negative amount. -/
def NonnegAmounts (σ : Trace) (u : EntityUID) : Prop :=
  ∀ (k : Nat) (p : TimePoint), σ[k]? = some p → ByCaller u p → ∀ i : Int64,
    recordPath? p.event.logged ["input", "amount"] = some (.prim (.int i)) → 0 ≤ i.toInt

section

variable {ι : ImplChoices} {σ : Trace} {e : Event} {vis : Nat → Prop}

theorem sat_pinnedPred {u : EntityUID} (he : e.principal = some u) (v : Valuation) (k : Nat) :
    Sat ι .seconds σ e vis v k pinnedPred ↔
      ∃ p, σ[k]? = some p ∧ ByCaller u p ∧ ∃ w,
        recordPath? p.event.logged ["input", "amount"] = some w ∧ v "a" = some (.val w) := by
  simp only [Sat, pinnedPred, ArgsMatch, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  simp only [Term.Matches, Term.eval?, Event.scopePath?, Event.scope, he, Option.map_some,
    Option.some.injEq, TVal.val.injEq, ByCaller]
  constructor
  · rintro ⟨p, hp, ha, hk, ⟨w, hw, hv⟩, ⟨w', hw', rfl⟩⟩
    exact ⟨p, hp, ⟨ha, hk, hw'⟩, w, hw, hv⟩
  · rintro ⟨p, hp, ⟨ha, hk, hpin⟩, w, hw, hv⟩
    exact ⟨p, hp, ha, hk, ⟨w, hw, hv⟩, ⟨_, hpin, rfl⟩⟩

theorem visible_of_byCaller {u : EntityUID} (he : e.principal = some u) {k : Nat}
    {p : TimePoint} (hp : σ[k]? = some p) (hb : ByCaller u p) : schema.Visible σ e k := by
  obtain ⟨ha, hkind, hpin⟩ := hb
  refine Or.inr ⟨p, hp, ⟨⟨refund, "request", true, [callerPin], actionFields [("amount", .int)]⟩,
    List.mem_cons_self .., ha.symm, hkind.symm⟩, ?_⟩
  rw [universalPins_schema]
  intro pin hpin'
  simp only [List.mem_singleton] at hpin'
  subst hpin'
  exact ⟨_, hpin, by simp [callerPin, PinRef.toTerm, Term.eval?, Event.scopePath?, Event.scope,
    he]⟩

end

/-! ## Sums over part of the rows -/

private theorem sum_perm {l₁ l₂ : List Int} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => simp
  | cons _ _ ih => simp [ih]
  | swap => simp; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem sum_le_of_sublist {l₁ l₂ : List Int} (h : l₁.Sublist l₂) (hnn : ∀ x ∈ l₂, 0 ≤ x) :
    l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => simp
  | cons a _ ih =>
    simp only [List.sum_cons]
    have := hnn a (by simp)
    have := ih fun x hx => hnn x (by simp [hx])
    omega
  | cons_cons a _ ih =>
    simp only [List.sum_cons]
    have := ih fun x hx => hnn x (by simp [hx])
    omega

/-- **`sum … ≤ c` bounds the summands of every list of distinct rows of its body**, when every
row of the body has a nonnegative summand and `c` is below `Int64.MAX`. -/
theorem sat_sum_le_rows {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event}
    {vis : Nat → Prop} (hadm : ι.Admissible) {v : Valuation} {j : Nat} {s : VarName}
    {dom : List Binder} {body : Formula} {c : Int64} (hc : c.toInt < Int64.MAX)
    (h : Sat ι rate σ e vis v j (.cmp .le (.agg (.sum s dom body)) (.long c)))
    (hnn : ∀ row : List TVal, row.length = (domainNames dom).length →
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body →
      0 ≤ summand s (domainNames dom) row)
    (L : List (List TVal)) (hL : L.Nodup)
    (hs : ∀ row ∈ L, row.length = (domainNames dom).length ∧
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body) :
    (L.map (summand s (domainNames dom))).sum ≤ c.toInt := by
  rw [sat_agg_cmp_down_iff hadm (fun _ hT => sum_nonneg hnn hT) (.inr ⟨rfl, hc⟩)] at h
  obtain ⟨n, ⟨rows, -, hm, rfl⟩, hh⟩ := h
  simp only [CmpOp.Holds] at hh
  have hsub : L ⊆ rows := fun r hr => (hm r).mpr (hs r hr)
  obtain ⟨l, hperm, hsl⟩ := List.subperm_of_subset hL hsub
  have h₁ := sum_perm (hperm.map (summand s (domainNames dom)))
  have h₂ := sum_le_of_sublist (hsl.map (summand s (domainNames dom))) fun x hx => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hl, hsat⟩ := (hm r).mp hr
    exact hnn r hl hsat
  omega

/-! ## The limit holds -/

/-- The row of the request at `j`: its logged amount and its timepoint. -/
def rowAt (σ : Trace) (j : Nat) : List TVal :=
  [.val ((σ[j]?.bind fun p => recordPath? p.event.logged ["input", "amount"]).getD default),
    tpValue j]

theorem bindAll_a (ra rt : TVal) : (Valuation.empty.bindAll ["a", "t"] [ra, rt]) "a" = some ra := by
  simp [Valuation.bindAll, Valuation.bind]

theorem bindAll_t (ra rt : TVal) : (Valuation.empty.bindAll ["a", "t"] [ra, rt]) "t" = some rt := by
  simp [Valuation.bindAll, Valuation.bind]

theorem summand_pair (w : Value) (rt : TVal) :
    summand "a" ["a", "t"] [.val w, rt] =
      match w with
      | .prim (.int i) => i.toInt
      | _ => 0 := by
  simp only [summand, List.zip, List.zipWith, List.lookup, BEq.rfl]
  cases w with
  | prim pv => cases pv <;> rfl
  | _ => rfl

/-- **A spending limit keeps a caller's allowed spending within the budget in any interval of
length `w`**: on every trace whose timestamps never decrease, under every admissible reading,
when the caller's requests log no negative amount and the budget is below `Int64.MAX`. The
requests summed are the caller's allowed requests that log a `Long` amount, as a conforming
event does. -/
theorem allowed_spend_le {ι : ImplChoices} (hι : ι.Admissible) {ω : Provider.Providers}
    {σ : Trace} (hσ : σ.Nondecreasing) {w : Window} {b : Int64} (hb : b.toInt < Int64.MAX)
    {u : EntityUID} (hnn : NonnegAmounts σ u) {t₀ : Int} {J : List Nat} (hJ : J.Nodup)
    (hne : J ≠ [])
    (hall : ∀ j ∈ J, ((spendLimit w b).authorize ι ω σ j).decision? = some .allow ∧
      ∃ p, σ[j]? = some p ∧ ByCaller u p ∧ p.event.principal = some u ∧
        (∃ i : Int64, recordPath? p.event.logged ["input", "amount"] = some (.prim (.int i))) ∧
        t₀ ≤ p.ts ∧ p.ts ≤ t₀ + w.ticks .seconds) :
    (J.map (amountAt σ)).sum ≤ b.toInt := by
  obtain ⟨m, hm, hmax⟩ := exists_max hne
  obtain ⟨hallow, pm, hpm, -, hu, -, -, hm₂⟩ := hall m hm
  obtain ⟨ι₀, hc, hleaf⟩ := leafHolds_of_allow hallow
  obtain ⟨pm', hpm', hsat⟩ := hleaf
  rw [hpm] at hpm'
  cases hpm'
  change Sat ι₀ .seconds σ pm.event (schema.Visible σ pm.event) Valuation.empty m
    ((budget w b).injectPins schema) at hsat
  rw [budget_injected] at hsat
  have hdom : domainNames domain = ["a", "t"] := rfl
  have key := sat_sum_le_rows (hc.admissible hι) hb hsat (fun row hl hs => ?_)
    (J.map (rowAt σ)) ?_ (fun row hrow => ?_)
  · -- The rows' summands are the amounts.
    rw [List.map_map] at key
    have heq : J.map (summand "a" (domainNames domain) ∘ rowAt σ) = J.map (amountAt σ) := by
      refine List.map_congr_left fun j hj => ?_
      obtain ⟨-, pj, hpj, -, -, ⟨i, hi⟩, -⟩ := hall j hj
      have hbind : (σ[j]?.bind fun p => recordPath? p.event.logged ["input", "amount"]) =
          some (.prim (.int i)) := by rw [hpj]; exact hi
      simp only [Function.comp, rowAt, hdom, hbind, Option.getD_some, summand_pair, amountAt]
    rw [← heq]
    exact key
  · -- Every row of the body has a nonnegative summand.
    rw [hdom] at hl hs ⊢
    match row, hl with
    | [ra, rt], _ =>
      obtain ⟨k, -, -, -, hpred, -⟩ := hs
      obtain ⟨p, hp, hbk, wv, hwv, hva⟩ := (sat_pinnedPred hu _ k).mp hpred
      rw [bindAll_a, Option.some.injEq] at hva
      subst hva
      rw [summand_pair]
      cases wv with
      | prim pv =>
        cases pv with
        | int i => exact hnn k p hp hbk i hwv
        | _ => exact Int.le_refl 0
      | _ => exact Int.le_refl 0
  · -- The rows are distinct: their timepoints are.
    rw [List.Nodup, List.pairwise_map]
    refine hJ.imp fun hne heq => hne ?_
    simp only [rowAt, tpValue, List.cons.injEq, TVal.tp.injEq] at heq
    exact heq.2.1
  · -- Each allowed request in the interval is a row of the body at `m`.
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨-, pj, hpj, hbj, -, ⟨i, hi⟩, hj₁, -⟩ := hall j hj
    refine ⟨rfl, j, hmax j hj, visible_of_byCaller hu hpj hbj,
      ⟨pm, pj, hpm, hpj, ?_, ?_⟩, ?_, ?_⟩
    · have := ts_le_of_le hσ (hmax j hj) hpj hpm; omega
    · omega
    · rw [hdom]
      refine (sat_pinnedPred hu _ j).mpr ⟨pj, hpj, hbj, _, hi, ?_⟩
      rw [rowAt, hpj]
      simp only [Option.bind_some, hi, Option.getD_some, bindAll_a]
    · simp only [Sat, hdom, rowAt, bindAll_t]

/-! ## A negative amount lets more through

A budget of 100 an hour. Alice requests `−100` at `@1`, then `90` at `@2` and `90` at `@3`. The
window's sum is `−100`, `−10`, then `80` at the three requests, so all three are allowed; the two
requests for `90`, in the hour from `@2`, spend 180. -/

def alice : EntityUID := oauthUser "alice"

def amounts (k : Nat) : Int64 :=
  match k with
  | 0 => -100
  | 1 => 90
  | _ => 90

def req (k : Nat) : Event :=
  logEvent alice refund "request" s!"r{k}" [("amount", .prim (.int (amounts k)))]

def negTrace : Trace := [⟨1, req 0⟩, ⟨2, req 1⟩, ⟨3, req 2⟩]

def hour : Window := ⟨1, .hours⟩

def cap : PolicySet := spendLimit hour 100

theorem cap_valid : cap.Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem negTrace_get {k : Nat} (hk : k < 3) : ∃ ts, negTrace[k]? = some ⟨ts, req k⟩ ∧ 1 ≤ ts ∧
    ts ≤ 3 ∧ ts = k + 1 := by
  rcases k with _ | _ | _ | k
  · exact ⟨1, rfl, by decide, by decide, rfl⟩
  · exact ⟨2, rfl, by decide, by decide, rfl⟩
  · exact ⟨3, rfl, by decide, by decide, rfl⟩
  · omega

theorem negTrace_none {k : Nat} (hk : 3 ≤ k) : negTrace[k]? = none := by
  simp [negTrace]; omega

theorem byCaller_req {k : Nat} (hk : k < 3) (ts : Int) : ByCaller alice ⟨ts, req k⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  change recordPath? (req k).logged ["callerPrincipal"] = _
  rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · omega

theorem logged_amount {k : Nat} (hk : k < 3) :
    recordPath? (req k).logged ["input", "amount"] = some (.prim (.int (amounts k))) := by
  rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · omega

theorem principal_req (k : Nat) : (req k).principal = some alice := rfl

/-- The rows of alice's requests up to `j`: each amount with its timepoint. -/
def rowsUpTo (j : Nat) : List (List TVal) :=
  (List.range (j + 1)).map fun k => [.val (.prim (.int (amounts k))), tpValue k]

theorem sat_body_iff {ι : ImplChoices} {j : Nat} (hj : j < 3) {e : Event}
    (he : e.principal = some alice) (ra rt : TVal) :
    Sat ι .seconds negTrace e (schema.Visible negTrace e)
        (Valuation.empty.bindAll ["a", "t"] [ra, rt]) j (.formerly hour (.and pinnedPred (.tp "t")))
      ↔ [ra, rt] ∈ rowsUpTo j := by
  constructor
  · rintro ⟨k, hk, -, -, hpred, ht⟩
    obtain ⟨p, hp, -, w, hw, hva⟩ := (sat_pinnedPred he _ k).mp hpred
    have hk3 : k < 3 := by omega
    obtain ⟨ts, hts, -⟩ := negTrace_get hk3
    rw [hts] at hp
    cases hp
    rw [logged_amount hk3, Option.some.injEq] at hw
    subst hw
    rw [bindAll_a, Option.some.injEq] at hva
    simp only [Sat, bindAll_t, Option.some.injEq] at ht
    subst hva ht
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩
  · intro hrow
    obtain ⟨k, hk, hkr⟩ := List.mem_map.mp hrow
    simp only [List.mem_range] at hk
    simp only [List.cons.injEq, and_true] at hkr
    obtain ⟨rfl, rfl⟩ := hkr
    have hk3 : k < 3 := by omega
    obtain ⟨ts, hts, h₁, h₂, rfl⟩ := negTrace_get hk3
    obtain ⟨tj, htj, h₃, h₄, rfl⟩ := negTrace_get hj
    refine ⟨k, by omega, visible_of_byCaller he hts (byCaller_req hk3 _),
      ⟨_, _, htj, hts, ?_, ?_⟩, ?_, ?_⟩
    · show (0 : Int) ≤ (j : Int) + 1 - (k + 1)
      omega
    · show (j : Int) + 1 - (k + 1) ≤ 1 * 3600 * 1
      omega
    · exact (sat_pinnedPred he _ k).mpr ⟨_, hts, byCaller_req hk3 _, _, logged_amount hk3,
        bindAll_a _ _⟩
    · simp only [Sat, bindAll_t]

theorem total_at {ι : ImplChoices} {j : Nat} (hj : j < 3) {e : Event}
    (he : e.principal = some alice) :
    Total ι .seconds negTrace e (schema.Visible negTrace e) Valuation.empty j
      (.sum "a" domain (.formerly hour (.and pinnedPred (.tp "t"))))
      (((rowsUpTo j).map (summand "a" ["a", "t"])).sum) := by
  refine ⟨rowsUpTo j, ?_, fun row => ?_, rfl⟩
  · simp only [rowsUpTo]
    rw [List.Nodup, List.pairwise_map]
    refine (List.nodup_range).imp fun hne heq => hne ?_
    simp only [tpValue, List.cons.injEq, TVal.tp.injEq] at heq
    exact heq.2.1
  · show row ∈ rowsUpTo j ↔ row.length = 2 ∧ _
    match row with
    | [ra, rt] => simp only [List.length_cons, List.length_nil, true_and]; exact
        (sat_body_iff hj he ra rt).symm
    | [] => simp [rowsUpTo]
    | [_] => simp [rowsUpTo]
    | _ :: _ :: _ :: _ => simp [rowsUpTo]

theorem sums : ((rowsUpTo 0).map (summand "a" ["a", "t"])).sum = -100 ∧
    ((rowsUpTo 1).map (summand "a" ["a", "t"])).sum = -10 ∧
    ((rowsUpTo 2).map (summand "a" ["a", "t"])).sum = 80 := by decide

theorem leaf_at {ι : ImplChoices} {j : Nat} (hj : j < 3) {ts : Int}
    (hts : negTrace[j]? = some ⟨ts, req j⟩) : cap.LeafHolds ι negTrace j (budget hour 100) := by
  refine ⟨_, hts, ?_⟩
  change Sat ι .seconds negTrace (req j) (schema.Visible negTrace (req j)) Valuation.empty j
    ((budget hour 100).injectPins schema)
  rw [budget_injected, sat_cmp_agg_long]
  refine ⟨_, ((rowsUpTo j).map (summand "a" ["a", "t"])).sum, total_at hj rfl, ?_, ?_⟩
  · rcases j with _ | _ | _ | j
    · rw [sums.1]; simp [readLong, Int64.MIN, Int64.MAX]
    · rw [sums.2.1]; simp [readLong, Int64.MIN, Int64.MAX]
    · rw [sums.2.2]; simp [readLong, Int64.MIN, Int64.MAX]
    · omega
  · rcases j with _ | _ | _ | j
    · rw [sums.1]; simp only [CmpOp.Holds]; decide
    · rw [sums.2.1]; simp only [CmpOp.Holds]; decide
    · rw [sums.2.2]; simp only [CmpOp.Holds]; decide
    · omega

/-- At each of alice's three requests, the window's sum is within the budget. -/
theorem cap_allows_at {ι : ImplChoices} (ω : Provider.Providers) {j : Nat} (hj : j < 3) :
    (cap.authorize ι ω negTrace j).decision? = some .allow := by
  rcases j with _ | _ | _ | j
  · exact (decision_temporalPermit (b := true) (p := ⟨1, req 0⟩) rfl
      (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel))
      fun ι' _ => ⟨fun _ => rfl, fun _ => leaf_at hj rfl⟩).trans (by decide)
  · exact (decision_temporalPermit (b := true) (p := ⟨2, req 1⟩) rfl
      (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel))
      fun ι' _ => ⟨fun _ => rfl, fun _ => leaf_at hj rfl⟩).trans (by decide)
  · exact (decision_temporalPermit (b := true) (p := ⟨3, req 2⟩) rfl
      (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel))
      fun ι' _ => ⟨fun _ => rfl, fun _ => leaf_at hj rfl⟩).trans (by decide)
  · omega

/-- **A negative amount lets the limit be exceeded**: on the trace above, under every reading,
the two requests for `90`, both allowed and in the hour from `@2`, spend 180 under a budget of
100, and alice's requests do not all log a nonnegative amount. -/
theorem negative_exceeds {ι : ImplChoices} (ω : Provider.Providers) :
    (∀ j ∈ [1, 2], (cap.authorize ι ω negTrace j).decision? = some .allow ∧
      ∃ p, negTrace[j]? = some p ∧ ByCaller alice p ∧ p.event.principal = some alice ∧
        2 ≤ p.ts ∧ p.ts ≤ 2 + hour.ticks .seconds) ∧
      (([1, 2] : List Nat).map (amountAt negTrace)).sum = 180 ∧
      ¬ NonnegAmounts negTrace alice := by
  refine ⟨fun j hj => ?_, by decide, fun h => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    have hj3 : j < 3 := by omega
    obtain ⟨ts, hts, h₁, h₂, hts'⟩ := negTrace_get hj3
    refine ⟨cap_allows_at ω hj3, _, hts, byCaller_req hj3 _, rfl, ?_, ?_⟩
    · show 2 ≤ ts
      omega
    · show ts ≤ 2 + 1 * 3600 * 1
      omega
  · have := h 0 _ rfl (byCaller_req (by decide) _) _ (logged_amount (by decide))
    exact absurd this (by decide)

/-! ## Excluding negative amounts in the sum

A check on the request being decided, `when { context.input.amount >= 0 }`, does not remove the
need for `NonnegAmounts`: it denies a negative request, but the request is still logged, and the
sum ranges over the logged requests, denied ones included. On the trace of `negative_exceeds`,
such a check would deny the request for `−100` and still let both requests for `90` through (not
formalized here). Excluding negative amounts from the sum itself does:

```text
(sum a for (a: Long), (t: Timepoint). where (
    formerly within W (Drupe::Action::"Refund"::request{ input.amount: a } && a >= 0 && tp(t))
)) <= B
```
-/

/-- `a >= 0` -/
def nonnegA : Formula := .cmp .ge (.var "a") (.long 0)

def filteredSpent (w : Window) : Aggregate :=
  .sum "a" domain (.formerly w (.and (.and spentPred nonnegA) (.tp "t")))

def filteredBudget (w : Window) (b : Int64) : Formula :=
  .cmp .le (.agg (filteredSpent w)) (.long b)

def filteredSpendLimit (w : Window) (b : Int64) : PolicySet :=
  onePolicy refund (filteredBudget w b) schema actions

theorem filteredSpendLimit_valid : (filteredSpendLimit hour 100).Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem filteredBudget_injected {w : Window} {b : Int64} :
    (filteredBudget w b).injectPins schema =
      .cmp .le (.agg (.sum "a" domain
        (.formerly w (.and (.and pinnedPred nonnegA) (.tp "t"))))) (.long b) := by
  have h : schema.pinsOf refund "request" = [callerPin] := by decide
  simp [filteredBudget, filteredSpent, spentPred, pinnedPred, nonnegA, Formula.injectPins,
    Term.injectPins, Aggregate.injectPins, h, callerPin, PinRef.toTerm]

theorem sat_nonnegA_iff {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event}
    {vis : Nat → Prop} {v : Valuation} {k : Nat} :
    Sat ι rate σ e vis v k nonnegA ↔
      ∃ i : Int64, v "a" = some (.val (.prim (.int i))) ∧ 0 ≤ i.toInt := by
  simp only [Sat, nonnegA, Denotes, Term.eval?, Option.some.injEq]
  constructor
  · rintro ⟨x, y, ⟨w, hw, rfl⟩, ⟨_, rfl, rfl⟩, hh⟩
    cases w with
    | tp k => simp [CVal.ofTVal, CmpOp.Holds] at hh
    | val v' =>
      cases v' with
      | prim pv =>
        cases pv with
        | int i =>
          refine ⟨i, hw, ?_⟩
          simpa [CVal.ofTVal, CVal.ofValue, CmpOp.Holds] using hh
        | _ => simp [CVal.ofTVal, CVal.ofValue, CmpOp.Holds] at hh
      | _ => simp [CVal.ofTVal, CVal.ofValue, CmpOp.Holds] at hh
  · rintro ⟨i, hv, hi⟩
    exact ⟨_, _, ⟨_, hv, rfl⟩, ⟨_, rfl, rfl⟩, by
      simpa [CVal.ofTVal, CVal.ofValue, CmpOp.Holds] using hi⟩

private theorem sum_le_sum_filter_nonneg (f : Nat → Int) :
    (J : List Nat) → (J.map f).sum ≤ ((J.filter fun j => decide (0 ≤ f j)).map f).sum
  | [] => by simp
  | j :: J => by
    have ih := sum_le_sum_filter_nonneg f J
    by_cases h : 0 ≤ f j
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, decide_eq_true h, ↓reduceIte]
      omega
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, decide_eq_false h,
        Bool.false_eq_true, ↓reduceIte]
      omega

/-- **A spending limit that sums only nonnegative amounts keeps a caller's allowed spending
within the budget in any interval of length `w`**, with no hypothesis on the amounts: on every
trace whose timestamps never decrease, under every admissible reading, when the budget is below
`Int64.MAX`. An allowed request with a negative amount only lowers the spending. -/
theorem allowed_spend_le_filtered {ι : ImplChoices} (hι : ι.Admissible)
    {ω : Provider.Providers} {σ : Trace} (hσ : σ.Nondecreasing) {w : Window} {b : Int64}
    (hb : b.toInt < Int64.MAX) {u : EntityUID} {t₀ : Int} {J : List Nat} (hJ : J.Nodup)
    (hne : J ≠ [])
    (hall : ∀ j ∈ J, ((filteredSpendLimit w b).authorize ι ω σ j).decision? = some .allow ∧
      ∃ p, σ[j]? = some p ∧ ByCaller u p ∧ p.event.principal = some u ∧
        (∃ i : Int64, recordPath? p.event.logged ["input", "amount"] = some (.prim (.int i))) ∧
        t₀ ≤ p.ts ∧ p.ts ≤ t₀ + w.ticks .seconds) :
    (J.map (amountAt σ)).sum ≤ b.toInt := by
  obtain ⟨m, hm, hmax⟩ := exists_max hne
  obtain ⟨hallow, pm, hpm, -, hu, -, -, hm₂⟩ := hall m hm
  obtain ⟨ι₀, hc, hleaf⟩ := leafHolds_of_allow hallow
  obtain ⟨pm', hpm', hsat⟩ := hleaf
  rw [hpm] at hpm'
  cases hpm'
  change Sat ι₀ .seconds σ pm.event (schema.Visible σ pm.event) Valuation.empty m
    ((filteredBudget w b).injectPins schema) at hsat
  rw [filteredBudget_injected] at hsat
  have hdom : domainNames domain = ["a", "t"] := rfl
  let J' := J.filter fun j => decide (0 ≤ amountAt σ j)
  have hJ'sub : ∀ j ∈ J', j ∈ J ∧ 0 ≤ amountAt σ j := fun j hj => by
    simpa [J'] using hj
  have key := sat_sum_le_rows (hc.admissible hι) hb hsat (fun row hl hs => ?_)
    (J'.map (rowAt σ)) ?_ (fun row hrow => ?_)
  · -- The rows' summands are the nonnegative amounts, which bound all the amounts.
    rw [List.map_map] at key
    have heq : J'.map (summand "a" (domainNames domain) ∘ rowAt σ) = J'.map (amountAt σ) := by
      refine List.map_congr_left fun j hj => ?_
      obtain ⟨-, pj, hpj, -, -, ⟨i, hi⟩, -⟩ := hall j (hJ'sub j hj).1
      have hbind : (σ[j]?.bind fun p => recordPath? p.event.logged ["input", "amount"]) =
          some (.prim (.int i)) := by rw [hpj]; exact hi
      simp only [Function.comp, rowAt, hdom, hbind, Option.getD_some, summand_pair, amountAt]
    rw [heq] at key
    exact Int.le_trans (sum_le_sum_filter_nonneg _ J) key
  · -- Every row of the body has a nonnegative summand: the body says so.
    rw [hdom] at hl hs ⊢
    match row, hl with
    | [ra, rt], _ =>
      obtain ⟨k, -, -, -, ⟨-, hnn⟩, -⟩ := hs
      obtain ⟨i, hi, hi₀⟩ := sat_nonnegA_iff.mp hnn
      rw [bindAll_a, Option.some.injEq] at hi
      subst hi
      rw [summand_pair]
      exact hi₀
  · -- The rows are distinct: their timepoints are.
    rw [List.Nodup, List.pairwise_map]
    refine (hJ.sublist List.filter_sublist).imp fun hne heq => hne ?_
    simp only [rowAt, tpValue, List.cons.injEq, TVal.tp.injEq] at heq
    exact heq.2.1
  · -- Each allowed nonnegative request in the interval is a row of the body at `m`.
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨hjJ, hj₀⟩ := hJ'sub j hj
    obtain ⟨-, pj, hpj, hbj, -, ⟨i, hi⟩, hj₁, -⟩ := hall j hjJ
    have hamt : amountAt σ j = i.toInt := by
      simp only [amountAt, hpj, Option.bind_some, hi]
    refine ⟨rfl, j, hmax j hjJ, visible_of_byCaller hu hpj hbj,
      ⟨pm, pj, hpm, hpj, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · have := ts_le_of_le hσ (hmax j hjJ) hpj hpm; omega
    · omega
    · rw [hdom]
      refine (sat_pinnedPred hu _ j).mpr ⟨pj, hpj, hbj, _, hi, ?_⟩
      rw [rowAt, hpj]
      simp only [Option.bind_some, hi, Option.getD_some, bindAll_a]
    · rw [hdom]
      refine sat_nonnegA_iff.mpr ⟨i, ?_, hamt ▸ hj₀⟩
      rw [rowAt, hpj]
      simp only [Option.bind_some, hi, Option.getD_some, bindAll_a]
    · simp only [Sat, hdom, rowAt, bindAll_t]

end Dogwood.Examples.SpendLimit
