import Dogwood.Examples.Common
import Dogwood.Spec.Validity

/-!
# Worked example: `refund_budget_settled_plus_current`

A compound operand over an aggregate
(`dogwood-docs/examples/refund_budget_settled_plus_current`):

```text
permit (principal, action == Drupe::Action::"Refund", resource)
when temporal {
    (sum a for (a: Long), (t: Timepoint). where (
        formerly within 24h (Drupe::Action::"Refund"::response{ output.amount: a } && tp(t))
    )) + context.input.amount <= 100
};
```

under the default (pinned) event schema. A refund request is allowed when
the refunds already settled in the last day (`response` events), plus the
amount requested now, come to at most 100.

On the bundle's trace, alice requests 60, 50, 30, 15 and 10, and the 60 and
the 30 settle. The reference interpreter allows the requests for 60, 30 and
10, and denies the others. This file derives the same outcomes from the
specification, for every reading of out-of-range results (`ι`).

The pin reaches the predicate inside the `sum`, though the `sum` is a leaf of
a compound operand, so the budget is alice's own. `outcome_isolated` shows
it on a second trace: bob's settled refund of 80 does not count against
alice, and her request for 30 is allowed. The crate's pin injection also
reaches an aggregate that is a leaf of an arithmetic operand
(`event_schema/pin.rs`, `inject_into_operand`).
-/

namespace Dogwood.Examples.RefundBudget

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Cedar.Spec (EntityUID Value Attr)
open Cedar.Data (Map)

def alice : EntityUID := oauthUser "alice"
def refund : EntityUID := action "Refund"

def input (user : String) (amount : Int64) : List (Attr × Value) :=
  [("amount", .prim (.int amount)), ("user", .prim (.string user))]

/-- A refund request: a decision event. -/
def request (user : String) (amount : Int64) (requestId : String) : Event :=
  logEvent (oauthUser user) refund "request" requestId (input user amount)

/-- A settled refund: a `response` event, which logs the refund's `output`
and carries no request context. -/
def response (user : String) (amount : Int64) (requestId : String) : Event where
  action := refund
  kind := "response"
  principal := some (oauthUser user)
  resource := some gw1
  logged := Map.make [
    ("input", .record (Map.make (input user amount))),
    ("output", .record (Map.make [("amount", .prim (.int amount))])),
    ("callerPrincipal", .prim (.entityUID (oauthUser user))),
    ("callerResource", .prim (.entityUID gw1)),
    ("requestId", .prim (.string requestId))]
  context := Map.empty
  entities := Map.empty

/-- The bundle's trace. -/
def history : Trace := [
  ⟨0, request "alice" 60 "r1"⟩,
  ⟨1, response "alice" 60 "r1"⟩,
  ⟨10, request "alice" 50 "r2"⟩,
  ⟨20, request "alice" 30 "r3"⟩,
  ⟨21, response "alice" 30 "r3"⟩,
  ⟨30, request "alice" 15 "r4"⟩,
  ⟨40, request "alice" 10 "r5"⟩]

/-- Bob's refund of 80 settles, then alice requests 30. -/
def shared : Trace := [
  ⟨0, request "bob" 80 "b1"⟩,
  ⟨1, response "bob" 80 "b1"⟩,
  ⟨10, request "alice" 30 "a1"⟩]

def actions : List ActionDecl := [(refund, [("amount", .int), ("user", .string)])]

/-- The event schema the crate derives for the bundle: the default schema,
whose `response` kind also declares the action's output. (The action schema
declares `output` optional, so the field is optional.) -/
def schema : EventSchema :=
  let fields := actionFields [("amount", .int), ("user", .string)]
  [⟨refund, "request", true, [callerPin], fields⟩,
   ⟨refund, "response", false, [callerPin], fields ++ [⟨["output", "amount"], .cedar .int, false⟩]⟩,
   ⟨refund, "error", false, [callerPin], fields⟩]

def settledPred : Formula := .pred refund "response" [(["output", "amount"], .var "a")]

def domain : List Binder := [⟨"a", .named ["Long"]⟩, ⟨"t", .timepoint⟩]

def window : Window := ⟨24, .hours⟩

def body : Formula := .formerly window (.and settledPred (.tp "t"))

def settled : Aggregate := .sum "a" domain body

def φ : Formula := .cmp .le (.arith .add (.agg settled) (.context ["input", "amount"])) (.long 100)

def policySet : PolicySet := onePolicy refund φ schema actions

/-! ## After pin injection -/

def pinnedPred : Formula :=
  .pred refund "response" [(["output", "amount"], .var "a"), (["callerPrincipal"], .scope .principal [])]

def pinnedSettled : Aggregate := .sum "a" domain (.formerly window (.and pinnedPred (.tp "t")))

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

/-- The pin reaches the predicate inside the `sum`, a leaf of the compound. -/
theorem φ_injected : φ.injectPins schema =
    .cmp .le (.arith .add (.agg pinnedSettled) (.context ["input", "amount"])) (.long 100) := by
  have h : schema.pinsOf refund "response" = [callerPin] := by decide
  simp [φ, settled, body, settledPred, pinnedSettled, pinnedPred, Formula.injectPins,
    Term.injectPins, Aggregate.injectPins, h, callerPin, PinRef.toTerm]

/-! ## The settled refunds a decision sees -/

/-- The amount of alice's refund that settles at `p`, if `p` is one. -/
def settledBy (p : TimePoint) : Option Value :=
  if p.event.action = refund ∧ p.event.kind = "response" ∧
      recordPath? p.event.logged ["callerPrincipal"] = some (.prim (.entityUID alice))
  then recordPath? p.event.logged ["output", "amount"] else none

/-- The rows of alice's settled refunds up to timepoint `n`: each amount with
its timepoint. -/
def rowsUpTo (σ : Trace) (n : Nat) : List (List TVal) :=
  (List.range (n + 1)).filterMap fun k =>
    (σ[k]?.bind settledBy).map fun w => [.val w, tpValue k]

/-- Their total. -/
def settledTotal (σ : Trace) (n : Nat) : Int :=
  ((rowsUpTo σ n).map (summand "a" ["a", "t"])).sum

variable (ι : ImplChoices)

/-- At a decision of alice's, the pinned predicate matches exactly alice's
settled refunds, and binds `a` to the amount. -/
theorem sat_pinnedPred (σ : Trace) (e : Event) (vis : Nat → Prop) (he : e.principal = some alice)
    (u : Valuation) (k : Nat) :
    Sat ι .seconds σ e vis u k pinnedPred ↔
      ∃ p, σ[k]? = some p ∧ ∃ w, settledBy p = some w ∧ u "a" = some (.val w) := by
  simp only [Sat, pinnedPred, ArgsMatch, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  simp only [Term.Matches, Term.eval?, Event.scopePath?, Event.scope, he, Option.map_some,
    Option.some.injEq, TVal.val.injEq]
  constructor
  · rintro ⟨p, hp, ha, hk, ⟨w, hw, hu⟩, ⟨w', hw', hpin⟩⟩
    refine ⟨p, hp, w, ?_, hu⟩
    simp only [settledBy, ha, hk, true_and]
    rw [if_pos (by rw [hw', ← hpin]), hw]
  · rintro ⟨p, hp, w, hs, hu⟩
    simp only [settledBy] at hs
    split at hs
    · next h =>
      obtain ⟨ha, hk, hpin⟩ := h
      exact ⟨p, hp, ha, hk, ⟨w, hs, hu⟩, ⟨_, hpin, rfl⟩⟩
    · cases hs

/-- Alice's settled refunds are visible to a decision of alice's: they are
hers on the universal pin. -/
theorem visible_of_settled {σ : Trace} {e : Event} (he : e.principal = some alice) {k : Nat}
    {p : TimePoint} {w : Value} (hp : σ[k]? = some p) (hs : settledBy p = some w) :
    schema.Visible σ e k := by
  simp only [settledBy] at hs
  split at hs
  · next h =>
    obtain ⟨ha, hk, hpin⟩ := h
    refine Or.inr ⟨p, hp, ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_, ?_⟩, ?_⟩
    · exact ha.symm
    · exact hk.symm
    · rw [universalPins_schema]
      intro pin hpin'
      simp only [List.mem_singleton] at hpin'
      subst hpin'
      exact ⟨_, hpin, by simp [callerPin, PinRef.toTerm, Term.eval?, Event.scopePath?, Event.scope, he]⟩
  · cases hs

/-- When every timepoint up to `n` is in the window, the `sum`'s rows are
`rowsUpTo σ n`. -/
theorem sat_body (σ : Trace) (e : Event) (he : e.principal = some alice)
    (v : Valuation) (n : Nat) (hwin : ∀ k ≤ n, InWindow .seconds σ n k window)
    (w₁ w₂ : TVal) :
    Sat ι .seconds σ e (schema.Visible σ e) (v.bindAll ["a", "t"] [w₁, w₂]) n
        (.formerly window (.and pinnedPred (.tp "t"))) ↔
      [w₁, w₂] ∈ rowsUpTo σ n := by
  simp only [Sat, sat_pinnedPred ι σ e _ he, rowsUpTo, List.mem_filterMap, List.mem_range]
  simp only [Valuation.bindAll, Valuation.bind]
  constructor
  · rintro ⟨k, hk, _, _, ⟨p, hp, w, hs, hw⟩, ht⟩
    simp only [if_true, Option.some.injEq] at hw ht
    simp only [show ("a" = "t") = False from by decide, if_false, Option.some.injEq] at hw
    refine ⟨k, Nat.lt_succ_of_le hk, ?_⟩
    rw [hp]
    simp [hs, hw, ht]
  · rintro ⟨k, hk, hrow⟩
    cases hp : σ[k]? with
    | none => simp [hp] at hrow
    | some p =>
      cases hs : settledBy p with
      | none => simp [hp, hs] at hrow
      | some w =>
        simp only [hp, hs, Option.bind_some, Option.map_some, Option.some.injEq, List.cons.injEq,
          and_true] at hrow
        obtain ⟨rfl, rfl⟩ := hrow
        have hk' : k ≤ n := Nat.le_of_lt_succ hk
        exact ⟨k, hk', visible_of_settled he hp hs, hwin k hk', ⟨p, hp, w, hs, by simp⟩, by simp⟩

theorem tpValue_inj : ∀ x < 8, ∀ y < 8, tpValue x = tpValue y → x = y :=
  fun _ _ _ _ h => TVal.tp.inj h

/-- Distinct timepoints give distinct rows. -/
theorem nodup_rowsUpTo (σ : Trace) (n : Nat) (hn : n < 8) : (rowsUpTo σ n).Nodup := by
  have h : (List.range (n + 1)).Pairwise fun a a' => a ≠ a' ∧ a < 8 ∧ a' < 8 :=
    List.nodup_range.imp_of_mem fun {a b} ha hb hne =>
      ⟨hne, by simp only [List.mem_range] at ha; omega, by simp only [List.mem_range] at hb; omega⟩
  refine List.Pairwise.filterMap _ ?_ h
  rintro a a' ⟨hne, ha, ha'⟩ row hrow row' hrow' rfl
  simp only [Option.map_eq_some_iff] at hrow hrow'
  obtain ⟨w, -, rfl⟩ := hrow
  obtain ⟨w', -, hr⟩ := hrow'
  simp only [List.cons.injEq, and_true] at hr
  exact hne (tpValue_inj a ha a' ha' hr.2.symm)

/-- The `sum` totals alice's settled refunds. -/
theorem total_settled (σ : Trace) (e : Event) (he : e.principal = some alice)
    (v : Valuation) (n : Nat) (hn : n < 8) (hwin : ∀ k ≤ n, InWindow .seconds σ n k window) :
    Total ι .seconds σ e (schema.Visible σ e) v n pinnedSettled (settledTotal σ n) := by
  refine ⟨rowsUpTo σ n, nodup_rowsUpTo σ n hn, fun row => ?_, rfl⟩
  show _ ↔ (row.length = 2 ∧ Sat ι .seconds σ e (schema.Visible σ e) (v.bindAll ["a", "t"] row) n _)
  constructor
  · intro hrow
    have hlen : row.length = 2 := by
      simp only [rowsUpTo, List.mem_filterMap] at hrow
      obtain ⟨k, _, hk⟩ := hrow
      simp only [Option.map_eq_some_iff] at hk
      obtain ⟨w, _, rfl⟩ := hk
      rfl
    match row, hlen with
    | [w₁, w₂], _ => exact ⟨rfl, (sat_body ι σ e he v n hwin w₁ w₂).mpr hrow⟩
  · rintro ⟨hlen, hs⟩
    match row, hlen with
    | [w₁, w₂], _ => exact (sat_body ι σ e he v n hwin w₁ w₂).mp hs

/-! ## The temporal leaf -/

/-- An integer in the `Long` range is read as itself. -/
theorem readLong_of_range {f : Int → Option Int} {n : Int} (h : Int64.MIN ≤ n ∧ n ≤ Int64.MAX) :
    readLong f n = some (.num n) := by
  simp [readLong, h]

/-- Timepoint `k` is in the day before timepoint `n`, as a `Bool`. -/
def inDay (σ : Trace) (n k : Nat) : Bool :=
  match σ[n]?, σ[k]? with
  | some pn, some pk => decide (0 ≤ pn.ts - pk.ts ∧ pn.ts - pk.ts ≤ 86400)
  | _, _ => false

theorem inWindow_of_inDay {σ : Trace} {n k : Nat} (h : inDay σ n k = true) :
    InWindow .seconds σ n k window := by
  unfold inDay at h
  unfold InWindow
  split at h
  · next pn pk hn hk =>
    simp only [decide_eq_true_eq] at h
    exact ⟨pn, pk, hn, hk, h.1, by simpa [window, Window.ticks, Window.seconds, TimeUnit.toSeconds, TickRate.seconds] using h.2⟩
  · cases h

/-- At alice's request for `amt` at timepoint `n`, the leaf holds exactly when
her settled refunds plus `amt` come to at most 100 — whichever reading `ι` of
out-of-range results, as long as the numbers stay in the `Long` range. -/
theorem leafHolds_iff (σ : Trace) (n : Nat) (hn : n < 8) {ts : Int} {amt : Int64} {rid : String}
    (hp : σ[n]? = some ⟨ts, request "alice" amt rid⟩)
    (hctx : (request "alice" amt rid).contextPath? ["input", "amount"] = some (.prim (.int amt)))
    (hwin : ∀ k ≤ n, inDay σ n k = true)
    (hrange : Int64.MIN ≤ settledTotal σ n ∧ settledTotal σ n ≤ Int64.MAX ∧
      Int64.MIN ≤ settledTotal σ n + amt.toInt ∧ settledTotal σ n + amt.toInt ≤ Int64.MAX) :
    policySet.LeafHolds ι σ n φ ↔ settledTotal σ n + amt.toInt ≤ 100 := by
  have he : (request "alice" amt rid).principal = some alice := rfl
  have htot := total_settled ι σ _ he Valuation.empty n hn fun k hk => inWindow_of_inDay (hwin k hk)
  have hagg : ι.aggregateValue (settledTotal σ n) = some (.num (settledTotal σ n)) :=
    readLong_of_range ⟨hrange.1, hrange.2.1⟩
  have harith : ι.arithValue (settledTotal σ n + amt.toInt) =
      some (.num (settledTotal σ n + amt.toInt)) :=
    readLong_of_range hrange.2.2
  simp only [PolicySet.LeafHolds, show policySet.schema = schema from rfl, φ_injected]
  constructor
  · rintro ⟨p, hp', hs⟩
    rw [hp] at hp'
    cases hp'
    obtain ⟨a, b, ⟨m, k, ⟨tot, htot', hm⟩, ⟨w, hw, hk⟩, hval⟩, ⟨w', hw', rfl⟩, hab⟩ := hs
    obtain rfl := total_unique htot' htot
    rw [hagg, Option.some.injEq, CVal.num.injEq] at hm
    subst hm
    simp only [Term.eval?, hctx, Option.map_some, Option.some.injEq] at hw
    subst hw
    simp only [CVal.ofTVal, CVal.ofValue, CVal.num.injEq] at hk
    subst hk
    rw [ArithOp.apply, harith, Option.some.injEq] at hval
    subst hval
    simp only [Term.eval?, Option.some.injEq] at hw'
    subst hw'
    simpa [CmpOp.Holds, CVal.ofTVal, CVal.ofValue] using hab
  · intro h
    refine ⟨_, hp, .num (settledTotal σ n + amt.toInt), .num 100,
      ⟨settledTotal σ n, amt.toInt, ⟨_, htot, hagg⟩,
        ⟨.val (.prim (.int amt)), by simp [Term.eval?, hctx], by simp [CVal.ofTVal, CVal.ofValue]⟩,
        harith⟩,
      ⟨.val (.prim (.int 100)), rfl, by decide⟩, ?_⟩
    simpa [CmpOp.Holds] using h

/-- The policy set is valid. -/
theorem policySet_valid : policySet.Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## The decisions on the bundle's trace -/

theorem settled_history :
    settledTotal history 0 = 0 ∧ settledTotal history 2 = 60 ∧ settledTotal history 3 = 60 ∧
      settledTotal history 5 = 90 ∧ settledTotal history 6 = 90 := by decide

variable (ω : Provider.Providers)

/-- How the policy set decides alice's request for `amt` at `n`, when its data conform. -/
theorem decision_request (σ : Trace) (n : Nat) (hn : n < 8) {ts : Int} {amt : Int64} {rid : String}
    (hp : σ[n]? = some ⟨ts, request "alice" amt rid⟩)
    (hctx : (request "alice" amt rid).contextPath? ["input", "amount"] = some (.prim (.int amt)))
    (hwin : ∀ k ≤ n, inDay σ n k = true)
    (hrange : Int64.MIN ≤ settledTotal σ n ∧ settledTotal σ n ≤ Int64.MAX ∧
      Int64.MIN ≤ settledTotal σ n + amt.toInt ∧ settledTotal σ n + amt.toInt ≤ Int64.MAX)
    (ha : policySet.Admits policySet.policies ω ⟨ts, request "alice" amt rid⟩ alice gw1) :
    (policySet.authorize ι ω σ n).decision? =
      some (if settledTotal σ n + amt.toInt ≤ 100 then .allow else .deny) := by
  have hb : ∀ ι', ι'.Completes ι → ((onePolicy refund φ schema actions).LeafHolds ι' σ n φ ↔
      decide (settledTotal σ n + amt.toInt ≤ 100) = true) := by
    intro ι' _
    rw [show onePolicy refund φ schema actions = policySet from rfl,
      leafHolds_iff ι' σ n hn hp hctx hwin hrange, decide_eq_true_iff]
  refine (decision_temporalPermit (ω := ω) hp ha hb).trans ?_
  by_cases h : settledTotal σ n + amt.toInt ≤ 100 <;> simp [h, request, logEvent]

/-- `@0`, a request for 60 with nothing settled: ALLOW. -/
theorem outcome_at_0 : (policySet.authorize ι ω history 0).decision? = some .allow := by
  rw [decision_request ι ω history 0 (by decide) rfl (by decide) (by decide) (by decide)
    (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel))]
  decide

/-- `@1` and `@21`, the settlements: no decision (history only). -/
theorem outcome_settlements :
    policySet.authorize ι ω history 1 = .noDecision ∧
    policySet.authorize ι ω history 4 = .noDecision :=
  ⟨authorize_history_only rfl (by decide), authorize_history_only rfl (by decide)⟩

/-- `@10`, a request for 50 with 60 settled: DENY. -/
theorem outcome_at_10 : (policySet.authorize ι ω history 2).decision? = some .deny := by
  rw [decision_request ι ω history 2 (by decide) rfl (by decide) (by decide) (by decide)
    (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel))]
  decide

/-- `@20`, a request for 30 with 60 settled: ALLOW. -/
theorem outcome_at_20 : (policySet.authorize ι ω history 3).decision? = some .allow := by
  rw [decision_request ι ω history 3 (by decide) rfl (by decide) (by decide) (by decide)
    (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel))]
  decide

/-- `@30`, a request for 15 with 90 settled: DENY. -/
theorem outcome_at_30 : (policySet.authorize ι ω history 5).decision? = some .deny := by
  rw [decision_request ι ω history 5 (by decide) rfl (by decide) (by decide) (by decide)
    (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel))]
  decide

/-- `@40`, a request for 10 with 90 settled: ALLOW, at exactly the budget. -/
theorem outcome_at_40 : (policySet.authorize ι ω history 6).decision? = some .allow := by
  rw [decision_request ι ω history 6 (by decide) rfl (by decide) (by decide) (by decide)
    (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel))]
  decide

/-! ## Budgets are per principal -/

/-- Bob's settled refund is not alice's. -/
theorem settled_shared : settledTotal shared 2 = 0 := by decide

/-- **The pin isolates the budget.** Bob's refund of 80 has settled, and alice
requests 30: she has settled nothing, so her request is allowed. Without the
pin on the `sum` inside the compound operand, the `sum` would total bob's
refund too, and the request would be denied. -/
theorem outcome_isolated : (policySet.authorize ι ω shared 2).decision? = some .allow := by
  rw [decision_request ι ω shared 2 (by decide) rfl (by decide) (by decide) (by decide)
    (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel))]
  decide

end Dogwood.Examples.RefundBudget
