import Dogwood.Examples.Common
import Dogwood.Spec.Validity

/-!
# Worked example: `alert_exactly_three_transfers`

An aggregation over timepoints (`dogwood-docs/examples/alert_exactly_three_transfers`):

```text
permit (principal, action == Drupe::Action::"Alert", resource)
when temporal {
    (count for (t: Timepoint). where (
        formerly within 1h (Drupe::Action::"Transfer"::request{ input.amount: * } && tp(t))
    )) == 3
};
```

The bundle uses the *unpinned* event schema, so the leaf has global
semantics: transfers by any principal count. Transfers happen at `@0`, `@100`,
`@300` and `@500`; alerts at `@200`, `@400`, `@600` and `@3700`. The reference
interpreter allows the alerts at `@400` (three transfers in the hour) and
`@3700` (the `@0` transfer has left the window), and denies every other
event. This file derives the same outcomes from the specification.
-/

namespace Dogwood.Examples.ExactlyThreeTransfers

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Cedar.Spec (EntityUID Value)

def transfer : EntityUID := action "Transfer"
def alert : EntityUID := action "Alert"

def transferEvent (user : String) (amount : Int64) (requestId : String) : Event :=
  logEvent (oauthUser user) transfer "request" requestId
    [("amount", .prim (.int amount)), ("user", .prim (.string user))]

def alertEvent (level : Int64) (server requestId : String) : Event :=
  logEvent (oauthUser "alice") alert "request" requestId
    [("level", .prim (.int level)), ("server", .prim (.string server))]

def history : Trace := [
  ⟨0, transferEvent "alice" 5 "w1"⟩,
  ⟨100, transferEvent "bob" 42 "w2"⟩,
  ⟨200, alertEvent 1 "s1" "a1"⟩,
  ⟨300, transferEvent "carol" 9 "w3"⟩,
  ⟨400, alertEvent 1 "s1" "a2"⟩,
  ⟨500, transferEvent "dave" 1 "w4"⟩,
  ⟨600, alertEvent 2 "s2" "a3"⟩,
  ⟨3700, alertEvent 1 "s1" "a4"⟩]

def actions : List ActionDecl :=
  [(transfer, [("amount", .int), ("user", .string)]), (alert, [("level", .int), ("server", .string)])]

def schema : EventSchema := defaultSchema false actions

def transferPred : Formula := .pred transfer "request" [(["input", "amount"], .wildcard)]

def body : Formula := .formerly ⟨1, .hours⟩ (.and transferPred (.tp "t"))

def countTransfers : Aggregate := .count [⟨"t", .timepoint⟩] body

def φ : Formula := .cmp .eq (.agg countTransfers) (.long 3)

def policySet : PolicySet := onePolicy alert φ schema actions

/-! ## Facts about the trace -/

/-- Whether timepoint `k` is a transfer request. -/
def isTransfer (k : Nat) : Bool := (history[k]?.map fun p => p.event.action == transfer).getD false

/-- Whether timepoint `k` lies within the hour before timepoint `n`. -/
def inHour (n k : Nat) : Bool :=
  match history[n]?, history[k]? with
  | some pn, some pk => decide (0 ≤ pn.ts - pk.ts ∧ pn.ts - pk.ts ≤ 3600)
  | _, _ => false

/-- The transfers within the hour before timepoint `n`. -/
def transfersBefore (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun k => inHour n k && isTransfer k

theorem universalPins_schema : schema.universalPins = [] := by decide

theorem φ_injected : φ.injectPins schema = φ := by
  have h : schema.pinsOf transfer "request" = [] := by decide
  simp [φ, countTransfers, body, transferPred, Formula.injectPins, Term.injectPins,
    Aggregate.injectPins, h]

theorem inWindow_iff (n k : Nat) : InWindow .seconds history n k ⟨1, .hours⟩ ↔ inHour n k = true := by
  unfold InWindow inHour
  cases history[n]? <;> cases history[k]? <;> simp [Window.ticks, Window.seconds, TimeUnit.toSeconds, TickRate.seconds]

variable (ι : ImplChoices)

theorem sat_transferPred (e : Event) (vis : Nat → Prop) (v : Valuation) (k : Nat) :
    Sat ι .seconds history e vis v k transferPred ↔ isTransfer k = true := by
  have hargs : ∀ user amount rid,
      recordPath? (transferEvent user amount rid).logged ["input", "amount"] =
        some (.prim (.int amount)) →
      ArgsMatch e v (transferEvent user amount rid) [(["input", "amount"], .wildcard)] := by
    intro user amount rid h a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact ⟨.prim (.int amount), h, trivial⟩
  have halert : ∀ level server rid, (alertEvent level server rid).action ≠ transfer := by
    intro level server rid h
    simp [alertEvent, logEvent, transfer, alert, action, drupe] at h
  simp only [Sat, transferPred]
  match k with
  | 0 => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl, rfl, rfl, hargs _ _ _ (by decide)⟩⟩
  | 1 => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl, rfl, rfl, hargs _ _ _ (by decide)⟩⟩
  | 3 => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl, rfl, rfl, hargs _ _ _ (by decide)⟩⟩
  | 5 => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl, rfl, rfl, hargs _ _ _ (by decide)⟩⟩
  | 2 | 4 | 6 | 7 =>
    constructor
    · rintro ⟨p, hp, ha, _⟩
      cases hp
      exact absurd ha (halert _ _ _)
    · intro h
      exact absurd (beq_iff_eq.mp h) (halert _ _ _)
  | k + 8 =>
    constructor
    · rintro ⟨p, hp, _⟩
      simp [history] at hp
    · intro h
      simp [isTransfer, history] at h

/-- The `where` body holds of `t ↦ w` exactly when `w` is a transfer's
timepoint within the hour. -/
theorem sat_body (e : Event) (vis : Nat → Prop) (hvis : ∀ k, vis k) (v : Valuation) (n : Nat)
    (w : TVal) :
    Sat ι .seconds history e vis (v.bindAll ["t"] [w]) n body ↔ ∃ k ∈ transfersBefore n, w = tpValue k := by
  simp only [body, Sat, transfersBefore, List.mem_filter, List.mem_range, Bool.and_eq_true]
  constructor
  · rintro ⟨k, hk, _, hw, hpred, htp⟩
    simp only [Valuation.bindAll, Valuation.bind, if_true, Option.some.injEq] at htp
    exact ⟨k, ⟨Nat.lt_succ_of_le hk, (inWindow_iff n k).mp hw,
      (sat_transferPred ι e vis _ k).mp hpred⟩, htp⟩
  · rintro ⟨k, ⟨hk, hw, ht⟩, rfl⟩
    refine ⟨k, Nat.le_of_lt_succ hk, hvis k, (inWindow_iff n k).mpr hw,
      (sat_transferPred ι e vis _ k).mpr ht, ?_⟩
    simp [Valuation.bindAll, Valuation.bind]

theorem tpValue_inj : ∀ x < 8, ∀ y < 8, tpValue x = tpValue y → x = y :=
  fun _ _ _ _ h => TVal.tp.inj h

theorem transfersBefore_lt (n : Nat) (hn : n < 8) : ∀ k ∈ transfersBefore n, k < 8 := by
  intro k hk
  simp only [transfersBefore, List.mem_filter, List.mem_range] at hk
  omega

/-- The aggregate's total at timepoint `n` is the number of transfers in the
hour before `n`. -/
theorem total_count (e : Event) (vis : Nat → Prop) (hvis : ∀ k, vis k) (v : Valuation) (n : Nat)
    (hn : n < 8) :
    Total ι .seconds history e vis v n countTransfers (transfersBefore n).length := by
  refine ⟨(transfersBefore n).map fun k => [tpValue k], ?_, ?_, by simp⟩
  · have hnd : (transfersBefore n).Nodup := List.Nodup.sublist List.filter_sublist List.nodup_range
    rw [List.Nodup, List.pairwise_map]
    refine hnd.imp_of_mem fun {x y} hx hy hne heq => hne ?_
    simp only [List.cons.injEq, and_true] at heq
    exact tpValue_inj x (transfersBefore_lt n hn x hx) y (transfersBefore_lt n hn y hy) heq
  · intro row
    show _ ↔ (row.length = 1 ∧ Sat ι .seconds history e vis (v.bindAll ["t"] row) n body)
    constructor
    · intro hrow
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hrow
      exact ⟨rfl, (sat_body ι e vis hvis v n _).mpr ⟨k, hk, rfl⟩⟩
    · rintro ⟨hlen, hs⟩
      match row, hlen with
      | [w], _ =>
        obtain ⟨k, hk, rfl⟩ := (sat_body ι e vis hvis v n w).mp hs
        exact List.mem_map.mpr ⟨k, hk, rfl⟩

/-- The leaf holds at timepoint `n` exactly when three transfers fall in the
hour before it. -/
theorem leafHolds_iff (n : Nat) (hn : n < 8) :
    policySet.LeafHolds ι history n φ ↔ (transfersBefore n).length = 3 := by
  have hlen : (transfersBefore n).length ≤ 8 := by
    have := List.length_filter_le (fun k => inHour n k && isTransfer k) (List.range (n + 1))
    simp only [List.length_range] at this
    simp only [transfersBefore]
    omega
  have hval : ι.aggregateValue (transfersBefore n).length =
      some (.num (transfersBefore n).length) := by
    simp only [ImplChoices.aggregateValue, readLong]
    rw [if_pos (by simp only [Int64.MIN, Int64.MAX]; omega)]
  have hvis : ∀ e k, schema.Visible history e k := fun _ _ => Or.inl universalPins_schema
  obtain ⟨p, hp⟩ : ∃ p, history[n]? = some p := ⟨history[n], List.getElem?_eq_getElem hn⟩
  simp only [PolicySet.LeafHolds, show policySet.schema = schema from rfl, φ_injected]
  constructor
  · rintro ⟨p', hp', hs⟩
    obtain ⟨a, b, ha, hb, hab⟩ := hs
    obtain ⟨m, hm, hma⟩ := ha
    obtain ⟨w, hw, rfl⟩ := hb
    have hm' := total_unique hm (total_count ι p'.event _ (hvis p'.event) _ n hn)
    subst hm'
    rw [hval] at hma
    cases hma
    simp only [Term.eval?, Option.some.injEq] at hw
    subst hw
    simp only [CmpOp.Holds, CVal.ofTVal, CVal.ofValue, CVal.num.injEq] at hab
    have : ((3 : Int64).toInt) = 3 := by decide
    omega
  · intro h3
    refine ⟨p, hp, .num 3, .num 3, ⟨_, total_count ι p.event _ (hvis p.event) _ n hn, ?_⟩,
      ⟨.val (.prim (.int 3)), rfl, rfl⟩, rfl⟩
    rw [hval, h3]
    rfl

/-- The policy set is valid. -/
theorem policySet_valid : policySet.Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## The decisions -/

variable (ω : Provider.Providers)

theorem transfers_at_400 : (transfersBefore 4).length = 3 := by decide
theorem transfers_at_3700 : (transfersBefore 7).length = 3 := by decide
theorem transfers_at_200 : (transfersBefore 2).length = 2 := by decide
theorem transfers_at_600 : (transfersBefore 6).length = 4 := by decide

/-- The transfers decide nothing in the rule's favor: DENY. -/
theorem outcome_transfers :
    (policySet.authorize ι ω history 0).decision? = some .deny ∧
    (policySet.authorize ι ω history 1).decision? = some .deny ∧
    (policySet.authorize ι ω history 3).decision? = some .deny ∧
    (policySet.authorize ι ω history 5).decision? = some .deny :=
  ⟨decision_temporalPermit_other rfl rfl (by decide +kernel),
   decision_temporalPermit_other rfl rfl (by decide +kernel),
   decision_temporalPermit_other rfl rfl (by decide +kernel),
   decision_temporalPermit_other rfl rfl (by decide +kernel)⟩

/-- `@200`: two transfers in the hour — DENY. -/
theorem outcome_at_200 : (policySet.authorize ι ω history 2).decision? = some .deny :=
  decision_temporalPermit_deny rfl rfl
    (.inr fun ι' _ h => absurd ((leafHolds_iff ι' 2 (by decide)).mp h)
      (by rw [transfers_at_200]; decide))

/-- The alerts `@400` and `@3700` pass every check of the decision: their logged records, their
requests, and their entity stores conform. -/
theorem admits_at_400 : policySet.Admits policySet.policies ω ⟨400, alertEvent 1 "s1" "a2"⟩
    (oauthUser "alice") gw1 :=
  onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem admits_at_3700 : policySet.Admits policySet.policies ω ⟨3700, alertEvent 1 "s1" "a4"⟩
    (oauthUser "alice") gw1 :=
  onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `@400`: three transfers in the hour — ALLOW. -/
theorem outcome_at_400 : (policySet.authorize ι ω history 4).decision? = some .allow := by
  refine (decision_temporalPermit (b := true) rfl (admits_at_400 ω)
    fun ι' _ => (leafHolds_iff ι' 4 (by decide)).trans (by rw [transfers_at_400]; decide)).trans
    (by decide)

/-- `@600`: four transfers in the hour — DENY. -/
theorem outcome_at_600 : (policySet.authorize ι ω history 6).decision? = some .deny :=
  decision_temporalPermit_deny rfl rfl
    (.inr fun ι' _ h => absurd ((leafHolds_iff ι' 6 (by decide)).mp h)
      (by rw [transfers_at_600]; decide))

/-- `@3700`: the `@0` transfer has left the window; three remain — ALLOW. -/
theorem outcome_at_3700 : (policySet.authorize ι ω history 7).decision? = some .allow := by
  refine (decision_temporalPermit (b := true) rfl (admits_at_3700 ω)
    fun ι' _ => (leafHolds_iff ι' 7 (by decide)).trans (by rw [transfers_at_3700]; decide)).trans
    (by decide)

end Dogwood.Examples.ExactlyThreeTransfers
