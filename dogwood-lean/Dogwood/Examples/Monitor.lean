import Dogwood.Examples.Callers
import Dogwood.Examples.RateLimit

/-!
# Worked example: an exact monitor

The alerting idiom of the examples, in its simplest form, with a caller pin
(`alert_login_in_last_hour` writes the same kind of condition as a positive count):

```text
permit (principal, action == Drupe::Action::"Alert", resource)
when temporal { formerly within W Drupe::Action::"Login"::request{} };
```

under the default (pinned) event schema. A monitor's policy is meant to say exactly when it
fires. Over every trace, under every reading:

* **An alert is allowed exactly when its condition holds** (`alert_allowed_iff`): an `Alert` of a
  caller's whose data pass the decision's checks is allowed if and only if a `Login` request of
  the caller's is logged within `W` before it. The condition reads no aggregate or arithmetic, so
  no reading of out-of-range results enters.
* **An alert whose data fail the checks is denied** (`PolicySet.authorize` fails closed; an allow
  passed every check, `Dogwood.Thm.decideWith_decision?_allow`), whatever the history.
-/

namespace Dogwood.Examples.Monitor

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Cedar.Spec (EntityUID Value)

def alert : EntityUID := action "Alert"
def login : EntityUID := action "Login"

def actions : List ActionDecl := [(alert, [("doc", .string)]), (login, [("doc", .string)])]

def schema : EventSchema := defaultSchema true actions

def recentLogin (w : Window) : Formula := .formerly w (.pred login "request" [])

def policySet (w : Window) : PolicySet := onePolicy alert (recentLogin w) schema actions

theorem policySet_valid : (policySet ⟨1, .hours⟩).Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

theorem injected (w : Window) :
    (recentLogin w).injectPins schema = .formerly w (callerPred login "request") := by
  have h : schema.pinsOf login "request" = [callerPin] := by decide
  simp [recentLogin, callerPred, Formula.injectPins, h, callerPin, PinRef.toTerm]

/-- The condition: a `Login` request of `u`'s within `w` before timepoint `j`. -/
def RecentLogin (σ : Trace) (w : Window) (u : EntityUID) (j : Nat) : Prop :=
  ∃ k ≤ j, ∃ pj pk, σ[j]? = some pj ∧ σ[k]? = some pk ∧ ByCaller u login "request" pk ∧
    0 ≤ pj.ts - pk.ts ∧ pj.ts - pk.ts ≤ w.ticks .seconds

/-- The leaf holds, under any reading, exactly when the condition does. -/
theorem leafHolds_iff {ι : ImplChoices} {σ : Trace} {w : Window} {j : Nat} {pj : TimePoint}
    {u : EntityUID} (hpj : σ[j]? = some pj) (hu : pj.event.principal = some u) :
    (policySet w).LeafHolds ι σ j (recentLogin w) ↔ RecentLogin σ w u j := by
  constructor
  · rintro ⟨pj', hpj', hsat⟩
    rw [hpj] at hpj'
    cases hpj'
    change Sat ι .seconds σ pj.event (schema.Visible σ pj.event) Valuation.empty j
      ((recentLogin w).injectPins schema) at hsat
    rw [injected] at hsat
    obtain ⟨k, hk, -, ⟨pj', pk, hpj', hpk, h₀, h₁⟩, hpred⟩ := hsat
    obtain ⟨pk', hpk', hb⟩ := (sat_callerPred hu login "request" _ k).mp hpred
    rw [hpk] at hpk'
    cases hpk'
    exact ⟨k, hk, pj', pk, hpj', hpk, hb, h₀, h₁⟩
  · rintro ⟨k, hk, pj', pk, hpj', hpk, hb, h₀, h₁⟩
    refine ⟨pj, hpj, ?_⟩
    change Sat ι .seconds σ pj.event (schema.Visible σ pj.event) Valuation.empty j
      ((recentLogin w).injectPins schema)
    rw [injected]
    refine ⟨k, hk, visible_of_byCaller universalPins_schema
      (sig_defaultSchema (ins := [("doc", .string)]) (by simp [actions]) (.inl rfl)) hu hpk hb,
      ⟨pj', pk, hpj', hpk, h₀, h₁⟩, (sat_callerPred hu login "request" _ k).mpr ⟨pk, hpk, hb⟩⟩

/-- **An alert is allowed exactly when a login of the caller's is logged within the window before
it**, for an alert whose data pass the decision's checks, on every trace, under every reading. -/
theorem alert_allowed_iff {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace} {w : Window}
    {j : Nat} {pj : TimePoint} {u rs : EntityUID} (hpj : σ[j]? = some pj)
    (ha : pj.event.action = alert) (hu : pj.event.principal = some u)
    (hadm : (policySet w).Admits (policySet w).policies ω pj u rs) :
    ((policySet w).authorize ι ω σ j).decision? = some .allow ↔ RecentLogin σ w u j := by
  classical
  have h := decision_temporalPermit (ι := ι) (b := decide (RecentLogin σ w u j)) hpj hadm
    fun ι' _ => (leafHolds_iff (ι := ι') hpj hu).trans decide_eq_true_iff.symm
  change ((onePolicy alert (recentLogin w) schema actions).authorize ι ω σ j).decision? = _ ↔ _
  rw [h]
  simp [ha]

end Dogwood.Examples.Monitor
