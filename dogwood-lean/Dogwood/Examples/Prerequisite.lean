import Dogwood.Examples.Callers
import Dogwood.Examples.RateLimit

/-!
# Worked example: a prerequisite

The prerequisite idiom of the examples (`read_after_login`, `write_after_read`,
`sell_after_approval_valid_ticker`), with a caller pin only:

```text
permit (principal, action == Drupe::Action::"Read", resource)
when temporal { formerly within W Drupe::Action::"Login"::response{} };
```

under the default (pinned) event schema. Over every trace:

* **A read follows a login** (`allowed_read_after_login`): every allowed `Read` of a caller's is
  preceded, within `W`, by a `Login` response of the same caller's. Nothing is assumed of the
  trace.
* **A read follows an allowed login** (`allowed_read_after_allowed_login`): if each `Login`
  response answers an earlier `Login` request of the caller's that the login service allowed
  (`LoginResponsesFollowAllows`, an assumption about the service stated here and nowhere in the
  semantics), every allowed `Read` is preceded by such an allowed `Login` request. The window
  bounds the response, not the request: a login request long before, answered late, still lets
  the reads through.
-/

namespace Dogwood.Examples.Prerequisite

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Dogwood.Examples.RateLimit (leafHolds_of_allow)
open Cedar.Spec (EntityUID Value)

def read : EntityUID := action "Read"
def login : EntityUID := action "Login"

def actions : List ActionDecl := [(read, [("doc", .string)]), (login, [("doc", .string)])]

def schema : EventSchema := defaultSchema true actions

def afterLogin (w : Window) : Formula := .formerly w (.pred login "response" [])

def policySet (w : Window) : PolicySet := onePolicy read (afterLogin w) schema actions

theorem policySet_valid : (policySet ⟨1, .hours⟩).Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

theorem afterLogin_injected (w : Window) :
    (afterLogin w).injectPins schema = .formerly w (callerPred login "response") := by
  have h : schema.pinsOf login "response" = [callerPin] := by decide
  simp [afterLogin, callerPred, Formula.injectPins, h, callerPin, PinRef.toTerm]

/-- **Every allowed read follows a login of the same caller's, within the window**, on every
trace, under every reading. -/
theorem allowed_read_after_login {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace}
    {w : Window} {j : Nat} {pj : TimePoint} {u : EntityUID}
    (h : ((policySet w).authorize ι ω σ j).decision? = some .allow)
    (hpj : σ[j]? = some pj) (hu : pj.event.principal = some u) :
    ∃ k ≤ j, ∃ pk, σ[k]? = some pk ∧ ByCaller u login "response" pk ∧
      0 ≤ pj.ts - pk.ts ∧ pj.ts - pk.ts ≤ w.ticks .seconds := by
  obtain ⟨ι₀, -, pj', hpj', hsat⟩ := leafHolds_of_allow h
  rw [hpj] at hpj'
  cases hpj'
  change Sat ι₀ .seconds σ pj.event (schema.Visible σ pj.event) Valuation.empty j
    ((afterLogin w).injectPins schema) at hsat
  rw [afterLogin_injected] at hsat
  obtain ⟨k, hk, -, ⟨pj', pk, hpj', hpk, h₀, h₁⟩, hpred⟩ := hsat
  rw [hpj] at hpj'
  cases hpj'
  obtain ⟨pk', hpk', hb⟩ := (sat_callerPred hu login "response" _ k).mp hpred
  rw [hpk] at hpk'
  cases hpk'
  exact ⟨k, hk, pk, hpk, hb, h₀, h₁⟩

/-- **Login responses follow allows**: each of `u`'s `Login` responses answers an earlier `Login`
request of `u`'s that the login service allowed (`loginAllowed`). -/
def LoginResponsesFollowAllows (σ : Trace) (u : EntityUID) (loginAllowed : Nat → Prop)
    (answers : Nat → Nat) : Prop :=
  ∀ r p, σ[r]? = some p → ByCaller u login "response" p →
    answers r < r ∧ loginAllowed (answers r) ∧
      ∃ q, σ[answers r]? = some q ∧ ByCaller u login "request" q

/-- **Every allowed read follows an allowed login of the same caller's**, when login responses
follow allows. -/
theorem allowed_read_after_allowed_login {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace}
    {w : Window} {j : Nat} {pj : TimePoint} {u : EntityUID} {loginAllowed : Nat → Prop}
    {answers : Nat → Nat} (hfollow : LoginResponsesFollowAllows σ u loginAllowed answers)
    (h : ((policySet w).authorize ι ω σ j).decision? = some .allow)
    (hpj : σ[j]? = some pj) (hu : pj.event.principal = some u) :
    ∃ q < j, loginAllowed q ∧ ∃ pq, σ[q]? = some pq ∧ ByCaller u login "request" pq := by
  obtain ⟨k, hk, pk, hpk, hb, -⟩ := allowed_read_after_login h hpj hu
  obtain ⟨hlt, hallowed, pq, hpq, hbq⟩ := hfollow k pk hpk hb
  exact ⟨answers k, by omega, hallowed, pq, hpq, hbq⟩

end Dogwood.Examples.Prerequisite
