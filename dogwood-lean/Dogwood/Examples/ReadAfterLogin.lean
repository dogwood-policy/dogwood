import Dogwood.Examples.Common
import Dogwood.Spec.Validity

/-!
# Worked example: `read_after_login`

The guide's first example (`dogwood-docs/examples/read_after_login`):

```text
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
};
```

replayed against a login request at `@0`, its successful response at `@5`,
and reads at `@10` and `@7200`, under the default (pinned) event schema. The
reference interpreter's verdicts (`expected.out`) are DENY, ALLOW, DENY for
the three decision events; the response decides nothing. This file derives
the same outcomes from the specification, at one tick per second, and the
allow at `@10` again at nanoseconds (`outcome_at_10_nanos`).
-/

namespace Dogwood.Examples.ReadAfterLogin

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Cedar.Spec (EntityUID Value)

def alice : EntityUID := oauthUser "alice"
def login : EntityUID := action "Login"
def read : EntityUID := action "Read"

def event (a : EntityUID) (kind requestId : String) : Event :=
  logEvent alice a kind requestId [("user", .prim (.string "alice"))]

def history : Trace := [
  ⟨0, event login "request" "u1"⟩,
  ⟨5, event login "response" "u1"⟩,
  ⟨10, event read "request" "u2"⟩,
  ⟨7200, event read "request" "u3"⟩]

def actions : List ActionDecl := [(login, [("user", .string)]), (read, [("user", .string)])]

def schema : EventSchema := defaultSchema true actions

def φ : Formula :=
  .formerly ⟨1, .hours⟩ (.pred login "response" [(["input", "user"], .context ["input", "user"])])

def policySet : PolicySet := onePolicy read φ schema actions

/-! ## The temporal leaf at each decision point -/

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

theorem pinsOf_login_response : schema.pinsOf login "response" = [callerPin] := by decide

/-- After pin injection, the login predicate also requires the request's
principal. -/
theorem φ_injected : φ.injectPins schema =
    .formerly ⟨1, .hours⟩ (.pred login "response"
      [(["input", "user"], .context ["input", "user"]), (["callerPrincipal"], .scope .principal [])]) := by
  simp [φ, Formula.injectPins, pinsOf_login_response, callerPin, PinRef.toTerm]

variable (ι : ImplChoices)

/-- At the read `@10`, the login response `@5` is in the window, of the same
user, and from the same principal. -/
theorem leaf_holds_at_10 : policySet.LeafHolds ι history 2 φ := by
  refine ⟨⟨10, event read "request" "u2"⟩, rfl, ?_⟩
  show Sat ι .seconds history _ (schema.Visible history _) _ 2 (φ.injectPins schema)
  rw [φ_injected]
  refine ⟨1, by decide, Or.inr ⟨⟨5, event login "response" "u1"⟩, rfl, ?_, ?_⟩, ?_, ?_⟩
  · decide
  · rw [universalPins_schema]
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨.prim (.entityUID alice), by decide, rfl⟩
  · exact ⟨_, _, rfl, rfl, by decide, by decide⟩
  · refine ⟨_, rfl, rfl, rfl, ?_⟩
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨.prim (.string "alice"), by decide, rfl⟩
    · exact ⟨.prim (.entityUID alice), by decide, rfl⟩

/-- The leaf fails at timepoint `n` when no timepoint up to `n` holds a login
response within the hour. -/
theorem leaf_fails (n : Nat)
    (h : ∀ k ≤ n, ∀ pj pk, history[n]? = some pj → history[k]? = some pk →
      pk.event.action = login → pk.event.kind = "response" → pj.ts - pk.ts ≤ 3600 → False) :
    ¬ policySet.LeafHolds ι history n φ := by
  rintro ⟨p, _, hs⟩
  change Sat ι .seconds history _ (schema.Visible history _) _ n (φ.injectPins schema) at hs
  rw [φ_injected] at hs
  obtain ⟨k, hk, _, ⟨pj, pk, hpj, hpk, _, hw⟩, ⟨p', hp', ha, hkd, _⟩⟩ := hs
  rw [hpk] at hp'
  cases hp'
  exact h k hk pj pk hpj hpk ha hkd hw

/-- At the login request `@0` there is no login response yet. -/
theorem leaf_fails_at_0 : ¬ policySet.LeafHolds ι history 0 φ := by
  refine leaf_fails ι 0 fun k hk pj pk _ hpk _ hkd _ => ?_
  obtain rfl : k = 0 := by omega
  simp only [history] at hpk
  cases hpk
  simp [event, logEvent] at hkd

/-- At the read `@7200`, the only login response (`@5`) is out of the window. -/
theorem leaf_fails_at_7200 : ¬ policySet.LeafHolds ι history 3 φ := by
  refine leaf_fails ι 3 fun k hk pj pk hpj hpk ha hkd hw => ?_
  simp only [history] at hpj
  cases hpj
  match k, hk with
  | 0, _ => simp only [history] at hpk; cases hpk; simp [event, logEvent] at hkd
  | 1, _ => simp only [history] at hpk; cases hpk; simp at hw
  | 2, _ => simp only [history] at hpk; cases hpk; simp [event, logEvent, read, login, action, drupe] at ha
  | 3, _ => simp only [history] at hpk; cases hpk; simp [event, logEvent, read, login, action, drupe] at ha

/-- The policy set is valid. -/
theorem policySet_valid : policySet.Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## The decisions -/

variable (ω : Provider.Providers)

/-- `@0`, the login request: DENY (the rule does not apply to `Login`). -/
theorem outcome_at_0 : (policySet.authorize ι ω history 0).decision? = some .deny :=
  decision_temporalPermit_deny rfl rfl (.inl (by decide +kernel))

/-- `@5`, the login response: no decision (history only). -/
theorem outcome_at_5 : policySet.authorize ι ω history 1 = .noDecision :=
  authorize_history_only (p := ⟨5, event login "response" "u1"⟩) rfl (by decide)

/-- The read `@10` passes every check of the decision: its logged record, its request, and its
entity store conform. -/
theorem admits_at_10 :
    policySet.Admits policySet.policies ω ⟨10, event read "request" "u2"⟩ alice gw1 :=
  onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `@10`, the first read: ALLOW. -/
theorem outcome_at_10 : (policySet.authorize ι ω history 2).decision? = some .allow := by
  refine (decision_temporalPermit (b := true) rfl (admits_at_10 ω)
    fun ι' _ => ⟨fun _ => rfl, fun _ => leaf_holds_at_10 ι'⟩).trans ?_
  decide

/-- `@10`, the first read, at nanoseconds: an authorizer that stamps in nanoseconds stamps the
recorded times as `s × 10⁹`, and allows the read too (`authorize_scale`). -/
theorem outcome_at_10_nanos :
    (({ policySet with tickRate := .nanos } : PolicySet).authorize ι ω
      (history.scale 1000000000) 2).decision? = some .allow := by
  have h : ({ policySet with tickRate := .nanos } : PolicySet) =
      policySet.scale 1000000000 (by decide) := rfl
  rw [h, authorize_scale]
  exact outcome_at_10 ι ω

/-- `@7200`, the second read: DENY (the login has left the window). -/
theorem outcome_at_7200 : (policySet.authorize ι ω history 3).decision? = some .deny :=
  decision_temporalPermit_deny rfl rfl (.inr fun ι' _ => leaf_fails_at_7200 ι')

end Dogwood.Examples.ReadAfterLogin
