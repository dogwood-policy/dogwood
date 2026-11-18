import Dogwood.Examples.Common
import Dogwood.Spec.Validity

/-!
# Worked example: `access_not_revoked_since_grant`

A negated-left `since` (`dogwood-docs/examples/access_not_revoked_since_grant`):

```text
permit (principal, action == Drupe::Action::"Access", resource)
when temporal {
    !Drupe::Action::"Revoke"::response{ input.user: context.input.user, input.resource: context.input.resource }
    since within 1h
    Drupe::Action::"Grant"::response{ input.user: context.input.user, input.resource: context.input.resource }
};
```

under the default (pinned) event schema, so the leaf has key-local
semantics. A grant of `doc1` to alice completes at `@35940`, she accesses it
at `@36060`, a revocation completes at `@36120`, and she accesses it again at
`@36180`. The completions are `response` events, which the default schema
records as history and does not decide. The reference interpreter allows the
access at `@36060` and denies the one at `@36180`. This file derives the same
outcomes from the specification.
-/

namespace Dogwood.Examples.NotRevokedSinceGrant

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Cedar.Spec (EntityUID Value)

def alice : EntityUID := oauthUser "alice"
def grant : EntityUID := action "Grant"
def access : EntityUID := action "Access"
def revoke : EntityUID := action "Revoke"

def event (a : EntityUID) (kind requestId : String) : Event :=
  logEvent alice a kind requestId
    [("resource", .prim (.string "doc1")), ("user", .prim (.string "alice"))]

def history : Trace := [
  ⟨35940, event grant "response" "u1"⟩,
  ⟨36060, event access "request" "u2"⟩,
  ⟨36120, event revoke "response" "u3"⟩,
  ⟨36180, event access "request" "u4"⟩]

def actions : List ActionDecl :=
  [(grant, [("resource", .string), ("user", .string)]),
   (access, [("resource", .string), ("user", .string)]),
   (revoke, [("resource", .string), ("user", .string)])]

def schema : EventSchema := defaultSchema true actions

/-- The same user and resource as the current request. -/
def sameUserAndResource : List (Path × Term) :=
  [(["input", "user"], .context ["input", "user"]),
   (["input", "resource"], .context ["input", "resource"])]

def φ : Formula :=
  .since (.not (.pred revoke "response" sameUserAndResource)) ⟨1, .hours⟩
    (.pred grant "response" sameUserAndResource)

def policySet : PolicySet := onePolicy access φ schema actions

/-! ## The temporal leaf at each access -/

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

/-- After pin injection, both predicates also require the request's principal. -/
theorem φ_injected : φ.injectPins schema =
    .since (.not (.pred revoke "response"
        (sameUserAndResource ++ [(["callerPrincipal"], .scope .principal [])])))
      ⟨1, .hours⟩
      (.pred grant "response"
        (sameUserAndResource ++ [(["callerPrincipal"], .scope .principal [])])) := by
  have hr : schema.pinsOf revoke "response" = [callerPin] := by decide
  have hg : schema.pinsOf grant "response" = [callerPin] := by decide
  simp [φ, Formula.injectPins, hr, hg, callerPin, PinRef.toTerm]

/-- The event at each timepoint of the trace. -/
def eventAt : Nat → Event
  | 0 => event grant "response" "u1"
  | 1 => event access "request" "u2"
  | 2 => event revoke "response" "u3"
  | _ => event access "request" "u4"

theorem history_get (k : Nat) (hk : k < 4) : ∃ ts, history[k]? = some ⟨ts, eventAt k⟩ := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ => exact ⟨_, rfl⟩

/-- Every event of the trace is alice's, so every timepoint is visible to a
decision at an event of alice's. -/
theorem visible (e : Event) (he : e.principal = some alice) (k : Nat) (hk : k < 4) :
    schema.Visible history e k := by
  obtain ⟨ts, hget⟩ := history_get k hk
  refine Or.inr ⟨⟨ts, eventAt k⟩, hget, ?_, ?_⟩
  · match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ => dsimp only; decide
  · rw [universalPins_schema]
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    refine ⟨.prim (.entityUID alice), ?_, ?_⟩
    · match k, hk with
      | 0, _ | 1, _ | 2, _ | 3, _ => dsimp only; decide
    · simp [callerPin, PinRef.toTerm, Term.eval?, Event.scopePath?, Event.scope, he]

/-- At an access by alice to `doc1`, the pinned `response` predicate for the
grant or the revocation holds at timepoint `k` exactly when `k`'s event is an
event of that action. -/
theorem sat_pinned (ι : ImplChoices) (e : Event) (vis : Nat → Prop) (v : Valuation)
    (he : e = event access "request" "u2" ∨ e = event access "request" "u4") (a : EntityUID)
    (hga : a = grant ∨ a = revoke) (k : Nat) (hk : k < 4) :
    Sat ι .seconds history e vis v k
        (.pred a "response" (sameUserAndResource ++ [(["callerPrincipal"], .scope .principal [])])) ↔
      (eventAt k).action = a := by
  obtain ⟨ts, hget⟩ := history_get k hk
  simp only [Sat]
  constructor
  · rintro ⟨p, hp, ha, _⟩
    rw [hget] at hp
    cases hp
    exact ha
  · intro ha
    refine ⟨⟨ts, eventAt k⟩, hget, ha, ?_, ?_⟩
    · rcases hga with rfl | rfl <;>
      match k, hk with
      | 0, _ | 1, _ | 2, _ | 3, _ => first | rfl | exact absurd ha (by decide)
    · intro arg harg
      simp only [sameUserAndResource, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at harg
      rcases he with rfl | rfl <;>
      rcases harg with rfl | rfl | rfl <;>
      match k, hk with
      | 0, _ | 1, _ | 2, _ | 3, _ =>
        first
          | exact ⟨.prim (.string "alice"), by dsimp only; decide,
              by simp only [Term.Matches, Term.eval?]; decide⟩
          | exact ⟨.prim (.string "doc1"), by dsimp only; decide,
              by simp only [Term.Matches, Term.eval?]; decide⟩
          | exact ⟨.prim (.entityUID alice), by dsimp only; decide,
              by simp only [Term.Matches, Term.eval?]; decide⟩

variable (ι : ImplChoices)

/-- At the access `@36060`: granted at `@35940`, not revoked since. -/
theorem leaf_holds_at_36060 : policySet.LeafHolds ι history 1 φ := by
  refine ⟨⟨36060, event access "request" "u2"⟩, rfl, ?_⟩
  show Sat ι .seconds history _ (schema.Visible history _) _ 1 (φ.injectPins schema)
  rw [φ_injected]
  refine ⟨0, by decide, visible _ rfl 0 (by decide), ⟨_, _, rfl, rfl, by decide, by decide⟩,
    (sat_pinned ι _ _ _ (Or.inl rfl) grant (Or.inl rfl) 0 (by decide)).mpr rfl, ?_⟩
  intro k' h₀ h₁ _
  obtain rfl : k' = 1 := by omega
  show ¬ _
  rw [sat_pinned ι _ _ _ (Or.inl rfl) revoke (Or.inr rfl) 1 (by decide)]
  decide

/-- At the access `@36180`: the only grant (`@35940`) has been revoked since,
at `@36120`. -/
theorem leaf_fails_at_36180 : ¬ policySet.LeafHolds ι history 3 φ := by
  rintro ⟨p, hp, hs⟩
  cases hp
  change Sat ι .seconds history _ (schema.Visible history _) _ 3 (φ.injectPins schema) at hs
  rw [φ_injected] at hs
  obtain ⟨k, hk, _, _, hanchor, hsince⟩ := hs
  rw [sat_pinned ι _ _ _ (Or.inr rfl) grant (Or.inl rfl) k (by omega)] at hanchor
  -- The anchor must be the grant at `@35940` …
  obtain rfl : k = 0 := by
    match k, hk with
    | 0, _ => rfl
    | 1, _ | 2, _ | 3, _ => exact absurd hanchor (by decide)
  -- … and the revocation at `@36120` breaks the `since`.
  have hrev := hsince 2 (by decide) (by decide) (visible _ rfl 2 (by decide))
  exact hrev ((sat_pinned ι _ _ _ (Or.inr rfl) revoke (Or.inr rfl) 2 (by decide)).mpr rfl)

/-- The policy set is valid. -/
theorem policySet_valid : policySet.Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## The decisions -/

variable (ω : Provider.Providers)

/-- The completed grant and revocation are history: no decision. -/
theorem outcome_history :
    policySet.authorize ι ω history 0 = .noDecision ∧
    policySet.authorize ι ω history 2 = .noDecision :=
  ⟨authorize_history_only rfl (by decide), authorize_history_only rfl (by decide)⟩

/-- `@36060`: ALLOW. -/
theorem outcome_at_36060 : (policySet.authorize ι ω history 1).decision? = some .allow :=
  (decision_temporalPermit (b := true) rfl
    (onePolicy_admitsB rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel))
    fun ι' _ => ⟨fun _ => rfl, fun _ => leaf_holds_at_36060 ι'⟩).trans (by decide)

/-- `@36180`: DENY. -/
theorem outcome_at_36180 : (policySet.authorize ι ω history 3).decision? = some .deny :=
  decision_temporalPermit_deny rfl rfl (.inr fun ι' _ => leaf_fails_at_36180 ι')

end Dogwood.Examples.NotRevokedSinceGrant
