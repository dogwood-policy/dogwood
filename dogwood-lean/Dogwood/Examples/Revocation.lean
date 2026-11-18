import Dogwood.Examples.Callers
import Dogwood.Examples.RateLimit

/-!
# Worked example: revocation

The revocation idiom of the example `access_not_revoked_since_grant`, with a caller pin only:

```text
permit (principal, action == Drupe::Action::"Access", resource)
when temporal {
    !Drupe::Action::"Revoke"::response{} since within W Drupe::Action::"Grant"::response{}
};
```

under the default (pinned) event schema. Over every trace, under every reading:

* **No access after a revocation until a new grant** (`no_access_after_revoke`): once a revocation
  of a caller's is logged, no `Access` of the caller's is allowed until a grant of the caller's is
  logged after it, within `W` of the access. A revocation and a grant are never at the same
  timepoint (each timepoint is one event), so which came first is never in doubt.
* **An access needs a recent grant** (`allowed_access_after_grant`): every allowed `Access` is
  preceded, within `W`, by a grant of the caller's, with no revocation of the caller's since.
  `within W` bounds the grant: a grant older than `W` does not let accesses through.
-/

namespace Dogwood.Examples.Revocation

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Dogwood.Examples.RateLimit (leafHolds_of_allow)
open Cedar.Spec (EntityUID Value)

def access : EntityUID := action "Access"
def grant : EntityUID := action "Grant"
def revoke : EntityUID := action "Revoke"

def actions : List ActionDecl :=
  [(access, [("doc", .string)]), (grant, [("doc", .string)]), (revoke, [("doc", .string)])]

def schema : EventSchema := defaultSchema true actions

def notRevokedSinceGrant (w : Window) : Formula :=
  .since (.not (.pred revoke "response" [])) w (.pred grant "response" [])

def policySet (w : Window) : PolicySet := onePolicy access (notRevokedSinceGrant w) schema actions

theorem policySet_valid : (policySet ⟨1, .hours⟩).Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

theorem injected (w : Window) :
    (notRevokedSinceGrant w).injectPins schema =
      .since (.not (callerPred revoke "response")) w (callerPred grant "response") := by
  have h₁ : schema.pinsOf revoke "response" = [callerPin] := by decide
  have h₂ : schema.pinsOf grant "response" = [callerPin] := by decide
  simp [notRevokedSinceGrant, callerPred, Formula.injectPins, h₁, h₂, callerPin, PinRef.toTerm]

/-- **Every allowed access follows a recent grant of the caller's, with no revocation of the
caller's since**: on every trace, under every reading. -/
theorem allowed_access_after_grant {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace}
    {w : Window} {j : Nat} {pj : TimePoint} {u : EntityUID}
    (h : ((policySet w).authorize ι ω σ j).decision? = some .allow)
    (hpj : σ[j]? = some pj) (hu : pj.event.principal = some u) :
    ∃ k ≤ j, (∃ pk, σ[k]? = some pk ∧ ByCaller u grant "response" pk ∧
      0 ≤ pj.ts - pk.ts ∧ pj.ts - pk.ts ≤ w.ticks .seconds) ∧
      ∀ r, k < r → r ≤ j → ∀ pr, σ[r]? = some pr → ¬ ByCaller u revoke "response" pr := by
  obtain ⟨ι₀, -, pj', hpj', hsat⟩ := leafHolds_of_allow h
  rw [hpj] at hpj'
  cases hpj'
  change Sat ι₀ .seconds σ pj.event (schema.Visible σ pj.event) Valuation.empty j
    ((notRevokedSinceGrant w).injectPins schema) at hsat
  rw [injected] at hsat
  obtain ⟨k, hk, -, ⟨pj', pk, hpj', hpk, h₀, h₁⟩, hgrant, hsince⟩ := hsat
  rw [hpj] at hpj'
  cases hpj'
  obtain ⟨pk', hpk', hb⟩ := (sat_callerPred hu grant "response" _ k).mp hgrant
  rw [hpk] at hpk'
  cases hpk'
  refine ⟨k, hk, ⟨pk, hpk, hb, h₀, h₁⟩, fun r hkr hrj pr hpr hbr => ?_⟩
  have hvis := visible_of_byCaller universalPins_schema
    (sig_defaultSchema (ins := [("doc", .string)]) (by simp [actions]) (.inr (.inl rfl))) hu hpr
    hbr
  exact hsince r hkr hrj hvis ((sat_callerPred hu revoke "response" _ r).mpr ⟨pr, hpr, hbr⟩)

/-- **No access after a revocation until a new grant**: if a revocation of `u`'s is logged at
`r`, an access of `u`'s allowed at or after `r` follows a grant of `u`'s logged after `r`, within
the window. -/
theorem no_access_after_revoke {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace}
    {w : Window} {j r : Nat} {pj pr : TimePoint} {u : EntityUID}
    (hpr : σ[r]? = some pr) (hrevoke : ByCaller u revoke "response" pr) (hrj : r ≤ j)
    (h : ((policySet w).authorize ι ω σ j).decision? = some .allow)
    (hpj : σ[j]? = some pj) (hu : pj.event.principal = some u) :
    ∃ k, r < k ∧ k ≤ j ∧ ∃ pk, σ[k]? = some pk ∧ ByCaller u grant "response" pk ∧
      pj.ts - pk.ts ≤ w.ticks .seconds := by
  obtain ⟨k, hk, ⟨pk, hpk, hb, -, h₁⟩, hnone⟩ := allowed_access_after_grant h hpj hu
  refine ⟨k, ?_, hk, pk, hpk, hb, h₁⟩
  rcases Nat.lt_trichotomy r k with hlt | rfl | hgt
  · exact hlt
  · rw [hpk] at hpr
    cases hpr
    exact absurd (hb.1.symm.trans hrevoke.1) (by decide)
  · exact absurd hrevoke (hnone r hgt hrj pr hpr)

end Dogwood.Examples.Revocation
