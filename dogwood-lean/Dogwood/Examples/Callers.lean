import Dogwood.Examples.Common

/-!
# A caller's events, under a universal caller pin

Helpers shared by the worked examples that prove guarantees over every trace
(`Dogwood.Examples.Prerequisite`, `Revocation`, `Monitor`, `ConcurrencyCap`, `Balance`):
under an event schema whose universal pin is the caller (`callerPin`), a predicate after pin
injection matches the decision's caller's events, and those events are visible to it.
-/

namespace Dogwood.Examples

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (EntityUID Value)

/-- The timepoint `p` is an event of action `a` and kind `kind` that logs `u` as its caller. -/
def ByCaller (u a : EntityUID) (kind : String) (p : TimePoint) : Prop :=
  p.event.action = a ∧ p.event.kind = kind ∧
    recordPath? p.event.logged ["callerPrincipal"] = some (.prim (.entityUID u))

/-- `a::kind{}` after injection of the caller pin. -/
def callerPred (a : EntityUID) (kind : String) : Formula :=
  .pred a kind [(["callerPrincipal"], .scope .principal [])]

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

/-- At a decision of `u`'s, the pinned predicate matches exactly `u`'s events of its action and
kind. -/
theorem sat_callerPred {u : EntityUID} (he : e.principal = some u) (a : EntityUID)
    (kind : String) (v : Valuation) (k : Nat) :
    Sat ι rate σ e vis v k (callerPred a kind) ↔ ∃ p, σ[k]? = some p ∧ ByCaller u a kind p := by
  simp only [Sat, callerPred, ArgsMatch, List.mem_singleton, forall_eq]
  simp only [Term.Matches, Term.eval?, Event.scopePath?, Event.scope, he, Option.map_some,
    Option.some.injEq, TVal.val.injEq, ByCaller]
  constructor
  · rintro ⟨p, hp, ha, hk, w, hw, rfl⟩
    exact ⟨p, hp, ha, hk, hw⟩
  · rintro ⟨p, hp, ha, hk, hw⟩
    exact ⟨p, hp, ha, hk, _, hw, rfl⟩

/-- `u`'s events of a declared signature are visible to a decision of `u`'s, under a schema whose
universal pin is the caller. -/
theorem visible_of_byCaller {S : EventSchema} (hpins : S.universalPins = [callerPin])
    {u a : EntityUID} {kind : String} (hsig : ∃ s ∈ S, s.action = a ∧ s.kind = kind)
    (he : e.principal = some u) {k : Nat} {p : TimePoint} (hp : σ[k]? = some p)
    (hb : ByCaller u a kind p) : S.Visible σ e k := by
  obtain ⟨ha, hkind, hpin⟩ := hb
  obtain ⟨s, hs, hsa, hsk⟩ := hsig
  refine Or.inr ⟨p, hp, ⟨⟨s, hs, hsa.trans ha.symm, hsk.trans hkind.symm⟩, ?_⟩⟩
  rw [hpins]
  intro pin hpin'
  simp only [List.mem_singleton] at hpin'
  subst hpin'
  exact ⟨_, hpin, by simp [callerPin, PinRef.toTerm, Term.eval?, Event.scopePath?, Event.scope,
    he]⟩

/-- A visible event, under a schema whose universal pin is the caller, logs the decision's
caller. -/
theorem caller_of_visible {S : EventSchema} (hpins : S.universalPins = [callerPin])
    {u : EntityUID} (he : e.principal = some u) {k : Nat} {p : TimePoint} (hp : σ[k]? = some p)
    (hv : S.Visible σ e k) :
    recordPath? p.event.logged ["callerPrincipal"] = some (.prim (.entityUID u)) := by
  rcases hv with h | ⟨p', hp', -, hmine⟩
  · rw [hpins] at h; cases h
  · rw [hp] at hp'
    cases hp'
    obtain ⟨w, hw, hev⟩ := hmine callerPin (by rw [hpins]; exact List.mem_singleton_self _)
    simp [callerPin, PinRef.toTerm, Term.eval?, Event.scopePath?, Event.scope, he] at hev
    exact hev ▸ hw

end

/-- In the default schema, every declared action has its `request`, `response`, and `error`
signatures. -/
theorem sig_defaultSchema {acts : List ActionDecl} {a : EntityUID}
    {ins : List (Cedar.Spec.Attr × Cedar.Validation.CedarType)} (ha : (a, ins) ∈ acts)
    {kind : String} (hk : kind = "request" ∨ kind = "response" ∨ kind = "error") :
    ∃ s ∈ defaultSchema true acts, s.action = a ∧ s.kind = kind := by
  simp only [defaultSchema, ↓reduceIte, List.mem_flatMap]
  rcases hk with rfl | rfl | rfl
  · exact ⟨_, ⟨_, ha, List.mem_cons_self ..⟩, rfl, rfl⟩
  · exact ⟨_, ⟨_, ha, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩, rfl, rfl⟩
  · exact ⟨_, ⟨_, ha, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))⟩, rfl, rfl⟩

end Dogwood.Examples
