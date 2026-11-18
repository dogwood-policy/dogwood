import Dogwood.Thm.Frontend.Relativization.Congr
import Dogwood.Thm.Soundness
import Dogwood.Thm.Pins

/-!
# A condition that implies mine holds only at the key's events

The relativization rewrite guards a temporal body with μ unless the body *implies mine*
(`LeafPasses.impliesMine`): unless its positive structure has a predicate conjunct. That is sound
because, after pin injection, every predicate of a well-typed leaf names a declared signature and
carries the universal symmetric pins (`Formula.Pinned`, `pinned_injectPins`), so it matches only
events that are mine (`xsat_mine`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (Event Trace TickRate EventSchema PinRef recordPath?)
open Dogwood.Spec.Temporal (Valuation ImplChoices CVal TVal ArgsMatch Formula Aggregate TypingCtx
  Bindings)

mutual

/-- Every predicate of the condition names a declared signature and carries the universal
symmetric pins as arguments: what pin injection makes of a well-typed condition. -/
def _root_.Dogwood.Spec.Temporal.Formula.Pinned (S : EventSchema) : Formula → Prop
  | .and φ ψ => φ.Pinned S ∧ ψ.Pinned S
  | .not φ => φ.Pinned S
  | .formerly _ φ => φ.Pinned S
  | .previous _ φ => φ.Pinned S
  | .since φ _ ψ => φ.Pinned S ∧ ψ.Pinned S
  | .pred a k args => (∃ s ∈ S, s.action = a ∧ s.kind = k) ∧
      ∀ pin ∈ S.universalPins, (pin.field, pin.ref.toTerm) ∈ args
  | .cmp _ l r => l.Pinned S ∧ r.Pinned S
  | .exist _ φ => φ.Pinned S
  | .tp _ => True

def _root_.Dogwood.Spec.Temporal.Term.Pinned (S : EventSchema) : Dogwood.Spec.Temporal.Term → Prop
  | .agg a => a.Pinned S
  | .arith _ l r => l.Pinned S ∧ r.Pinned S
  | _ => True

def _root_.Dogwood.Spec.Temporal.Aggregate.Pinned (S : EventSchema) : Aggregate → Prop
  | .count _ body => body.Pinned S
  | .sum _ _ body => body.Pinned S

end

mutual

/-- **Pin injection pins a well-typed condition.** -/
theorem pinned_injectPins {C : TypingCtx} : {Γ : Bindings} → {φ : Formula} →
    Formula.WellTyped C Γ φ → (φ.injectPins C.events).Pinned C.events
  | _, _, .and h₁ h₂ => ⟨pinned_injectPins h₁, pinned_injectPins h₂⟩
  | _, .not φ, .not h => (pinned_injectPins h : (φ.injectPins C.events).Pinned C.events)
  | _, .formerly _ φ, .formerly _ h => (pinned_injectPins h : (φ.injectPins C.events).Pinned C.events)
  | _, .previous _ φ, .previous _ h => (pinned_injectPins h : (φ.injectPins C.events).Pinned C.events)
  | _, _, .since _ h₁ h₂ => ⟨pinned_injectPins h₁, pinned_injectPins h₂⟩
  | _, .pred a k args, .pred (sig := sig) hs _ _ => by
    have hdecl : ∃ s ∈ C.events, s.action = a ∧ s.kind = k := by
      refine ⟨sig, ?_, Dogwood.Thm.signature?_spec hs⟩
      unfold EventSchema.signature? at hs
      exact List.mem_of_find?_eq_some hs
    refine ⟨hdecl, fun pin hpin => List.mem_append_right _ (List.mem_map.mpr
      ⟨pin, Dogwood.Thm.universalPins_subset_pinsOf hdecl hpin, rfl⟩)⟩
  | _, _, .eq _ hl hr _ => ⟨term_pinned_injectPins hl, term_pinned_injectPins hr⟩
  | _, _, .ord _ hl hr => ⟨term_pinned_injectPins hl, term_pinned_injectPins hr⟩
  | _, .exist _ φ, .exist _ h => (pinned_injectPins h : (φ.injectPins C.events).Pinned C.events)
  | _, _, .tp _ => trivial

theorem term_pinned_injectPins {C : TypingCtx} : {Γ : Bindings} → {t : Dogwood.Spec.Temporal.Term} →
    {τ : Dogwood.Spec.Temporal.TType} → Dogwood.Spec.Temporal.Term.Typed C Γ t τ →
    (t.injectPins C.events).Pinned C.events
  | _, _, _, .entity _ => trivial
  | _, _, _, .long => trivial
  | _, _, _, .decimal _ => trivial
  | _, _, _, .string => trivial
  | _, _, _, .bool => trivial
  | _, _, _, .context _ _ => trivial
  | _, _, _, .scopeRoot => trivial
  | _, _, _, .scopeAttr _ _ _ => trivial
  | _, _, _, .var _ => trivial
  | _, .agg a, _, .agg h => (agg_pinned_injectPins h : (a.injectPins C.events).Pinned C.events)
  | _, _, _, .arith h₁ h₂ => ⟨term_pinned_injectPins h₁, term_pinned_injectPins h₂⟩

theorem agg_pinned_injectPins {C : TypingCtx} : {Γ : Bindings} → {a : Aggregate} →
    Dogwood.Spec.Temporal.Aggregate.Typed C Γ a → (a.injectPins C.events).Pinned C.events
  | _, .count _ b, .count _ h => (pinned_injectPins h : (b.injectPins C.events).Pinned C.events)
  | _, .sum _ _ b, .sum _ _ h => (pinned_injectPins h : (b.injectPins C.events).Pinned C.events)

end

section
variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}
  {ord : Bool} {dom : Domain} {S : EventSchema}

/-- **A condition that implies mine holds only at the key's events.** -/
theorem xsat_mine : (c : Condition) → impliesMine c = true → {ψ : Formula} → c.toFormula = .ok ψ →
    ψ.Pinned S → {v : Valuation} → {k : Nat} → XSat ι rate σ e vis ord dom v k c →
    ∃ p, σ[k]? = some p ∧ S.Mine e p.event
  | ⟨_, .predicate ⟨_, ns, a, kd, args⟩⟩, _, ψ, h, hp, v, k, hs => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨uid, hu, args', ha, rfl⟩ := h
    obtain ⟨hdecl, hpins⟩ := hp
    obtain ⟨uid', args'', hu', ha', p, hpk, hact, hkind, hmatch⟩ := hs
    rw [hu] at hu'; cases hu'
    rw [ha] at ha'; cases ha'
    refine ⟨p, hpk, ?_, fun pin hpin => ?_⟩
    · obtain ⟨s, hs, hsa, hsk⟩ := hdecl
      exact ⟨s, hs, hsa.trans hact.symm, hsk.trans hkind.symm⟩
    · obtain ⟨w, hw, hm⟩ := hmatch _ (hpins pin hpin)
      refine ⟨w, hw, ?_⟩
      rw [Dogwood.Thm.PinRef.matches_toTerm] at hm
      rw [Dogwood.Thm.PinRef.eval_toTerm pin.ref Valuation.empty v]
      exact hm
  | ⟨_, .and l r⟩, hm, ψ, h, hp, v, k, hs => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [impliesMine, Bool.or_eq_true] at hm
    rcases hm with hm | hm
    · exact xsat_mine l hm ha hp.1 hs.1
    · exact xsat_mine r hm hb hp.2 hs.2
  | ⟨_, .or _ _⟩, _, ψ, h, _, _, _, _ => by
    simp [Condition.toFormula, ConditionKind.toFormula] at h
  | ⟨_, .exists ⟨sl, ty⟩ b⟩, hm, ψ, h, hp, v, k, hs => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨x, _, a, ha, rfl⟩ := h
    simp only [impliesMine] at hm
    obtain ⟨_, _, w, _, hs⟩ := hs
    exact xsat_mine b hm ha hp hs
  | ⟨_, .not _⟩, hm, _, _, _, _, _, _ => by simp [impliesMine] at hm
  | ⟨_, .formerly _ _⟩, hm, _, _, _, _, _, _ => by simp [impliesMine] at hm
  | ⟨_, .previous _ _⟩, hm, _, _, _, _, _, _ => by simp [impliesMine] at hm
  | ⟨_, .since _ _ _⟩, hm, _, _, _, _, _, _ => by simp [impliesMine] at hm
  | ⟨_, .comparison _ _ _⟩, hm, _, _, _, _, _, _ => by simp [impliesMine] at hm
  | ⟨_, .tp _⟩, hm, _, _, _, _, _, _ => by simp [impliesMine] at hm
  | ⟨_, .call _⟩, hm, _, _, _, _, _, _ => by simp [impliesMine] at hm
  | ⟨_, .sigilRef _ _⟩, hm, _, _, _, _, _, _ => by simp [impliesMine] at hm
  | ⟨_, .refine _ _ _⟩, hm, _, _, _, _, _, _ => by simp [impliesMine] at hm

/-- A condition that implies mine holds only at visible timepoints. -/
theorem xsat_visible {c : Condition} (hm : impliesMine c = true) {ψ : Formula}
    (h : c.toFormula = .ok ψ) (hp : ψ.Pinned S) {v : Valuation} {k : Nat}
    (hs : XSat ι rate σ e vis ord dom v k c) : S.Visible σ e k := by
  obtain ⟨p, hp', hmine⟩ := xsat_mine c hm h hp hs
  exact Or.inr ⟨p, hp', hmine⟩

end

end Dogwood.Thm.Frontend
