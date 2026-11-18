import Dogwood.Thm.Temporal
import Dogwood.Spec.Decision

/-!
# Pins

* **A pin cannot be bypassed** (`pin_enforced`): whenever a predicate holds
  after pin injection, the matched event's pinned fields hold the pins'
  request-side values — whatever the author wrote for those fields.
* **A pinned predicate matches only the current key's events**
  (`pinned_pred_mine`): under a universal symmetric pin, an injected
  predicate for a declared event can only be satisfied at a timepoint whose
  event is *mine*.
* **Pin injection is idempotent** (`sat_injectPins_idem`): injecting a
  schema's pins twice means the same as injecting them once, so it does not
  matter whether a leaf is supplied as authored or already pinned.
* As a consequence, for `formerly` over such a predicate the key-local and
  global readings coincide (`formerly_pinned_local_iff_global`) — the first
  instance of the guide's claim that key-local semantics changes the meaning
  of `previous` and of a positive `since` left, and of nothing else.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

theorem PinRef.eval_toTerm (r : PinRef) (v v' : Valuation) :
    r.toTerm.eval? e v = r.toTerm.eval? e v' := by
  cases r <;> rfl

theorem PinRef.matches_toTerm (r : PinRef) (v : Valuation) (w : Cedar.Spec.Value) :
    r.toTerm.Matches e v w ↔ r.toTerm.eval? e v = some (.val w) := by
  cases r <;> rfl

theorem injectPins_pred (S : EventSchema) (a : Cedar.Spec.EntityUID) (k : String)
    (args : List (Path × Term)) :
    (Formula.pred a k args).injectPins S =
      .pred a k (args ++ (S.pinsOf a k).map fun p => (p.field, p.ref.toTerm)) := by
  simp [Formula.injectPins]

/-- **A pin cannot be bypassed.** -/
theorem pin_enforced {S : EventSchema} {a : Cedar.Spec.EntityUID} {k : String}
    {args : List (Path × Term)} {v : Valuation} {j : Nat}
    (h : Sat ι rate σ e vis v j ((Formula.pred a k args).injectPins S)) :
    ∃ p, σ[j]? = some p ∧ ∀ pin ∈ S.pinsOf a k, ∃ w,
      recordPath? p.event.logged pin.field = some w ∧ pin.ref.toTerm.eval? e v = some (.val w) := by
  rw [injectPins_pred] at h
  obtain ⟨p, hp, _, _, hargs⟩ := h
  refine ⟨p, hp, fun pin hpin => ?_⟩
  obtain ⟨w, hw, hm⟩ := hargs (pin.field, pin.ref.toTerm)
    (List.mem_append_right _ (List.mem_map.mpr ⟨pin, hpin, rfl⟩))
  exact ⟨w, hw, (PinRef.matches_toTerm pin.ref v w).mp hm⟩

theorem mem_universalPins {S : EventSchema} {pin : Pin} (h : pin ∈ S.universalPins) :
    ∀ s ∈ S, pin ∈ s.pins := by
  cases S with
  | nil => simp [EventSchema.universalPins] at h
  | cons s₀ rest =>
    simp only [EventSchema.universalPins, List.mem_filter, Bool.and_eq_true, List.all_eq_true,
      List.contains_iff_mem] at h
    obtain ⟨h₀, _, hrest⟩ := h
    intro s hs
    cases List.mem_cons.mp hs with
    | inl hs => exact hs ▸ h₀
    | inr hs => exact hrest s hs

theorem universalPins_subset_pinsOf {S : EventSchema} {a : Cedar.Spec.EntityUID} {k : String}
    (hsig : ∃ s ∈ S, s.action = a ∧ s.kind = k) {pin : Pin} (h : pin ∈ S.universalPins) :
    pin ∈ S.pinsOf a k := by
  unfold EventSchema.pinsOf EventSchema.signature?
  cases hfind : S.find? (fun s => s.action == a && s.kind == k) with
  | none =>
    obtain ⟨s, hs, ha, hk⟩ := hsig
    have := List.find?_eq_none.mp hfind s hs
    simp [ha, hk] at this
  | some s => exact mem_universalPins h s (List.mem_of_find?_eq_some hfind)

/-- **A pinned predicate matches only the current key's events.** -/
theorem pinned_pred_mine {S : EventSchema} {a : Cedar.Spec.EntityUID} {k : String}
    {args : List (Path × Term)} {v : Valuation} {j : Nat}
    (hsig : ∃ s ∈ S, s.action = a ∧ s.kind = k)
    (h : Sat ι rate σ e vis v j ((Formula.pred a k args).injectPins S)) :
    ∃ p, σ[j]? = some p ∧ EventSchema.Mine S e p.event := by
  obtain ⟨p, hp, hpins⟩ := pin_enforced h
  rw [injectPins_pred] at h
  obtain ⟨p', hp', ha, hk, _⟩ := h
  rw [hp] at hp'
  cases hp'
  refine ⟨p, hp, ?_, fun pin hpin => ?_⟩
  · obtain ⟨s, hs, hsa, hsk⟩ := hsig
    exact ⟨s, hs, hsa.trans ha.symm, hsk.trans hk.symm⟩
  · obtain ⟨w, hw, he⟩ := hpins pin (universalPins_subset_pinsOf hsig hpin)
    exact ⟨w, hw, (PinRef.eval_toTerm pin.ref Valuation.empty v).trans he⟩

/-- `formerly` over a pinned predicate for a declared event means the same
under the key-local and the global reading. -/
theorem formerly_pinned_local_iff_global {S : EventSchema} {a : Cedar.Spec.EntityUID}
    {k : String} {args : List (Path × Term)} {v : Valuation} {j : Nat} {w : Window}
    (hsig : ∃ s ∈ S, s.action = a ∧ s.kind = k) :
    Sat ι rate σ e (S.Visible σ e) v j (.formerly w ((Formula.pred a k args).injectPins S)) ↔
    Sat ι rate σ e (fun _ => True) v j (.formerly w ((Formula.pred a k args).injectPins S)) := by
  -- A predicate's satisfaction does not depend on visibility.
  have hpred : ∀ vis₁ vis₂ i, Sat ι rate σ e vis₁ v i ((Formula.pred a k args).injectPins S) ↔
      Sat ι rate σ e vis₂ v i ((Formula.pred a k args).injectPins S) := by
    intro vis₁ vis₂ i
    simp only [injectPins_pred, Sat]
  simp only [Sat]
  constructor
  · rintro ⟨i, hi, _, hw, hs⟩
    exact ⟨i, hi, trivial, hw, (hpred _ _ i).mp hs⟩
  · rintro ⟨i, hi, _, hw, hs⟩
    have hs' := (hpred (fun _ => True) (S.Visible σ e) i).mp hs
    obtain ⟨p, hp, hmine⟩ := pinned_pred_mine hsig hs'
    exact ⟨i, hi, Or.inr ⟨p, hp, hmine⟩, hw, hs'⟩

theorem argsMatch_congr {v : Valuation} {ev : Event} {l₁ l₂ : List (Path × Term)}
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : ArgsMatch e v ev l₁ ↔ ArgsMatch e v ev l₂ :=
  ⟨fun hm a ha => hm a ((h a).mpr ha), fun hm a ha => hm a ((h a).mp ha)⟩

section

variable (S : EventSchema)

mutual

/-- **Pin injection is idempotent.** -/
theorem sat_injectPins_idem : (φ : Formula) → (v : Valuation) → (j : Nat) →
    (Sat ι rate σ e vis v j ((φ.injectPins S).injectPins S) ↔ Sat ι rate σ e vis v j (φ.injectPins S))
  | .and φ ψ, _, _ => by
    simp only [Formula.injectPins, Sat, sat_injectPins_idem φ, sat_injectPins_idem ψ]
  | .not φ, _, _ => by simp only [Formula.injectPins, Sat, sat_injectPins_idem φ]
  | .formerly _ φ, _, _ => by simp only [Formula.injectPins, Sat, sat_injectPins_idem φ]
  | .previous _ φ, _, _ => by simp only [Formula.injectPins, Sat, sat_injectPins_idem φ]
  | .since φ _ ψ, _, _ => by
    simp only [Formula.injectPins, Sat, sat_injectPins_idem φ, sat_injectPins_idem ψ]
  | .pred a k args, v, j => by
    simp only [Formula.injectPins, Sat]
    refine exists_congr fun p => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => argsMatch_congr fun x => ?_
    simp only [List.mem_append]
    exact ⟨fun h => h.elim id Or.inr, Or.inl⟩
  | .cmp _ l r, _, _ => by
    simp only [Formula.injectPins, Sat, denotes_injectPins_idem l, denotes_injectPins_idem r]
  | .exist _ φ, _, _ => by simp only [Formula.injectPins, Sat, sat_injectPins_idem φ]
  | .tp _, _, _ => by simp only [Formula.injectPins]

theorem denotes_injectPins_idem : (t : Term) → (v : Valuation) → (j : Nat) → (c : CVal) →
    (Denotes ι rate σ e vis v j ((t.injectPins S).injectPins S) c ↔
      Denotes ι rate σ e vis v j (t.injectPins S) c)
  | .agg a, _, _, _ => by simp only [Term.injectPins, Denotes, total_injectPins_idem a]
  | .arith _ l r, _, _, _ => by
    simp only [Term.injectPins, Denotes, denotes_injectPins_idem l, denotes_injectPins_idem r]
  | .entity _, _, _, _ => by simp only [Term.injectPins]
  | .long _, _, _, _ => by simp only [Term.injectPins]
  | .decimal _, _, _, _ => by simp only [Term.injectPins]
  | .string _, _, _, _ => by simp only [Term.injectPins]
  | .bool _, _, _, _ => by simp only [Term.injectPins]
  | .context _, _, _, _ => by simp only [Term.injectPins]
  | .scope _ _, _, _, _ => by simp only [Term.injectPins]
  | .var _, _, _, _ => by simp only [Term.injectPins]
  | .wildcard, _, _, _ => by simp only [Term.injectPins]

theorem total_injectPins_idem : (a : Aggregate) → (v : Valuation) → (j : Nat) → (n : Int) →
    (Total ι rate σ e vis v j ((a.injectPins S).injectPins S) n ↔
      Total ι rate σ e vis v j (a.injectPins S) n)
  | .count _ body, _, _, _ => by
    simp only [Aggregate.injectPins, Total, sat_injectPins_idem body]
  | .sum _ _ body, _, _, _ => by
    simp only [Aggregate.injectPins, Total, sat_injectPins_idem body]

end

end

end Dogwood.Thm
