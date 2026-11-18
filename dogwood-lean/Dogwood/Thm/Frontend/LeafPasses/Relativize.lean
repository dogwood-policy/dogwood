import Dogwood.Thm.Frontend.LeafPasses.Basic
import Dogwood.Thm.Pins

/-!
# Relativization: when it is the identity, what it keeps, and what μ means

* Without universal pins, relativization is the identity (`relativize_nil`); in particular when
  the specification's schema has no universal symmetric pin (`relativize_of_universalPins_nil`),
  in which case every timepoint is visible to the specification too
  (`visible_of_universalPins_nil`).
* It fails only on universal pins over a schema without events (`relativize_ok`).
* It keeps whether a condition implies mine (`impliesMine_relCond`), which its guards and its
  `since` fast path depend on.
* **μ is visibility** (`xsat_mu_iff_visible`): over a derived schema that agrees with the
  specification's and has a universal symmetric pin, μ holds at exactly the timepoints the
  specification makes visible.

These are the first steps of the relativization theorem (`LeafPasses.RelativizationTheorem`),
which `Dogwood.Thm.Frontend.Relativization` proves.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (EventSchema PinRef Event Trace TickRate TimePoint recordPath?)
open Dogwood.Spec.Temporal (Formula Aggregate Valuation ImplChoices Sat Denotes CVal TVal CmpOp ArgsMatch)

/-! ## Relativization -/

/-- **Relativization is the identity without universal pins.** -/
theorem relativize_nil (d : DerivedEventSchema) (c : Condition) : relativize d [] c = .ok c := rfl

/-- The crate's universal pins are empty when the specification's schema has none. -/
theorem universalPins_eq_nil {d : DerivedEventSchema} {S : EventSchema}
    (hS : d.toSpecUntyped = .ok S) (hu : Dogwood.Spec.EventSchema.universalPins S = []) :
    universalPins d = .ok [] := by
  unfold universalPins
  rw [hS]
  cases h : d.events with
  | nil => rfl
  | cons e es =>
    simp only [Except.mapError]
    show (Except.ok (List.filter _ e.pins) : Result (List Pin)) = .ok []
    congr 1
    apply List.filter_eq_nil_iff.mpr
    intro p _
    cases p.toSpec <;> simp [hu]

/-- **Relativization is the identity when the schema has no universal symmetric pin.** -/
theorem relativize_of_universalPins_nil {d : DerivedEventSchema} {S : EventSchema}
    (hS : d.toSpecUntyped = .ok S) (hu : Dogwood.Spec.EventSchema.universalPins S = [])
    {pins : List Pin} (hp : universalPins d = .ok pins) (c : Condition) :
    relativize d pins c = .ok c := by
  rw [universalPins_eq_nil hS hu] at hp
  cases hp
  rfl

/-- Relativization fails only on universal pins over a schema without events. -/
theorem relativize_ok {d : DerivedEventSchema} {pins : List Pin} (h : pins = [] ∨ d.events ≠ [])
    (c : Condition) : ∃ r, relativize d pins c = .ok r := by
  unfold relativize
  cases pins with
  | nil => exact ⟨c, rfl⟩
  | cons p ps =>
    cases he : d.events with
    | nil => simp_all
    | cons e es => exact ⟨_, rfl⟩

theorem impliesMine_mkAnds (sp : Span) (c : Condition) (cs : List Condition) :
    impliesMine (mkAnds sp (c :: cs)) = (c :: cs).any impliesMine := by
  simp only [mkAnds]
  induction cs generalizing c with
  | nil => simp
  | cons c' cs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [mkAnd, List.any_cons, impliesMine, Bool.or_assoc]

/-- `Functor.map` of the identity monad is application. -/
private theorem id_map_eq {α β : Type} (f : α → β) (x : Id α) :
    (f <$> x) = (show Id β from f x) := rfl

/-- `pure` of the identity monad is the identity. -/
private theorem id_pure_eq {α : Type} (a : α) : (pure a : Id α) = (show Id α from a) := rfl

/-- `bind` of the identity monad is application. -/
private theorem id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

/-- **Relativization keeps whether a condition implies mine**: the rewrite keeps the predicates,
conjunctions, disjunctions and `exists` at the top of a condition, and builds none from the other
forms. -/
theorem impliesMine_relCond (pre : String) (μ : Span → Condition) : (c : Condition) → (n : Nat) →
    impliesMine ((relCond pre μ c).run n).1 = impliesMine c
  | ⟨sp, .and l r⟩, n => by
    simp only [relCond, relKind, StateT.run_bind, StateT.run_pure, StateT.run_map, id_map_eq,
      id_bind_eq, id_pure_eq]
    simp [impliesMine, impliesMine_relCond pre μ l, impliesMine_relCond pre μ r]
  | ⟨sp, .or l r⟩, n => by
    simp only [relCond, relKind, StateT.run_bind, StateT.run_pure, StateT.run_map, id_map_eq,
      id_bind_eq, id_pure_eq]
    simp [impliesMine, impliesMine_relCond pre μ l, impliesMine_relCond pre μ r]
  | ⟨sp, .exists x c⟩, n => by
    simp only [relCond, relKind, StateT.run_bind, StateT.run_pure, StateT.run_map, id_map_eq,
      id_bind_eq, id_pure_eq]
    simp [impliesMine, impliesMine_relCond pre μ c]
  | ⟨sp, .not c⟩, n => by
    simp only [relCond, relKind, StateT.run_bind, StateT.run_pure, StateT.run_map, id_map_eq,
      id_bind_eq, id_pure_eq]; simp [impliesMine]
  | ⟨sp, .comparison op l r⟩, n => by
    simp only [relCond, relKind, StateT.run_bind, StateT.run_pure, StateT.run_map, id_map_eq,
      id_bind_eq, id_pure_eq]; simp [impliesMine]
  | ⟨sp, .formerly w c⟩, n => by
    simp only [relCond, relKind, StateT.run_bind, StateT.run_pure, StateT.run_map, id_map_eq,
      id_bind_eq, id_pure_eq]; simp [impliesMine]
  | ⟨sp, .previous w c⟩, n => by
    simp only [relCond, relKind, StateT.run_bind, StateT.run_pure, StateT.run_map, id_map_eq,
      id_bind_eq, id_pure_eq]
    simp only [encodePrevious, mkExistsTp]
    simp [impliesMine, impliesMine_mkAnds, mkTp, mkFormerly, mkCmp, mkNot]
  | ⟨sp, .since l w r⟩, n => by
    show impliesMine ((relKind pre μ sp (.since l w r)).run n).1 = false
    rcases l with ⟨lsp, lk⟩
    cases lk <;> simp only [relKind, relSinceGeneral, StateT.run_bind, StateT.run_pure,
        StateT.run_map, id_map_eq, id_bind_eq, id_pure_eq, encodeSince, mkExistsTp,
        mkExistsLong] <;> (try split) <;>
      simp [impliesMine, impliesMine_mkAnds, mkTp, mkFormerly, mkCmp, mkAggEq, mkNot,
        StateT.run_bind, StateT.run_pure, StateT.run_map, id_map_eq, id_bind_eq, id_pure_eq]
  | ⟨sp, .predicate _⟩, n => rfl
  | ⟨sp, .tp _⟩, n => rfl
  | ⟨sp, .call _⟩, n => rfl
  | ⟨sp, .sigilRef _ _⟩, n => rfl
  | ⟨sp, .refine b fs rsp⟩, n => by
    simp only [relCond, relKind, StateT.run_bind, StateT.run_pure, StateT.run_map, id_map_eq,
      id_bind_eq, id_pure_eq]; simp [impliesMine]

/-! ## μ is visibility -/

section
variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop} {ord : Bool}
  {dom : Domain}

/-- A left fold of `&&` holds when each of its conjuncts does. -/
theorem xsat_mkAnds (sp : Span) (v : Valuation) (k : Nat) (c : Condition) (cs : List Condition) :
    XSat ι rate σ e vis ord dom v k (mkAnds sp (c :: cs)) ↔
      ∀ c' ∈ c :: cs, XSat ι rate σ e vis ord dom v k c' := by
  simp only [mkAnds]
  induction cs generalizing c with
  | nil => simp
  | cons c' cs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp, mkAnd, XSat]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, h₂, h₃⟩
    · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₁, h₂⟩, h₃⟩

/-- A guarded body holds when the body does and, unless it implies mine, μ does too. -/
theorem xsat_guardMine (μ : Span → Condition) (b : Condition) (v : Valuation) (k : Nat) :
    XSat ι rate σ e vis ord dom v k (guardMine μ b) ↔
      (impliesMine b = false → XSat ι rate σ e vis ord dom v k (μ b.span)) ∧
        XSat ι rate σ e vis ord dom v k b := by
  unfold guardMine
  cases h : impliesMine b
  · simp [mkAnd, XSat]
  · simp

/-- A μ-branch holds at the events of its signature that agree with the current request on every
pin it carries. -/
theorem xsat_muBranch {pins : List Pin} {qs : List Dogwood.Spec.Pin} (hq : pins.mapM Pin.toSpec = .ok qs)
    (hpaths : ∀ p ∈ pins, fieldPathSplit (fieldPathJoin p.fieldPath) = p.fieldPath)
    {ev : DerivedEvent}
    (hname : entityUid ("::".intercalate ev.namespace) ev.action = .ok (actionUid ev.namespace ev.action))
    (sp : Span) (v : Valuation) (k : Nat) :
    XSat ι rate σ e vis ord dom v k (muBranch pins sp ev) ↔
      ∃ p, σ[k]? = some p ∧ p.event.action = actionUid ev.namespace ev.action ∧
        p.event.kind = ev.kind ∧ ∀ q ∈ qs, ∃ w, recordPath? p.event.logged q.field = some w ∧
          q.ref.toTerm.eval? e Valuation.empty = some (.val w) := by
  simp only [muBranch, XSat, hname, pinArgs_toSpecList pins hq hpaths, Except.ok.injEq,
    exists_eq_left', exists_and_left]
  refine exists_congr fun p => and_congr_right' (and_congr_right' (and_congr_right' ?_))
  simp only [ArgsMatch, List.forall_mem_map]
  refine forall_congr' fun q => imp_congr_right fun _ => exists_congr fun w => and_congr_right' ?_
  rw [Dogwood.Thm.PinRef.matches_toTerm, Dogwood.Thm.PinRef.eval_toTerm q.ref v Valuation.empty]

theorem mapM_filter {xs : List Pin} {ys : List Dogwood.Spec.Pin} (P : Dogwood.Spec.Pin → Bool)
    (h : xs.mapM Pin.toSpec = .ok ys) :
    (xs.filter fun p => match p.toSpec with | .ok q => P q | .error _ => false).mapM Pin.toSpec =
      .ok (ys.filter P) := by
  induction xs generalizing ys with
  | nil => simp only [List.mapM_nil, pure_eq_ok] at h; subst h; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    simp only [List.filter_cons, hy, List.filter_cons]
    cases hP : P y
    · simpa using ih hys
    · simp only [if_true, List.mapM_cons, hy, ih hys]; rfl

/-- The crate's universal pins are the specification's. -/
theorem universalPins_toSpec {d : DerivedEventSchema} {S₀ : EventSchema}
    (hS : d.events.mapM eventToSpec = .ok S₀) {pins : List Pin} (hp : universalPins d = .ok pins) :
    ∃ qs, pins.mapM Pin.toSpec = .ok qs ∧ (∀ q, q ∈ qs ↔ q ∈ Dogwood.Spec.EventSchema.universalPins S₀) ∧
      ∀ p ∈ pins, ∃ ev ∈ d.events, p ∈ ev.pins := by
  unfold universalPins at hp
  rw [toSpecUntyped_eq, hS] at hp
  cases hev : d.events with
  | nil =>
    rw [hev] at hS hp
    simp only [List.mapM_nil, pure_eq_ok] at hS; subst hS
    simp only [Except.mapError, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hp
    subst hp
    exact ⟨[], rfl, by simp [Dogwood.Spec.EventSchema.universalPins], by simp⟩
  | cons e₀ es =>
    rw [hev] at hS hp
    simp only [Except.mapError, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hp
    subst hp
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at hS
    obtain ⟨s₀, hs₀, S', _, rfl⟩ := hS
    simp only [eventToSpec, bind_eq_ok, pure_eq_ok] at hs₀
    obtain ⟨qs₀, hqs₀, rfl⟩ := hs₀
    refine ⟨_, mapM_filter _ hqs₀, fun q => ?_, fun p hp => ⟨e₀, by simp, (List.mem_filter.mp hp).1⟩⟩
    simp only [List.mem_filter, List.contains_iff_mem]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      simp only [Dogwood.Spec.EventSchema.universalPins, List.mem_filter] at h
      exact h.1

theorem declared_iff {d : DerivedEventSchema} {S₀ : EventSchema} (hS : d.events.mapM eventToSpec = .ok S₀)
    (a : Cedar.Spec.EntityUID) (k : String) :
    (∃ s ∈ S₀, s.action = a ∧ s.kind = k) ↔
      ∃ ev ∈ d.events, actionUid ev.namespace ev.action = a ∧ ev.kind = k := by
  generalize d.events = evs at hS
  induction evs generalizing S₀ with
  | nil => simp only [List.mapM_nil, pure_eq_ok] at hS; subst hS; simp
  | cons ev evs ih =>
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at hS
    obtain ⟨s, hs, S', hS', rfl⟩ := hS
    simp only [eventToSpec, bind_eq_ok, pure_eq_ok] at hs
    obtain ⟨_, _, rfl⟩ := hs
    simp only [List.mem_cons, exists_eq_or_imp, ih hS']

/-- **μ holds exactly at the events that are mine.** Over a derived schema that agrees with the
specification's, the disjunction relativization builds for the crate's universal pins holds at a
timepoint exactly when its event is mine (`EventSchema.Mine`). -/
theorem xsat_mu_iff {d : DerivedEventSchema} {S : EventSchema} (h : Agrees d S) {pins : List Pin}
    (hp : universalPins d = .ok pins) {e₀ : DerivedEvent} {es : List DerivedEvent}
    (hev : d.events = e₀ :: es) (sp : Span) (v : Valuation) (k : Nat) :
    XSat ι rate σ e vis ord dom v k (mu pins e₀ es sp) ↔
      ∃ p, σ[k]? = some p ∧ EventSchema.Mine S e p.event := by
  have hS : d.events.mapM eventToSpec = .ok (strip S) := h.untyped
  obtain ⟨qs, hqs, hmem, hsub⟩ := universalPins_toSpec hS hp
  have hpaths : ∀ p ∈ pins, fieldPathSplit (fieldPathJoin p.fieldPath) = p.fieldPath := fun p hp' => by
    obtain ⟨ev, hev', hpe⟩ := hsub p hp'
    exact h.paths ev hev' p hpe
  have hbr : ∀ ev ∈ d.events, (XSat ι rate σ e vis ord dom v k (muBranch pins sp ev) ↔
      ∃ p, σ[k]? = some p ∧ p.event.action = actionUid ev.namespace ev.action ∧
        p.event.kind = ev.kind ∧ ∀ q ∈ qs, ∃ w, recordPath? p.event.logged q.field = some w ∧
          q.ref.toTerm.eval? e Valuation.empty = some (.val w)) :=
    fun ev hev' => xsat_muBranch hqs hpaths (h.names ev hev') sp v k
  unfold mu
  rw [balancedFold_any _ (XSat ι rate σ e vis ord dom v k) (fun a b => by simp only [XSat])]
  have hall : (∃ c ∈ muBranch pins sp e₀ :: es.map (muBranch pins sp),
      XSat ι rate σ e vis ord dom v k c) ↔
      ∃ ev ∈ d.events, XSat ι rate σ e vis ord dom v k (muBranch pins sp ev) := by
    rw [hev]
    constructor
    · rintro ⟨c, hc, hx⟩
      simp only [List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨ev, hev', rfl⟩
      · exact ⟨e₀, by simp, hx⟩
      · exact ⟨ev, by simp [hev'], hx⟩
    · rintro ⟨ev, hev', hx⟩
      exact ⟨_, by
        simp only [List.mem_cons, List.mem_map] at hev' ⊢
        rcases hev' with rfl | hev'
        · exact .inl rfl
        · exact .inr ⟨ev, hev', rfl⟩, hx⟩
  rw [hall]
  constructor
  · rintro ⟨ev, hev', hx⟩
    obtain ⟨p, hp', ha, hk, hq⟩ := (hbr ev hev').mp hx
    refine ⟨p, hp', ?_, fun q hq' => hq q ((hmem q).mpr (by rw [universalPins_strip]; exact hq'))⟩
    have := (declared_iff hS p.event.action p.event.kind).mpr ⟨ev, hev', ha.symm, hk.symm⟩
    obtain ⟨s, hs, hsa, hsk⟩ := this
    simp only [strip, List.mem_map] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    exact ⟨s', hs', hsa, hsk⟩
  · rintro ⟨p, hp', ⟨s, hs, hsa, hsk⟩, hpins⟩
    obtain ⟨ev, hev', ha, hk⟩ := (declared_iff hS p.event.action p.event.kind).mp
      ⟨{ s with fields := [] }, List.mem_map.mpr ⟨s, hs, rfl⟩, hsa, hsk⟩
    refine ⟨ev, hev', (hbr ev hev').mpr ⟨p, hp', ha.symm, hk.symm, fun q hq => ?_⟩⟩
    have := (hmem q).mp hq
    rw [universalPins_strip] at this
    exact hpins q this

/-- **μ is visibility.** When the schema has a universal symmetric pin, μ holds at exactly the
timepoints the specification makes visible to the decision (`EventSchema.Visible`). -/
theorem xsat_mu_iff_visible {d : DerivedEventSchema} {S : EventSchema} (h : Agrees d S)
    (hne : Dogwood.Spec.EventSchema.universalPins S ≠ []) {pins : List Pin}
    (hp : universalPins d = .ok pins) {e₀ : DerivedEvent} {es : List DerivedEvent}
    (hev : d.events = e₀ :: es) (sp : Span) (v : Valuation) (k : Nat) :
    XSat ι rate σ e vis ord dom v k (mu pins e₀ es sp) ↔ S.Visible σ e k := by
  rw [xsat_mu_iff h hp hev, EventSchema.Visible]
  simp [hne]

end

end Dogwood.Thm.Frontend
