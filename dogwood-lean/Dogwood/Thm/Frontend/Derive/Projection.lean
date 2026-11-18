import Dogwood.Thm.Frontend.Derive.Fields
import Dogwood.Frontend.Conformance

/-!
# The derived schema and its projection to the specification

The specification starts from the derived event schema as `Dogwood.Spec.EventSchema`, the
projection `typedSignatures` makes of the crate's (`Conformance.lean`). This module shows that
the derived schema is well-formed in the specification's sense, and that what the frontend reads
off it agrees with what the specification reads off its projection:

* **pins name declared fields** (`typed_pin_declared`), and **each signature's fields are
  distinct** (`typed_fields_nodup`);
* the **universal symmetric pins** (`universalPins_toSpec`): the frontend's partition keys
  project to the specification's `EventSchema.universalPins` of the projection;
* the **decision kinds** (`decisionKinds_toSpec`): a kind is one of the frontend's decision
  kinds exactly when the specification's `isDecisionKind` holds of it in the projection, and
  exactly when the DSL declares it a decision kind and the action schema declares an action
  (`derive_decisionKinds`).
-/

namespace Dogwood.Thm.Frontend.Derivation

open Dogwood.Frontend Dogwood.Frontend.Derive Dogwood.Frontend.CedarSchema
open Dogwood.Frontend.EventSchemaDsl

/-! ## One signature -/

theorem Pin.toSpec_field {p : Pin} {q : Dogwood.Spec.Pin} (h : p.toSpec = .ok q) :
    q.field = p.fieldPath := by
  unfold Pin.toSpec at h
  split at h <;> first
    | (simp [pure, Except.pure] at h; subst h; rfl)
    | (simp [throw, throwThe, MonadExceptOf.throw] at h)

/-- Elementwise results of `mapM`. -/
theorem mapM_forall₂ {α β ε : Type} {g : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM g = .ok ys) : List.Forall₂ (fun x y => g x = .ok y) xs ys :=
  List.mapM_ok_iff_forall₂.mp h

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {fa : α → γ} {fb : β → γ}
    (hR : ∀ a b, R a b → fb b = fa a) {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    ys.map fb = xs.map fa := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hR _ _ hab, ih]

/-- What the projection of one signature keeps: its action, kind, decision flag, pins (each the
specification's), and its fields' paths. -/
theorem EventSignature.toSpec_ok {A : Cedar.Validation.Schema} {s : EventSignature}
    {s' : Dogwood.Spec.EventSignature} (h : s.toSpec A = .ok s') :
    s'.action = actionUid s.namespace s.action ∧ s'.kind = s.kind ∧ s'.decision = s.decision ∧
      s.pins.mapM Pin.toSpec = .ok s'.pins ∧ s'.fields.map (·.path) = s.fields.map (·.1) := by
  unfold EventSignature.toSpec at h
  simp only [bind, Except.bind] at h
  cases hp : s.pins.mapM Pin.toSpec with
  | error _ => simp [hp] at h
  | ok pins =>
    simp only [hp] at h
    split at h
    · simp at h
    · rename_i fields hf
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      refine forall₂_map_eq ?_ (mapM_forall₂ hf)
      rintro ⟨path, fty⟩ fd hg
      simp only at hg
      split at hg
      · simp [pure, Except.pure] at hg; subst hg; rfl
      · split at hg
        · split at hg
          · simp at hg
          · simp [pure, Except.pure] at hg; subst hg; rfl
        · split at hg
          · simp at hg
          · simp [pure, Except.pure] at hg; subst hg; rfl

/-- `Forall₂` over a mapped list, as a relation on the unmapped elements. -/
theorem forall₂_of_map_left {α β γ : Type} {R : β → γ → Prop} {g : α → β} :
    ∀ {xs : List α} {ys : List γ}, List.Forall₂ R (xs.map g) ys →
      List.Forall₂ (fun a c => R (g a) c) xs ys
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    cases h with
    | cons hxy hrest => exact .cons hxy (forall₂_of_map_left hrest)

/-- The signatures of the projection, from the derived events. -/
theorem typedSignatures_forall₂ {d : DerivedEventSchema} {A : Cedar.Validation.Schema}
    {S : Dogwood.Spec.EventSchema} (h : typedSignatures d A = .ok S) :
    List.Forall₂ (fun e s => e.signature.toSpec A = .ok s) d.events S := by
  unfold typedSignatures at h
  exact forall₂_of_map_left (mapM_forall₂ h)

/-! ## Well-formedness in the specification's sense -/

variable {dsl : EventSchemaDsl.EventSchema} {f : Fragment} {d : DerivedEventSchema}
  {A : Cedar.Validation.Schema} {S : Dogwood.Spec.EventSchema}

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => simp at hy
  | cons hab _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨x, hx, hr⟩ := ih hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-- **Each signature of the projection has distinct fields.** -/
theorem typed_fields_nodup (h : derive dsl f = .ok d) (ht : typedSignatures d A = .ok S) :
    ∀ s ∈ S, (s.fields.map (·.path)).Nodup := by
  intro s hs
  obtain ⟨e, he, hspec⟩ := forall₂_mem_right (typedSignatures_forall₂ ht) hs
  rw [(EventSignature.toSpec_ok hspec).2.2.2.2]
  exact derive_leafFields_nodup h he

/-- **Every pin of the projection names a declared field of its signature**, when no record field
is pinned (the parser's guarantee). -/
theorem typed_pin_declared (h : derive dsl f = .ok d) (hpins : PinsOnLeaves dsl)
    (ht : typedSignatures d A = .ok S) :
    ∀ s ∈ S, ∀ p ∈ s.pins, (s.field? p.field).isSome := by
  intro s hs p hp
  obtain ⟨e, he, hspec⟩ := forall₂_mem_right (typedSignatures_forall₂ ht) hs
  obtain ⟨-, -, -, hpins', hpaths⟩ := EventSignature.toSpec_ok hspec
  obtain ⟨q, hq, hqp⟩ := forall₂_mem_right (mapM_forall₂ hpins') hp
  have hfield := Pin.toSpec_field hqp
  obtain ⟨t, ht'⟩ := derive_pin_declared h hpins he q hq
  have hmem : p.field ∈ s.fields.map (·.path) := by
    rw [hpaths, hfield]
    exact List.mem_map.mpr ⟨_, ht', rfl⟩
  obtain ⟨fd, hfd, hfdp⟩ := List.mem_map.mp hmem
  unfold Dogwood.Spec.EventSignature.field?
  exact List.find?_isSome.mpr ⟨fd, hfd, by rw [hfdp]; exact beq_self_eq_true _⟩

/-! ## Universal pins and decision kinds -/

/-- The untyped projection (`toSpecUntyped`), from the typed one: the same actions, kinds,
decision flags and pins. -/
theorem toSpecUntyped_of_typed (ht : typedSignatures d A = .ok S) :
    ∃ S₀, d.toSpecUntyped = .ok S₀ ∧ S₀.map (·.pins) = S.map (·.pins) ∧
      S₀.map (fun s => (s.kind, s.decision)) = S.map (fun s => (s.kind, s.decision)) := by
  have h2 := typedSignatures_forall₂ ht
  obtain ⟨events, mw⟩ := d
  simp only at h2
  unfold DerivedEventSchema.toSpecUntyped
  simp only
  clear ht
  induction h2 with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | @cons e s es ss hes _ ih =>
    obtain ⟨S₀, h₀, hp, hk⟩ := ih
    obtain ⟨-, hk', hd', hpins, -⟩ := EventSignature.toSpec_ok hes
    refine ⟨{ action := actionUid e.namespace e.action, kind := e.kind, decision := e.decision,
              pins := s.pins, fields := [] } :: S₀, ?_, ?_, ?_⟩
    · rw [List.mapM_cons, h₀]
      simp only [DerivedEvent.signature] at hpins
      simp [hpins, bind, Except.bind, pure, Except.pure]
    · simp [hp]
    · simp [hk, hk', hd', DerivedEvent.signature]

theorem all_contains_congr {r₁ r₂ : List Dogwood.Spec.EventSignature}
    (h : r₁.map (·.pins) = r₂.map (·.pins)) (p : Dogwood.Spec.Pin) :
    r₁.all (·.pins.contains p) = r₂.all (·.pins.contains p) := by
  induction r₁ generalizing r₂ with
  | nil => cases r₂ <;> simp_all
  | cons s₁ r₁ ih =>
    cases r₂ with
    | nil => simp at h
    | cons s₂ r₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.all_cons, h.1, ih h.2]

/-- The universal pins read only the signatures' pins. -/
theorem universalPins_congr {S₁ S₂ : Dogwood.Spec.EventSchema}
    (h : S₁.map (·.pins) = S₂.map (·.pins)) :
    Dogwood.Spec.EventSchema.universalPins S₁ = Dogwood.Spec.EventSchema.universalPins S₂ := by
  cases S₁ with
  | nil => cases S₂ <;> simp_all [Dogwood.Spec.EventSchema.universalPins]
  | cons s₁ r₁ =>
    cases S₂ with
    | nil => simp at h
    | cons s₂ r₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hp, hr⟩ := h
      simp only [Dogwood.Spec.EventSchema.universalPins, hp, all_contains_congr hr]

/-- The decision kinds read only the signatures' kinds and decision flags. -/
theorem isDecisionKind_congr {S₁ S₂ : Dogwood.Spec.EventSchema}
    (h : S₁.map (fun s => (s.kind, s.decision)) = S₂.map (fun s => (s.kind, s.decision)))
    (k : String) : S₁.isDecisionKind k = S₂.isDecisionKind k := by
  unfold Dogwood.Spec.EventSchema.isDecisionKind
  induction S₁ generalizing S₂ with
  | nil => cases S₂ <;> simp_all
  | cons s₁ r₁ ih =>
    cases S₂ with
    | nil => simp at h
    | cons s₂ r₂ =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      simp only [List.any_cons, h.1.1, h.1.2, ih h.2]

theorem mapM_filter {α β ε : Type} {g : α → Except ε β} {P : α → Bool} {Q : β → Bool}
    (hP : ∀ x y, g x = .ok y → P x = Q y) :
    ∀ {xs : List α} {ys : List β}, xs.mapM g = .ok ys → (xs.filter P).mapM g = .ok (ys.filter Q)
  | [], ys, h => by simp [pure, Except.pure] at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hx : g x with
    | error _ => simp [hx] at h
    | ok y =>
      cases hxs : xs.mapM g with
      | error _ => simp [hx, hxs] at h
      | ok ys' =>
        simp only [hx, hxs, Except.ok.injEq] at h
        subst h
        have ih := mapM_filter hP hxs
        have hpq := hP x y hx
        by_cases hq : Q y
        · simp [hpq, hq, List.mapM_cons, hx, ih, bind, Except.bind, pure, Except.pure]
        · simp [hpq, hq, ih]

/-- **The universal pins commute with the projection**: the frontend's universal pins (the
partition keys) are, as the specification's pins, the specification's `universalPins` of the
projection. -/
theorem universalPins_toSpec (ht : typedSignatures d A = .ok S) :
    ∃ ps, universalPins d = .ok ps ∧
      ps.mapM Pin.toSpec = .ok (Dogwood.Spec.EventSchema.universalPins S) := by
  obtain ⟨S₀, h₀, hp, -⟩ := toSpecUntyped_of_typed ht
  have h2 := typedSignatures_forall₂ ht
  unfold universalPins
  simp only [h₀, Except.mapError, bind, Except.bind]
  rw [universalPins_congr hp]
  obtain ⟨events, mw⟩ := d
  simp only at h2 ⊢
  cases h2 with
  | nil => exact ⟨[], rfl, by simp [Dogwood.Spec.EventSchema.universalPins, pure, Except.pure]⟩
  | @cons e s es ss hes _ =>
    obtain ⟨-, -, -, hpins, -⟩ := EventSignature.toSpec_ok hes
    simp only [DerivedEvent.signature] at hpins
    refine ⟨_, rfl, ?_⟩
    rw [mapM_filter (Q := fun q => (Dogwood.Spec.EventSchema.universalPins (s :: ss)).contains q)
      (fun x y hxy => by simp [hxy]) hpins]
    congr 1
    simp only [Dogwood.Spec.EventSchema.universalPins]
    apply List.filter_congr
    intro q hq
    simp [List.mem_filter, hq, List.all_eq]

theorem mem_sortedSet {k : String} {xs : List String} :
    k ∈ ProviderDecls.sortedSet xs ↔ k ∈ xs := by
  simp [ProviderDecls.sortedSet, List.mem_eraseDups, List.mem_mergeSort]

/-- **The decision kinds commute with the projection**: a kind is a decision kind of the
frontend exactly when the specification's `isDecisionKind` holds of it in the projection. -/
theorem decisionKinds_toSpec (ht : typedSignatures d A = .ok S) :
    ∃ ks, decisionKinds d = .ok ks ∧ ∀ k, k ∈ ks ↔ S.isDecisionKind k = true := by
  obtain ⟨S₀, h₀, -, hk⟩ := toSpecUntyped_of_typed ht
  unfold decisionKinds
  simp only [h₀, Except.mapError, bind, Except.bind]
  refine ⟨_, rfl, fun k => ?_⟩
  rw [mem_sortedSet, List.mem_filter, ← isDecisionKind_congr hk]
  constructor
  · exact fun h => h.2
  · intro hdk
    refine ⟨?_, hdk⟩
    unfold Dogwood.Spec.EventSchema.isDecisionKind at hdk
    obtain ⟨s, hs, hsk⟩ := List.any_eq_true.mp hdk
    simp only [Bool.and_eq_true, beq_iff_eq] at hsk
    have hmem : (s.kind, s.decision) ∈ S₀.map (fun s => (s.kind, s.decision)) :=
      List.mem_map.mpr ⟨s, hs, rfl⟩
    have h2 := typedSignatures_forall₂ ht
    rw [hk] at hmem
    obtain ⟨s', hs', hss'⟩ := List.mem_map.mp hmem
    obtain ⟨e, he, hes⟩ := forall₂_mem_right h2 hs'
    obtain ⟨-, hke, -, -, -⟩ := EventSignature.toSpec_ok hes
    simp only [Prod.mk.injEq] at hss'
    exact List.mem_map.mpr ⟨e, he, by rw [← hsk.2, ← hss'.1, hke]; rfl⟩

/-- The decision kinds are the crate's: the kinds with a decision event. -/
theorem decisionKinds_iff {ks : List String} (h : decisionKinds d = .ok ks) (k : String) :
    k ∈ ks ↔ ∃ e ∈ d.events, e.decision = true ∧ e.kind = k := by
  unfold decisionKinds at h
  cases h₀ : d.toSpecUntyped with
  | error _ => simp [h₀, Except.mapError, bind, Except.bind] at h
  | ok S₀ =>
    simp only [h₀, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [mem_sortedSet, List.mem_filter]
    unfold DerivedEventSchema.toSpecUntyped at h₀
    have h2 := mapM_forall₂ h₀
    have hkd : S₀.map (fun s => (s.kind, s.decision)) =
        d.events.map (fun e => (e.kind, e.decision)) := by
      refine forall₂_map_eq ?_ h2
      intro e s hs
      simp only [bind, Except.bind] at hs
      split at hs
      · simp at hs
      · simp [pure, Except.pure] at hs; subst hs; rfl
    constructor
    · rintro ⟨hm, hdk⟩
      unfold Dogwood.Spec.EventSchema.isDecisionKind at hdk
      obtain ⟨s, hs, hsk⟩ := List.any_eq_true.mp hdk
      simp only [Bool.and_eq_true, beq_iff_eq] at hsk
      have hmem : (s.kind, s.decision) ∈ S₀.map (fun s => (s.kind, s.decision)) :=
        List.mem_map.mpr ⟨s, hs, rfl⟩
      rw [hkd] at hmem
      obtain ⟨e, he, hes⟩ := List.mem_map.mp hmem
      simp only [Prod.mk.injEq] at hes
      exact ⟨e, he, hes.2 ▸ hsk.1, hes.1 ▸ hsk.2⟩
    · rintro ⟨e, he, hd, rfl⟩
      refine ⟨List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
      unfold Dogwood.Spec.EventSchema.isDecisionKind
      have hmem : (e.kind, e.decision) ∈ S₀.map (fun s => (s.kind, s.decision)) := by
        rw [hkd]; exact List.mem_map.mpr ⟨e, he, rfl⟩
      obtain ⟨s, hs, hse⟩ := List.mem_map.mp hmem
      simp only [Prod.mk.injEq] at hse
      exact List.any_eq_true.mpr ⟨s, hs, by simp [hse.1, hse.2, hd]⟩

/-- **The derived decision kinds are the DSL's**: a kind is a decision kind of the derived schema
exactly when the action schema declares an action and the DSL declares the kind a decision
kind. -/
theorem derive_decisionKinds (h : derive dsl f = .ok d) {ks : List String}
    (hks : decisionKinds d = .ok ks) (k : String) :
    k ∈ ks ↔ (∃ ns nd, (ns, nd) ∈ f ∧ nd.actions ≠ []) ∧
      ∃ decl ∈ dsl.decls, decl.decision = true ∧ decl.kind = k := by
  rw [decisionKinds_iff hks]
  constructor
  · rintro ⟨e, he, hd, rfl⟩
    obtain ⟨ns, nd, hns, -, ⟨a, ha⟩, decl, hdecl, hk, hdec⟩ := derive_event_declared h he
    exact ⟨⟨ns, nd, hns, List.ne_nil_of_mem ha⟩, decl, hdecl, hdec ▸ hd, hk.symm⟩
  · rintro ⟨⟨ns, nd, hns, hne⟩, decl, hdecl, hd, rfl⟩
    obtain ⟨⟨id, a⟩, ha⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨e, he, hone⟩ := derive_event_complete h hns ha hdecl
    obtain ⟨-, -, hk, hdec, -⟩ := deriveOne_ok hone
    exact ⟨e, he, hdec ▸ hd, hk⟩

end Dogwood.Thm.Frontend.Derivation
