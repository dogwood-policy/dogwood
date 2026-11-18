import Dogwood.Thm.Partition
import Dogwood.Thm.Pins
import Dogwood.Spec.Conformance

/-!
# The strict mirror rule: keys follow from conformance

Under the strict mirror rule (`Mirrored`), a field that mirrors the request is logged exactly when
the event carries the request-side value, and then holds it. So under a universal symmetric pin,
which every signature declares and pins, every conforming event carries each pin's request-side
value and logs it. This module proves what follows for implementations that key their history:

* `strict_universal`: a conforming event carries and logs each universal pin's request-side value;
* `fileable_of_strict`: so an implementation can file every conforming event under the key its
  own request side gives (`Fileable`);
* `mine_iff_mineReq`, `mine_iff_mineReq_of_strict`: visibility computed from the event's own
  request side (`MineReq`) is `EventSchema.Mine`, which compares the event's *logged* pin field;
* `partitionable_of_strict`: every trace of conforming events is `EventSchema.Partitionable`, so
  `Dogwood.Thm.leafHolds_iff_partition` applies to every log ingestion builds.

If the rule held vacuously when the request side did not resolve, none of these would hold: a
scope-less event could log any caller and enter that caller's history.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-- An implementation can file `ev` by its own request side: every universal pin's request-side
reference resolves on `ev`. -/
def Fileable (S : EventSchema) (ev : Event) : Prop :=
  ∀ p ∈ S.universalPins, ∃ w, p.ref.toTerm.eval? ev Valuation.empty = some (.val w)

/-- Visibility computed from the request side alone: `ev` is of a declared signature, and each
universal pin's request-side value on `ev` is the decision event `e`'s. -/
def MineReq (S : EventSchema) (e ev : Event) : Prop :=
  (∃ s ∈ S, s.action = ev.action ∧ s.kind = ev.kind) ∧
  ∀ p ∈ S.universalPins, ∃ w, p.ref.toTerm.eval? ev Valuation.empty = some (.val w) ∧
    p.ref.toTerm.eval? e Valuation.empty = some (.val w)

theorem mem_universalPins_symmetric {S : EventSchema} {p : Pin} (h : p ∈ S.universalPins) :
    EventSchema.Pin.isSymmetric p = true := by
  cases S with
  | nil => simp [EventSchema.universalPins] at h
  | cons s rest =>
    simp only [EventSchema.universalPins, List.mem_filter, Bool.and_eq_true] at h
    exact h.2.1

/-- A pin's request-side reference denotes a Cedar value or nothing, never a timepoint. -/
theorem pinRef_eval_val (r : PinRef) (e : Event) :
    ∀ x, r.toTerm.eval? e Valuation.empty = some x → ∃ w, x = .val w := by
  intro x hx
  cases r with
  | scope root path =>
    simp only [PinRef.toTerm, Term.eval?, Option.map_eq_some_iff] at hx
    obtain ⟨w, _, rfl⟩ := hx; exact ⟨w, rfl⟩
  | context path =>
    simp only [PinRef.toTerm, Term.eval?, Option.map_eq_some_iff] at hx
    obtain ⟨w, _, rfl⟩ := hx; exact ⟨w, rfl⟩

theorem signature?_mem {S : EventSchema} {a : Cedar.Spec.EntityUID} {k : String}
    {sig : EventSignature} (h : S.signature? a k = some sig) :
    sig ∈ S ∧ sig.action = a ∧ sig.kind = k := by
  unfold EventSchema.signature? at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp.1, hp.2⟩

/-- A universal pin is one of the mirrored fields of every signature of the schema. -/
theorem mem_mirrors_of_universal {S : EventSchema} {sig : EventSignature} (hsig : sig ∈ S)
    {p : Pin} (hp : p ∈ S.universalPins) : (p.field, p.ref) ∈ sig.mirrors := by
  unfold EventSignature.mirrors
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  exact List.mem_map.mpr
    ⟨p, List.mem_filter.mpr ⟨mem_universalPins hp sig hsig, mem_universalPins_symmetric hp⟩, rfl⟩

/-- **A conforming event carries its key.** Under the strict mirror rule, a conforming event's
request side resolves for each universal pin, and the event logs that value at the pinned
field. -/
theorem strict_universal {A : Cedar.Validation.Schema} {S : EventSchema} {ev : Event}
    (hc : ev.Conforms A S) {p : Pin} (hp : p ∈ S.universalPins) :
    ∃ w, p.ref.toTerm.eval? ev Valuation.empty = some (.val w) ∧
      recordPath? ev.logged p.field = some w := by
  unfold Event.Conforms at hc
  split at hc
  · rename_i sig hsig
    obtain ⟨hsigmem, _, _⟩ := signature?_mem hsig
    have hpin := hc.pinned p (mem_universalPins hp sig hsigmem)
    have hmir := hc.mirrored (p.field, p.ref) (mem_mirrors_of_universal hsigmem hp)
    unfold Mirrored at hmir
    cases hr : p.ref.toTerm.eval? ev Valuation.empty with
    | none => simp only [hr] at hmir; rw [hmir] at hpin; cases hpin
    | some x =>
      obtain ⟨w, rfl⟩ := pinRef_eval_val p.ref ev x hr
      simp only [hr] at hmir
      exact ⟨w, rfl, hmir⟩
  · exact hc.elim

/-- **Every conforming event can be filed by its own request side.** -/
theorem fileable_of_strict {A : Cedar.Validation.Schema} {S : EventSchema} {ev : Event}
    (hc : ev.Conforms A S) : Fileable S ev := fun _ hp =>
  let ⟨w, hw, _⟩ := strict_universal hc hp; ⟨w, hw⟩

/-- **Where the two filings agree.** On an event that mirrors every universal pin and carries
each one's request-side value, visibility from the request side is `Mine`. -/
theorem mine_iff_mineReq {S : EventSchema} {e ev : Event}
    (hmir : ∀ p ∈ S.universalPins, Mirrored ev (p.field, p.ref))
    (hfile : Fileable S ev) :
    S.Mine e ev ↔ MineReq S e ev := by
  unfold EventSchema.Mine MineReq
  refine and_congr Iff.rfl (forall₂_congr fun p hp => ?_)
  obtain ⟨w, hw⟩ := hfile p hp
  have hm := hmir p hp
  unfold Mirrored at hm
  rw [hw] at hm
  constructor
  · rintro ⟨w', hl, he⟩
    rw [hm] at hl; cases hl
    exact ⟨w, hw, he⟩
  · rintro ⟨w', hr, he⟩
    rw [hw] at hr; cases hr
    exact ⟨w, hm, he⟩

/-- **The two filings agree on every conforming event**: keying an event by its own request side
decides visibility exactly as `Mine` does. -/
theorem mine_iff_mineReq_of_strict {A : Cedar.Validation.Schema} {S : EventSchema} {e ev : Event}
    (hc : ev.Conforms A S) : S.Mine e ev ↔ MineReq S e ev := by
  refine mine_iff_mineReq (fun p hp => ?_) (fileable_of_strict hc)
  obtain ⟨w, hw, hl⟩ := strict_universal hc hp
  unfold Mirrored; rw [hw]; exact hl

/-- **`Partitionable` follows from conformance.** Every trace of conforming events suits
partitioned evaluation: every event, decision or not, is of a declared signature and logs each
universal pin's request-side value. -/
theorem partitionable_of_strict {A : Cedar.Validation.Schema} {S : EventSchema} {σ : Trace}
    (h : ∀ p ∈ σ, p.event.Conforms A S) : S.Partitionable σ where
  declared k p hk := by
    have hc := h p (List.mem_of_getElem? hk)
    unfold Event.Conforms at hc
    split at hc
    · rename_i sig hsig
      obtain ⟨hm, ha, hkd⟩ := signature?_mem hsig
      exact ⟨sig, hm, ha, hkd⟩
    · exact hc.elim
  logged k p hk pin hpin := by
    obtain ⟨w, _, hl⟩ := strict_universal (h p (List.mem_of_getElem? hk)) hpin
    rw [hl]; rfl
  symmetric _ p hk _ pin hpin := by
    obtain ⟨w, hw, hl⟩ := strict_universal (h p (List.mem_of_getElem? hk)) hpin
    rw [hl, hw]; rfl

/-- `partitionable_of_strict`, under the name of what it assumes. -/
theorem partitionable_of_conforms {A : Cedar.Validation.Schema} {S : EventSchema} {σ : Trace}
    (h : ∀ p ∈ σ, p.event.Conforms A S) : S.Partitionable σ :=
  partitionable_of_strict h

end Dogwood.Thm
