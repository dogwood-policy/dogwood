import Dogwood.Frontend.LeafPasses.Semantics

/-!
# Lemmas shared by the theorems about the leaf passes

The inversion of the projection's `Except` computations, the atomic terms, and the correspondence
between the crate's derived event schema and the specification's untyped signatures
(`DerivedEventSchema.toSpecUntyped`): the pins, their request-side terms, and the text form of a
pinned field's path.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (EventSchema)

theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β} :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [bind, Except.bind]

theorem pure_eq_ok {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-! ## Atomic terms -/

/-- A crate term that is neither an aggregate nor a compound. -/
def TermAtom : Surface.Temporal.Term → Prop
  | .agg _ | .arith _ _ _ => False
  | _ => True

/-- A specification term that is neither an aggregate nor a compound. -/
def SpecAtom : Dogwood.Spec.Temporal.Term → Prop
  | .agg _ | .arith _ _ _ => False
  | _ => True

theorem toSpec_atom {t : Surface.Temporal.Term} (ht : TermAtom t) {t' : Dogwood.Spec.Temporal.Term}
    (h : t.toSpec = .ok t') : SpecAtom t' := by
  cases t with
  | agg _ => exact absurd ht id
  | arith _ _ _ => exact absurd ht id
  | entity ty id =>
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, rfl⟩ := h; trivial
  | scopeField p =>
    unfold Surface.Temporal.Term.toSpec at h
    split at h <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] <;>
      (subst h; trivial)
  | _ => simp [Surface.Temporal.Term.toSpec, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h <;> (try subst h) <;> trivial

/-! ## Action names and pins -/

theorem entityUid_eid {ty id : String} {u : Cedar.Spec.EntityUID} (h : entityUid ty id = .ok u) :
    u.eid = id := by
  unfold entityUid at h
  simp only at h
  generalize (ty.splitOn "::").getLast? = o at h
  cases o with
  | some last => simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | none => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A derived event as the specification's untyped signature (`DerivedEventSchema.toSpecUntyped`). -/
def eventToSpec (e : DerivedEvent) : Except String Dogwood.Spec.EventSignature := do
  let pins ← e.pins.mapM Pin.toSpec
  return { action := actionUid e.namespace e.action, kind := e.kind, decision := e.decision, pins, fields := [] }

theorem toSpecUntyped_eq (d : DerivedEventSchema) : d.toSpecUntyped = d.events.mapM eventToSpec := rfl

theorem toSpecList_append : (xs ys : List NamedArg) →
    NamedArg.toSpecList (xs ++ ys) =
      (do let a ← NamedArg.toSpecList xs; let b ← NamedArg.toSpecList ys; pure (a ++ b))
  | [], ys => by
    simp only [List.nil_append, NamedArg.toSpecList]
    cases NamedArg.toSpecList ys <;> rfl
  | ⟨n, t⟩ :: xs, ys => by
    simp only [List.cons_append, NamedArg.toSpecList, toSpecList_append xs ys]
    cases t.toSpec <;> cases NamedArg.toSpecList xs <;> cases NamedArg.toSpecList ys <;> rfl

/-- The pin's request-side term projects to the specification pin's. -/
theorem pinTerm_toSpec {p : Pin} {q : Dogwood.Spec.Pin} (h : p.toSpec = .ok q) :
    (pinTerm p).toSpec = .ok q.ref.toTerm ∧ q.field = p.fieldPath := by
  obtain ⟨fp, cp, root⟩ := p
  cases root with
  | context =>
    simp only [Pin.toSpec, pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨rfl, rfl⟩
  | scope =>
    rcases cp with _ | ⟨hd, rest⟩
    · simp [Pin.toSpec, throw, throwThe, MonadExceptOf.throw] at h
    · by_cases h1 : hd = "principal"
      · subst h1
        simp only [Pin.toSpec, pure, Except.pure, Except.ok.injEq] at h; subst h
        exact ⟨rfl, rfl⟩
      · by_cases h2 : hd = "resource"
        · subst h2
          simp only [Pin.toSpec, pure, Except.pure, Except.ok.injEq] at h; subst h
          exact ⟨rfl, rfl⟩
        · simp [Pin.toSpec, h1, h2, throw, throwThe, MonadExceptOf.throw] at h

theorem pinArgs_toSpecList : (pins : List Pin) → {qs : List Dogwood.Spec.Pin} →
    pins.mapM Pin.toSpec = .ok qs →
    (∀ p ∈ pins, fieldPathSplit (fieldPathJoin p.fieldPath) = p.fieldPath) →
    NamedArg.toSpecList (pins.map pinArg) = .ok (qs.map fun q => (q.field, q.ref.toTerm))
  | [], qs, h, _ => by
    simp only [List.mapM_nil, pure_eq_ok] at h; subst h; rfl
  | p :: pins, qs, h, hp => by
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨q, hq, qs', hqs, rfl⟩ := h
    obtain ⟨ht, hf⟩ := pinTerm_toSpec hq
    simp only [List.map_cons, NamedArg.toSpecList, pinArg, ht,
      pinArgs_toSpecList pins hqs (fun p' hp' => hp p' (List.mem_cons_of_mem _ hp')),
      hp p (List.mem_cons_self), hf]
    rfl

/-- The signatures without their fields: what `toSpecUntyped` keeps of a specification schema. -/
def strip (S : EventSchema) : EventSchema := S.map fun s => { s with fields := [] }

theorem pinsOf_strip (S : EventSchema) (a : Cedar.Spec.EntityUID) (k : String) :
    (strip S).pinsOf a k = S.pinsOf a k := by
  simp only [strip, EventSchema.pinsOf, EventSchema.signature?, List.find?_map]
  have hc : ((fun s : Dogwood.Spec.EventSignature => s.action == a && s.kind == k) ∘
      fun s : Dogwood.Spec.EventSignature => { s with fields := [] }) =
      fun s => s.action == a && s.kind == k := rfl
  rw [hc]
  cases S.find? (fun s => s.action == a && s.kind == k) <;> rfl

theorem universalPins_strip (S : EventSchema) :
    Dogwood.Spec.EventSchema.universalPins (strip S) = Dogwood.Spec.EventSchema.universalPins S := by
  cases S with
  | nil => rfl
  | cons s rest =>
    simp only [strip, List.map_cons, Dogwood.Spec.EventSchema.universalPins, List.all_map]
    rfl

end Dogwood.Thm.Frontend
