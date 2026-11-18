import Dogwood.Thm.Frontend.Derive.Projection

/-!
# The default event schema

The crate's `configuration/event-schemas/pinned.dwschema`: under the default event schema, each
action has three kinds of event; a `request` is a decision event, a `response` and an `error` are
history events; every kind logs the action's inputs (a `response` also its outputs),
`callerPrincipal`, `callerResource`, `requestId` and `sessionId`, and declares the pin
`callerPrincipal = principal`. Derivation produces exactly that (`default_event`,
`default_complete`), so the universal symmetric pins are that one pin (`default_universalPins`,
`default_typed_universalPins`: key-local semantics by principal), and the only decision kind is
`request` (`default_decisionKinds`).
-/

namespace Dogwood.Thm.Frontend.Derivation

open Dogwood.Frontend Dogwood.Frontend.Derive Dogwood.Frontend.CedarSchema
open Dogwood.Frontend.EventSchemaDsl

/-- The default schema's pin, `pin callerPrincipal = principal`. -/
def callerPrincipalPin : Pin :=
  { fieldPath := ["callerPrincipal"], contextPath := ["principal"], root := .scope }

/-- The default schema's pin in the specification. -/
def callerPrincipalSpecPin : Dogwood.Spec.Pin := ⟨["callerPrincipal"], .scope .principal []⟩

/-- The `appliesTo` principal types of an action, as written. -/
def principalTypesOf (a : ActionDef) : List String := (a.appliesTo.map (·.principalTypes)).getD []

/-- The `appliesTo` resource types of an action, as written. -/
def resourceTypesOf (a : ActionDef) : List String := (a.appliesTo.map (·.resourceTypes)).getD []

/-- The field map of a default event on an action with these principal and resource types,
input group and, for a response, output group. -/
def defaultTree (ps rs : List String) (ins : List (String × DerivedFieldNode))
    (outs : Option (List (String × DerivedFieldNode))) : List (String × DerivedFieldNode) :=
  [("callerPrincipal", .leaf (.entityTypes ps)), ("callerResource", .leaf (.entityTypes rs)),
   ("input", .group ins)] ++
  (match outs with
   | some o => [("output", .group o)]
   | none => []) ++
  [("requestId", .leaf (.cedar "String")), ("sessionId", .leaf (.cedar "String"))]

theorem deriveSpecs_defaultFields {c : Ctx} {b : Bool} {acc : Acc}
    (h : deriveSpecs c [] (defaultFields b) ⟨[], [], []⟩ = .ok acc) :
    ∃ ins outs, contextSubrecord c.fragment c.action c.home "input" = .ok ins ∧
      (match b with
       | true => ∃ o, outs = some o ∧ contextSubrecord c.fragment c.action c.home "output" = .ok o
       | false => outs = none) ∧
      acc.fields = defaultTree c.principalTypes c.resourceTypes ins outs ∧
      acc.pins = [callerPrincipalPin] := by
  cases hi : contextSubrecord c.fragment c.action c.home "input" with
  | error _ =>
    cases b <;> simp [defaultFields, deriveSpecs, deriveSpec, hi, bind, Except.bind] at h
  | ok ins =>
    cases b with
    | false =>
      simp [defaultFields, deriveSpecs, deriveSpec, deriveType, hi, bind, Except.bind, pure,
        Except.pure, insertKey, hasKey] at h
      subst h
      exact ⟨ins, none, rfl, rfl, rfl, rfl⟩
    | true =>
      cases ho : contextSubrecord c.fragment c.action c.home "output" with
      | error _ =>
        simp [defaultFields, deriveSpecs, deriveSpec, hi, ho, bind, Except.bind, pure,
          Except.pure, insertKey, hasKey] at h
      | ok outs =>
        simp [defaultFields, deriveSpecs, deriveSpec, deriveType, hi, ho, bind, Except.bind, pure,
          Except.pure, insertKey, hasKey] at h
        subst h
        exact ⟨ins, some outs, rfl, ⟨outs, rfl, rfl⟩, rfl, rfl⟩

variable {f : Fragment} {d : DerivedEventSchema}

/-- **The default event schema derives to the schema `pinned.dwschema` declares**: each event
is a `request` (a decision event), a `response` or an `error` (history events) of a declared
action; it logs the action's inputs (a response also its outputs), `callerPrincipal` (an entity
of the action's principal types), `callerResource`, `requestId` and `sessionId`, and nothing
else; and its pins are `callerPrincipal = principal`. -/
theorem default_event (h : derive defaultEventSchema f = .ok d) {e : DerivedEvent}
    (he : e ∈ d.events) :
    ∃ ns nd a, (ns, nd) ∈ f ∧ (e.action, a) ∈ nd.actions ∧
      e.namespace = nsPath ns ++ ["Action"] ∧
      ((e.kind = "request" ∧ e.decision = true) ∨ (e.kind = "response" ∧ e.decision = false) ∨
        (e.kind = "error" ∧ e.decision = false)) ∧
      e.pins = [callerPrincipalPin] ∧
      ∃ ins outs, contextSubrecord f a ns "input" = .ok ins ∧
        (e.kind = "response" → ∃ o, outs = some o ∧ contextSubrecord f a ns "output" = .ok o) ∧
        (e.kind ≠ "response" → outs = none) ∧
        e.fields = defaultTree (principalTypesOf a) (resourceTypesOf a) ins outs := by
  obtain ⟨ns, nd, hns, id, a, ha, decl, hdecl, hone⟩ := derive_event_mem h he
  obtain ⟨hn, hid, hk, hdec, acc, hs, hf, hp⟩ := deriveOne_ok hone
  subst hid
  refine ⟨ns, nd, a, hns, ha, hn, ?_⟩
  simp only [defaultEventSchema, List.mem_cons, List.not_mem_nil, or_false] at hdecl
  rcases hdecl with rfl | rfl | rfl
  · obtain ⟨ins, outs, hi, ho, hfs, hps⟩ := deriveSpecs_defaultFields hs
    refine ⟨.inl ⟨hk, hdec⟩, hp.trans hps, ins, outs, hi, fun h' => by simp [hk] at h',
      fun _ => ho, hf.trans hfs⟩
  · obtain ⟨ins, outs, hi, ho, hfs, hps⟩ := deriveSpecs_defaultFields hs
    refine ⟨.inr (.inl ⟨hk, hdec⟩), hp.trans hps, ins, outs, hi, fun _ => ho,
      fun h' => absurd hk h', hf.trans hfs⟩
  · obtain ⟨ins, outs, hi, ho, hfs, hps⟩ := deriveSpecs_defaultFields hs
    refine ⟨.inr (.inr ⟨hk, hdec⟩), hp.trans hps, ins, outs, hi, fun h' => by simp [hk] at h',
      fun _ => ho, hf.trans hfs⟩

/-- **Each action has the three kinds of event** under the default event schema. -/
theorem default_complete (h : derive defaultEventSchema f = .ok d) {ns : Option String}
    {nd : NamespaceDef} (hns : (ns, nd) ∈ f) {id : String} {a : ActionDef}
    (ha : (id, a) ∈ nd.actions) :
    ∀ k ∈ ["request", "response", "error"], ∃ e ∈ d.events, e.action = id ∧ e.kind = k ∧
      e.namespace = nsPath ns ++ ["Action"] := by
  intro k hk
  have hdecl : ∃ decl ∈ defaultEventSchema.decls, decl.kind = k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> simp [defaultEventSchema]
  obtain ⟨decl, hdecl, rfl⟩ := hdecl
  obtain ⟨e, he, hone⟩ := derive_event_complete h hns ha hdecl
  obtain ⟨hn, hid, hk', -, -⟩ := deriveOne_ok hone
  exact ⟨e, he, hid, hk', hn⟩

theorem callerPrincipalPin_toSpec : callerPrincipalPin.toSpec = .ok callerPrincipalSpecPin := by
  simp [callerPrincipalPin, callerPrincipalSpecPin, Pin.toSpec, pure, Except.pure]

/-- Under the default event schema, the projection's signatures each pin `callerPrincipal`. -/
theorem default_typed_pins (h : derive defaultEventSchema f = .ok d)
    {A : Cedar.Validation.Schema} {S : Dogwood.Spec.EventSchema}
    (ht : typedSignatures d A = .ok S) : ∀ s ∈ S, s.pins = [callerPrincipalSpecPin] := by
  intro s hs
  obtain ⟨e, he, hspec⟩ := forall₂_mem_right (typedSignatures_forall₂ ht) hs
  obtain ⟨-, -, -, hpins, -⟩ := EventSignature.toSpec_ok hspec
  obtain ⟨-, -, -, -, -, -, -, hp, -⟩ := default_event h he
  simp only [DerivedEvent.signature, hp, List.mapM_cons, List.mapM_nil, callerPrincipalPin_toSpec,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hpins
  exact hpins.symm

/-- **Key-local semantics by principal**: under the default event schema, the specification's
universal symmetric pins of the projection are `callerPrincipal = principal`, as soon as the
action schema declares an action. -/
theorem default_typed_universalPins (h : derive defaultEventSchema f = .ok d)
    {A : Cedar.Validation.Schema} {S : Dogwood.Spec.EventSchema}
    (ht : typedSignatures d A = .ok S) (hne : S ≠ []) :
    Dogwood.Spec.EventSchema.universalPins S = [callerPrincipalSpecPin] := by
  have hp := default_typed_pins h ht
  cases S with
  | nil => exact absurd rfl hne
  | cons s rest =>
    simp only [Dogwood.Spec.EventSchema.universalPins, hp s (List.mem_cons_self ..)]
    simp only [List.filter_cons, List.filter_nil, callerPrincipalSpecPin,
      Dogwood.Spec.EventSchema.Pin.isSymmetric]
    have hall : ∀ x ∈ rest, callerPrincipalSpecPin ∈ x.pins := by
      intro x hx
      rw [hp x (List.mem_cons_of_mem _ hx)]
      simp
    simp only [callerPrincipalSpecPin] at hall
    simpa using hall

/-- The frontend's universal pins (the partition keys) under the default event schema. -/
theorem default_universalPins (h : derive defaultEventSchema f = .ok d)
    {A : Cedar.Validation.Schema} {S : Dogwood.Spec.EventSchema}
    (ht : typedSignatures d A = .ok S) (hne : d.events ≠ []) :
    universalPins d = .ok [callerPrincipalPin] := by
  have hS : S ≠ [] := by
    have h2 := typedSignatures_forall₂ ht
    obtain ⟨events, mw⟩ := d
    cases events with
    | nil => exact absurd rfl hne
    | cons _ _ => cases h2; exact List.cons_ne_nil _ _
  obtain ⟨S₀, h₀, hp, -⟩ := toSpecUntyped_of_typed ht
  unfold universalPins
  simp only [h₀, Except.mapError, bind, Except.bind]
  rw [universalPins_congr hp, default_typed_universalPins h ht hS]
  obtain ⟨events, mw⟩ := d
  cases events with
  | nil => exact absurd rfl hne
  | cons e₀ rest =>
    obtain ⟨-, -, -, -, -, -, -, hp₀, -⟩ := default_event h (List.mem_cons_self ..)
    simp only at hp₀ ⊢
    simp [hp₀, callerPrincipalPin_toSpec, pure, Except.pure]

/-- **The only decision kind is `request`** under the default event schema, as soon as the action
schema declares an action. -/
theorem default_decisionKinds (h : derive defaultEventSchema f = .ok d) {ks : List String}
    (hks : decisionKinds d = .ok ks) (k : String) :
    k ∈ ks ↔ (∃ ns nd, (ns, nd) ∈ f ∧ nd.actions ≠ []) ∧ k = "request" := by
  rw [derive_decisionKinds h hks]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨decl, hdecl, hd, rfl⟩
    simp only [defaultEventSchema, List.mem_cons, List.not_mem_nil, or_false] at hdecl
    rcases hdecl with rfl | rfl | rfl <;> simp_all
  · rintro rfl
    exact ⟨_, List.mem_cons_self .., rfl, rfl⟩

end Dogwood.Thm.Frontend.Derivation
