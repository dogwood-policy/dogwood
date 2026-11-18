import Dogwood.Frontend.Types
import Dogwood.Spec.EventSchema

/-!
# What is read off the derived event schema

Three small functions of the derived event schema, which the crate computes in `Base::derive`
(`api.rs`) and `derive.rs`, and which this module defines through the specification's own
definitions where it has them:

* the public **event signatures**, each derived event with its leaf fields sorted by the text of
  their path (`DerivedEvent::leaf_fields`);
* the **universal symmetric pins** (`relativize::universal_pins`), through the specification's
  `EventSchema.universalPins` and `Pin.isSymmetric`; the crate's partition keys are these pins;
* the **decision kinds** (`DerivedEventSchema::decision_kinds`), through the specification's
  `EventSchema.isDecisionKind`.
-/

namespace Dogwood.Frontend

open Dogwood.Spec (ScopeRoot)

mutual

/-- The leaf fields under a field tree, as `(path, type)`, in tree order. -/
def DerivedFieldNode.leaves (prefix_ : List String) : List (String × DerivedFieldNode) →
    List (List String × FieldType)
  | [] => []
  | (n, .leaf t) :: rest => (prefix_ ++ [n], t) :: DerivedFieldNode.leaves prefix_ rest
  | (n, .group ms) :: rest =>
    DerivedFieldNode.leaves (prefix_ ++ [n]) ms ++ DerivedFieldNode.leaves prefix_ rest

end

/-- The event's leaf fields, sorted by the text of their path (crate
`DerivedEvent::leaf_fields`; the sort is stable). -/
def DerivedEvent.leafFields (e : DerivedEvent) : List (List String × FieldType) :=
  (DerivedFieldNode.leaves [] e.fields).mergeSort fun a b =>
    decide (fieldPathJoin a.1 ≤ fieldPathJoin b.1)

/-- The event's public signature (crate `signature_of`). -/
def DerivedEvent.signature (e : DerivedEvent) : EventSignature :=
  { «namespace» := e.namespace, action := e.action, kind := e.kind, decision := e.decision,
    fields := e.leafFields, pins := e.pins }

/-- The public event signatures (crate `Lowered::event_signatures`). -/
def DerivedEventSchema.signatures (d : DerivedEventSchema) : Result (List EventSignature) :=
  pure (d.events.map DerivedEvent.signature)

/-- The action an event's `(namespace, action)` names, as an entity uid. -/
def actionUid (ns : List String) (action : String) : Cedar.Spec.EntityUID :=
  ⟨⟨ns.getLast?.getD "", ns.dropLast⟩, action⟩

/-- A crate pin as the specification's: a `scope` path's head is its root. -/
def Pin.toSpec (p : Pin) : Except String Dogwood.Spec.Pin :=
  match p.root, p.contextPath with
  | .context, path => pure ⟨p.fieldPath, .context path⟩
  | .scope, "principal" :: rest => pure ⟨p.fieldPath, .scope .principal rest⟩
  | .scope, "resource" :: rest => pure ⟨p.fieldPath, .scope .resource rest⟩
  | .scope, path => throw s!"scope pin rooted at {path}"

/-- The derived schema's events as the specification's signatures, without their fields: all
that the universal pins and the decision kinds read. -/
def DerivedEventSchema.toSpecUntyped (d : DerivedEventSchema) :
    Except String Dogwood.Spec.EventSchema :=
  d.events.mapM fun e => do
    return { action := actionUid e.namespace e.action, kind := e.kind, decision := e.decision,
             pins := ← e.pins.mapM Pin.toSpec, fields := [] }

/-- The universal symmetric pins (crate `relativize::universal_pins`): the pins of the first
event that the specification's `EventSchema.universalPins` keeps. -/
def universalPins (d : DerivedEventSchema) : Result (List Pin) := do
  let S ← (d.toSpecUntyped).mapError fun m => { stage := .universalPins, category := .other, message := m }
  let u := Dogwood.Spec.EventSchema.universalPins S
  match d.events with
  | [] => pure []
  | e :: _ => pure (e.pins.filter fun p => match p.toSpec with
      | .ok q => u.contains q
      | .error _ => false)

/-- The decision kinds (crate `DerivedEventSchema::decision_kinds`): the kinds the
specification's `EventSchema.isDecisionKind` holds of, sorted. -/
def decisionKinds (d : DerivedEventSchema) : Result (List String) := do
  let S ← (d.toSpecUntyped).mapError fun m => { stage := .decisionKinds, category := .other, message := m }
  pure (ProviderDecls.sortedSet ((d.events.map (·.kind)).filter S.isDecisionKind))

end Dogwood.Frontend
