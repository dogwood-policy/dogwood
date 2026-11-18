import Dogwood.Spec.EventSchema
import Dogwood.Spec.Provider
import Cedar.Validation.RequestEntityValidator
import Dogwood.Spec.Canonical

/-!
# Runtime conformance

Validation (`Dogwood.Spec.PolicySet.Valid`) makes a policy set's leaves well-typed against the
schemas. At runtime, the data a decision reads must conform to the same schemas. This module
states what conformance is for each kind of runtime data; the decision fails closed on each
kind of nonconforming data, with a reason of its own (`Dogwood.Spec.FailClosed`).

* **A request** conforms when Cedar's `validateRequest` accepts it against the action schema:
  its principal, action, and resource are of a request environment's types, and its context
  is an instance of the action's context record type, closed (no undeclared attribute) and with
  every required attribute present.
* **An entity store** conforms when Cedar's `validateEntities` accepts it: every entity is of a
  declared type, has the declared attributes and tags of its type and ancestors of permitted
  types, and every action of the schema is present with its declared ancestors. A decision's
  store is the schema's action entities and the entity data supplied with the event, with the
  schema's entities taking precedence (`Dogwood.Spec.PolicySet.decisionEntities`).
* **An event** conforms to the event schema when it is of a declared signature and its logged record
  is an instance of the signature (`Event.Conforms`): every logged declared field has its declared
  type, every required field and every pinned field is logged, and every field that mirrors the
  request follows the mirror rule (`Mirrored`). The mirrored fields (`EventSignature.mirrors`) are
  the fields of the symmetric pins, and the caller fields `callerPrincipal` and `callerResource`
  when no pin names them. A pin is symmetric when it is pinned to the request's principal, its
  resource, or a context attribute, whatever the field is called (`EventSchema.Pin.isSymmetric`). A
  mirrored field holds the request's value when the event carries one, and is absent when the event
  does not. The mirror rule is what lets a pin isolate a key: an event cannot log one principal as
  its caller while it carries another, nor log a caller while it carries none. So under a universal
  pin, which every signature pins, an event that does not carry the pin's request-side value (a
  scope-less history event, say) conforms to no signature: every event must carry the scope of the
  key it reports on (`Dogwood.Thm.partitionable_of_strict`).
* **A provider output** conforms when it is a value of the provider's declared output type
  (`Provider.Output.Conforms`). A nonconforming output is a broken provider contract: the
  decision fails closed, as it does for a provider that errors.

Values are checked with Cedar's `instanceOfType`, against the entity types and actions of the
action schema.

**Values are canonical.** Cedar values have one form per meaning, except for sets and records:
`instanceOfType` admits a set whose elements are out of order or repeated, which then compares
unequal to the same set in order. So an event conforms only when its logged record and its
context are canonical (`Canonical`): every set in them is well-formed, sorted and without
duplicates, as `Set.make` builds it, and so is every record's attribute map. On canonical sets,
equality is equality of members (`Dogwood.Thm.canonical_set_eq_iff`). Cedar values have no
`null`, so a field an implementation records as `null` is absent here, and a decimal is its
numeric value, so `02.5` and `2.5` are one value. An implementation canonicalizes its values
(sorting and deduplicating sets, dropping `null` fields, reading decimals by value) before it
checks an event; it then accepts the event this specification accepts in canonical form.
-/

namespace Dogwood.Spec

open Cedar.Spec (Value EntityUID EntityType)
open Cedar.Validation (CedarType Schema instanceOfType)
open Temporal

/-- A logged field value has the field's declared type. An entity field of
`principalType(A)` or `resourceType(A)` holds a valid entity of one of the listed types. -/
def FieldTy.HasValue (A : Schema) : FieldTy → Value → Prop
  | .cedar ty, w => instanceOfType w ty A = true
  | .entities etys, w => ∃ uid, w = .prim (.entityUID uid) ∧ uid.ty ∈ etys ∧
      A.ets.isValidEntityUID uid = true

instance (A : Schema) (ft : FieldTy) (w : Value) : Decidable (ft.HasValue A w) :=
  match ft with
  | .cedar _ => inferInstanceAs (Decidable (_ = true))
  | .entities etys =>
    match w with
    | .prim (.entityUID uid) =>
      decidable_of_iff (uid.ty ∈ etys ∧ A.ets.isValidEntityUID uid = true)
        ⟨fun h => ⟨uid, rfl, h⟩, fun ⟨u, hu, h⟩ => by cases hu; exact h⟩
    | .prim (.bool _) | .prim (.int _) | .prim (.string _) | .set _ | .record _ | .ext _ =>
      .isFalse fun ⟨_, h, _⟩ => by cases h

/-- Whether the signature declares a field at `path` that no pin names. -/
def EventSignature.declaresUnpinned (sig : EventSignature) (path : Path) : Bool :=
  (sig.field? path).isSome && !sig.pins.any (·.field == path)

/-- The logged fields of an event of the signature that mirror its request: the field of each
symmetric pin, with the pin's request-side reference, and the caller fields `callerPrincipal`
and `callerResource` when the signature declares them and no pin names them. The crate's event
builder fills the caller fields from the request's scope. -/
def EventSignature.mirrors (sig : EventSignature) : List (Path × PinRef) :=
  (sig.pins.filter EventSchema.Pin.isSymmetric).map (fun p => (p.field, p.ref)) ++
    (if sig.declaresUnpinned ["callerPrincipal"] then [(["callerPrincipal"], .scope .principal [])]
     else []) ++
    (if sig.declaresUnpinned ["callerResource"] then [(["callerResource"], .scope .resource [])]
     else [])

/-- A declared field of an event: logged with its declared type, or absent and optional. -/
def FieldDecl.LoggedBy (A : Schema) (fd : FieldDecl) (ev : Event) : Prop :=
  match recordPath? ev.logged fd.path with
  | some w => fd.ty.HasValue A w
  | none => fd.required = false

instance (A : Schema) (fd : FieldDecl) (ev : Event) : Decidable (fd.LoggedBy A ev) := by
  unfold FieldDecl.LoggedBy; split <;> infer_instance

/-- **The mirror rule** (strict): a logged field that mirrors the request holds the request's
value when the event carries it, and is absent when the event does not.

When the request side resolves (the event carries a principal, a resource, or the pinned context
attribute), the logged field must hold exactly that value. When it does not resolve (a scope-less
event, or a context that omits the attribute), the field must not be logged at all: an event
cannot log a caller or a key it does not carry. A rule that held vacuously when the request side
did not resolve would let a scope-less event log any `callerPrincipal` and, under a pin, enter
that principal's history. Under the strict rule, a trace of conforming events is
partitionable (`Dogwood.Thm.partitionable_of_strict`). -/
def Mirrored (ev : Event) (m : Path × PinRef) : Prop :=
  match m.2.toTerm.eval? ev Valuation.empty with
  | some (.val w) => recordPath? ev.logged m.1 = some w
  | _ => recordPath? ev.logged m.1 = none

instance (ev : Event) (m : Path × PinRef) : Decidable (Mirrored ev m) := by
  unfold Mirrored; split <;> infer_instance

/-- The event's logged record is an instance of the signature. -/
structure EventSignature.Admits (A : Schema) (sig : EventSignature) (ev : Event) : Prop where
  /-- Every logged declared field has its declared type; every required field is logged. -/
  fields : ∀ fd ∈ sig.fields, fd.LoggedBy A ev
  /-- Every pinned field is logged. -/
  pinned : ∀ pin ∈ sig.pins, (recordPath? ev.logged pin.field).isSome = true
  /-- Every field that mirrors the request holds the request's value, and is absent when the
  event does not carry the request's value. -/
  mirrored : ∀ m ∈ sig.mirrors, Mirrored ev m
  /-- The logged record is canonical. -/
  canonical : Canonical (.record ev.logged)
  /-- The request context is canonical. -/
  contextCanonical : Canonical (.record ev.context)

instance (A : Schema) (sig : EventSignature) (ev : Event) : Decidable (sig.Admits A ev) :=
  decidable_of_iff
    ((∀ fd ∈ sig.fields, fd.LoggedBy A ev) ∧
     (∀ pin ∈ sig.pins, (recordPath? ev.logged pin.field).isSome = true) ∧
     (∀ m ∈ sig.mirrors, Mirrored ev m) ∧
     Canonical (.record ev.logged) ∧ Canonical (.record ev.context))
    ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩,
     fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

/-- **An event conforms** to the event schema: it is of a declared signature, and its logged
record is an instance of the signature. -/
def Event.Conforms (A : Schema) (S : EventSchema) (ev : Event) : Prop :=
  match S.signature? ev.action ev.kind with
  | some sig => sig.Admits A ev
  | none => False

instance (A : Schema) (S : EventSchema) (ev : Event) : Decidable (ev.Conforms A S) := by
  unfold Event.Conforms
  split <;> infer_instance

/-- **A provider output conforms** to its declared type: it is a value of the type. -/
def Provider.Output.Conforms (A : Schema) (ty : CedarType) : Provider.Output → Prop
  | .value v => instanceOfType v ty A = true
  | .error => False

instance (A : Schema) (ty : CedarType) (o : Provider.Output) : Decidable (o.Conforms A ty) :=
  match o with
  | .value _ => inferInstanceAs (Decidable (_ = true))
  | .error => .isFalse id

/-- An `Except` result succeeded. -/
def succeeds {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

end Dogwood.Spec
