import Dogwood.Spec.Conformance

/-!
# Deciding runtime conformance

Cedar's `instanceOfType` is defined by well-founded recursion, so no proof by reduction can
compute it: `decide` cannot check that a concrete value conforms. This module restates it by
structural recursion (`valueInstanceOf`), which the kernel evaluates, and builds on it Boolean
checks of each kind of runtime conformance:

* `FieldTy.hasValueB`, `Event.conformsB`: an event conforms to the event schema;
* `requestConformsB`: Cedar's `validateRequest` accepts a request;
* `Provider.Output.conformsB`: a provider output conforms to its declared type.

`Dogwood.Thm.valueInstanceOf_eq` proves the restatement equal to Cedar's, and
`Dogwood.Thm.conformsB_iff`, `Dogwood.Thm.requestConformsB_eq`, and
`Dogwood.Thm.output_conformsB_iff` prove the checks decide the specification's relations.
-/

namespace Dogwood.Eval

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value Attr Request)
open Cedar.Validation (CedarType RecordType Schema instanceOfBoolType instanceOfEntityType
  instanceOfExtType requiredAttributePresent)

mutual

/-- Cedar's `instanceOfType v ty schema`, by structural recursion on the value. -/
def valueInstanceOf (env : Schema) : Value → CedarType → Bool
  | .prim (.bool b), .bool bty => instanceOfBoolType b bty
  | .prim (.int _), .int => true
  | .prim (.string _), .string => true
  | .prim (.entityUID e), .entity ety => instanceOfEntityType e ety env
  | .set (.mk vs), .set ty => valuesInstanceOf env vs ty
  | .record (.mk kvs), .record rty =>
    kvs.all (fun (k, _) => rty.contains k) && fieldsInstanceOf env kvs rty &&
      rty.toList.all (fun (k, _) => requiredAttributePresent (.mk kvs) rty k)
  | .ext x, .ext xty => instanceOfExtType x xty
  | _, _ => false

/-- Every element of a set's list is an instance of the element type. -/
def valuesInstanceOf (env : Schema) : List Value → CedarType → Bool
  | [], _ => true
  | v :: vs, ty => valueInstanceOf env v ty && valuesInstanceOf env vs ty

/-- Every attribute of a record's list that the record type declares holds a value of the
declared type. -/
def fieldsInstanceOf (env : Schema) : List (Attr × Value) → RecordType → Bool
  | [], _ => true
  | (k, v) :: kvs, rty =>
    (match rty.find? k with
     | some qty => valueInstanceOf env v qty.getType
     | none => true) && fieldsInstanceOf env kvs rty

end

end Dogwood.Eval

namespace Dogwood.Spec

open Temporal Dogwood.Eval
open Cedar.Spec (Value Request)
open Cedar.Validation (CedarType Schema instanceOfEntityType)

/-- A logged field value has the field's declared type (`FieldTy.HasValue`). -/
def FieldTy.hasValueB (A : Schema) : FieldTy → Value → Bool
  | .cedar ty, w => valueInstanceOf A w ty
  | .entities etys, .prim (.entityUID uid) => etys.contains uid.ty && A.ets.isValidEntityUID uid
  | .entities _, _ => false

/-- A declared field of an event is logged with its declared type, or absent and optional
(`FieldDecl.LoggedBy`). -/
def FieldDecl.loggedByB (A : Schema) (fd : FieldDecl) (ev : Event) : Bool :=
  match recordPath? ev.logged fd.path with
  | some w => fd.ty.hasValueB A w
  | none => !fd.required

/-- A field that mirrors the request holds the request's value, and is absent when the event
does not carry it (`Mirrored`, the strict mirror rule). -/
def mirroredB (ev : Event) (m : Path × PinRef) : Bool :=
  match m.2.toTerm.eval? ev Valuation.empty with
  | some (.val w) => recordPath? ev.logged m.1 == some w
  | _ => (recordPath? ev.logged m.1).isNone

/-- The event's logged record is an instance of the signature (`EventSignature.Admits`). -/
def EventSignature.admitsB (A : Schema) (sig : EventSignature) (ev : Event) : Bool :=
  sig.fields.all (FieldDecl.loggedByB A · ev) &&
    sig.pins.all (fun pin => (recordPath? ev.logged pin.field).isSome) &&
    sig.mirrors.all (mirroredB ev) &&
    canonicalB (.record ev.logged) && canonicalB (.record ev.context)

/-- **An event conforms** to the event schema (`Event.Conforms`). -/
def Event.conformsB (A : Schema) (S : EventSchema) (ev : Event) : Bool :=
  match S.signature? ev.action ev.kind with
  | some sig => EventSignature.admitsB A sig ev
  | none => false

/-- **A request conforms**: `Cedar.Validation.validateRequest` accepts it. -/
def _root_.Dogwood.Eval.requestConformsB (A : Schema) (req : Request) : Bool :=
  A.environments.any fun env =>
    instanceOfEntityType req.principal env.reqty.principal env.schema &&
    req.action == env.reqty.action &&
    instanceOfEntityType req.resource env.reqty.resource env.schema &&
    valueInstanceOf env.schema req.context (.record env.reqty.context)

/-- **A provider output conforms** to its declared type (`Provider.Output.Conforms`). -/
def Provider.Output.conformsB (A : Schema) (ty : CedarType) : Provider.Output → Bool
  | .value v => valueInstanceOf A v ty
  | .error => false

end Dogwood.Spec
