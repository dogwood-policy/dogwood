import Dogwood.Frontend.Validate.Schema

/-!
# The validator's view of the derived event schema

The lookups the crate's validator makes in the derived event schema: the event a predicate names
(`DerivedEventSchema::get`), whether a field path names a field, a field group, or nothing
(`DerivedEvent::lookup_path`), and the type of each declared field (`conformance::event_fields`):
a field spliced from the action's `context.input` or `context.output` has the type the context
declares at its path, any other field the type the event schema names. A type the schemas do not
determine (the crate's `CType::Any`) is `none`: no value of a known type is in it.

The field types are the specification's (`FieldTy`), computed with the conformance projection's
own helpers (`pathType`, `textType`, `resolveEntityType`), which follow the bridge as the crate's
`event_fields` follows the same rules.
-/

namespace Dogwood.Frontend.Validate

open Cedar.Spec (EntityUID)
open Cedar.Validation (CedarType Schema)

/-- The derived event a predicate names, by its action's uid and its kind (crate
`DerivedEventSchema::get`): the first that matches. -/
def eventOf? (d : DerivedEventSchema) (action : EntityUID) (kind : String) : Option DerivedEvent :=
  d.events.find? fun e => actionUid e.namespace e.action == action && e.kind == kind

/-- What a field path names in an event's field tree (crate `PathLookup`). -/
inductive PathLookup where
  | leaf
  | group
  | absent
deriving DecidableEq, Repr

/-- Look `rest` up below a node. -/
def lookupBelow : DerivedFieldNode → List String → PathLookup
  | .leaf _, [] => .leaf
  | .group _, [] => .group
  | .group ms, seg :: rest =>
    match ms.lookup seg with
    | some n => lookupBelow n rest
    | none => .absent
  | .leaf _, _ :: _ => .absent

/-- What a field path names in the event (crate `DerivedEvent::lookup_path`). -/
def lookupPath (e : DerivedEvent) : List String → PathLookup
  | [] => .absent
  | head :: rest =>
    match e.fields.lookup head with
    | some n => lookupBelow n rest
    | none => .absent

/-- The declared leaf field paths, as text, for a diagnostic. -/
def declaredPaths (e : DerivedEvent) : List String :=
  e.leafFields.map (fieldPathJoin ·.1)

/-- Whether a field path is spliced from the action's `input` or `output` record. -/
def isSpliced : List String → Bool
  | "input" :: _ | "output" :: _ => true
  | _ => false

/-- The type of each declared leaf field of the event, and whether every event must log it
(crate `conformance::event_fields`). `none` is a type the schemas do not determine. -/
def eventFields (S : Schema) (e : DerivedEvent) :
    List (List String × Option Dogwood.Spec.FieldTy × Bool) :=
  let context := (S.acts.find? (actionUid e.namespace e.action)).map (·.context)
  e.leafFields.map fun (path, fty) =>
    match isSpliced path, context.bind (pathType · path) with
    | true, some (t, req) => (path, some (.cedar t), req)
    | _, _ =>
      match fty with
      | .entityTypes names =>
        (path, some (.entities (names.filterMap fun n =>
          (resolveEntityType S e.namespace n).toOption)), false)
      | .cedar text => (path, ((textType S text).toOption.map .cedar), false)

/-- The declared type of the field at `path`, when the event declares one (`some none` for a type
the schemas do not determine). -/
def fieldType? (S : Schema) (e : DerivedEvent) (path : List String) :
    Option (Option Dogwood.Spec.FieldTy) :=
  ((eventFields S e).find? (·.1 == path)).map (·.2.1)

/-- Whether a field type can hold a value of sort `τ` (crate `validity::accepts`): a type the
schemas do not determine holds none. -/
def fieldAccepts : Option Dogwood.Spec.FieldTy → Dogwood.Spec.Temporal.TType → Bool
  | some fd, τ => Dogwood.Eval.acceptsB fd τ
  | none, _ => false

/-- Whether every value of a field type has sort `τ` (crate `validity::within`). -/
def fieldWithin : Option Dogwood.Spec.FieldTy → Dogwood.Spec.Temporal.TType → Bool
  | some fd, τ => Dogwood.Eval.withinB fd τ
  | none, _ => false

/-- A field type, as the crate renders it in a diagnostic (`CType::render`). -/
def renderFieldTy : Option Dogwood.Spec.FieldTy → String
  | some (.cedar t) => renderCType t
  | some (.entities etys) => " | ".intercalate (etys.map nameText)
  | none => "any value"

end Dogwood.Frontend.Validate
