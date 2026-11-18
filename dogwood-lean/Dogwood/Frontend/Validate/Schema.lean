import Dogwood.Frontend.Conformance
import Dogwood.Frontend.Escape

/-!
# The validator's view of the augmented schema

The crate's validator reads the augmented schema through a thin adapter over Cedar's
`ValidatorSchema` (`extension/temporal/schema_info.rs`): an action's context record, the
attributes of an entity type, the entity types an action admits for its principal and resource
under a rule's scope narrowing, and the resolution of an attribute path. This module is that
adapter over the compiled schema of a lowered set (`Lowered.schema`, cedar-lean's
`Cedar.Validation.Schema`), with the crate's names: an action is `(namespace, id)`, an entity
type is named by its text `A::B`.

Types are Cedar's (`CedarType`): the crate's `RichType` is a projection of Cedar's types that is
exact for every type a schema declares (`schema_info.rs`, `RichType`), so the two compare alike.
-/

namespace Dogwood.Frontend.Validate

open Cedar.Spec (EntityType EntityUID Attr)
open Cedar.Validation (CedarType RecordType QualifiedType Schema ActionSchemaEntry)

/-! ## Names -/

/-- The last position at which `pat` occurs in `s`, as a character offset. -/
def lastIndexOf? (s pat : List Char) : Option Nat :=
  go s 0 none
where
  go : List Char → Nat → Option Nat → Option Nat
    | [], i, best => if pat.isEmpty then some i else best
    | c :: cs, i, best => go cs (i + 1) (if pat.isPrefixOf (c :: cs) then some i else best)

/-- A name lowering reserves for a leaf's value (crate `api::is_hoisted_name`): `providers`, or a
name ending in `__temporal_<digits>`. -/
def isHoistedName (name : String) : Bool :=
  name == "providers" ||
    let marker := "__temporal_".toList
    match lastIndexOf? name.toList marker with
    | some i =>
      let ordinal := name.toList.drop (i + marker.length)
      !ordinal.isEmpty && ordinal.all Char.isDigit
    | none => false

/-- An entity type by its text `A::B::T`. -/
def parseEntityType (text : String) : EntityType :=
  let segs := text.splitOn "::"
  ⟨segs.getLast?.getD "", segs.dropLast⟩

/-- The uid of the action `(namespace, id)`: `Ns::Action::"id"`, or `Action::"id"` at the root
(crate `SchemaInfo::action`). -/
def actionUidOf (ns id : String) : EntityUID :=
  ⟨parseEntityType (if ns.isEmpty then "Action" else ns ++ "::Action"), id⟩

/-- An action uid as the crate renders an action reference in a diagnostic: Cedar's text of the
uid, its id escaped (`EntityUID`'s `Display`, `Eid::escaped`). -/
def actionText (uid : EntityUID) : String :=
  nameText uid.ty ++ "::\"" ++ Escape.strEscapeDebug uid.eid ++ "\""

/-- An id as the crate's diagnostics print it (`Eid::escaped`, Rust's `str::escape_debug`). -/
def escapedId (id : String) : String := Escape.strEscapeDebug id

/-- The predicate form of an action, `Ns::id` (crate `schema_info::predicate_ref`): the namespace
of its type without the trailing `Action`, then its escaped id; the escaped id alone at the
root. -/
def predicateRef (uid : EntityUID) : String :=
  match uid.ty.path with
  | [] => escapedId uid.eid
  | path => "::".intercalate path ++ "::" ++ escapedId uid.eid

/-! ## Types, rendered -/

mutual

/-- A Cedar type as the crate's validator renders it in a diagnostic (`RichType::display`). -/
def renderType : CedarType → String
  | .bool _ => "boolean"
  | .int => "int"
  | .string => "string"
  | .entity ety => nameText ety
  | .set t => s!"array<{renderType t}>"
  | .record rty => "{ " ++ ", ".intercalate (renderAttrs rty.toList) ++ " }"
  | .ext .decimal => "decimal"
  | .ext .ipAddr => "ipaddr"
  | .ext .datetime => "datetime"
  | .ext .duration => "duration"

def renderAttrs : List (Attr × QualifiedType) → List String
  | [] => []
  | (a, .required t) :: rest => (a ++ ": " ++ renderType t) :: renderAttrs rest
  | (a, .optional t) :: rest => (a ++ "?: " ++ renderType t) :: renderAttrs rest

end

mutual

/-- A Cedar type as the crate's runtime types render it (`CType::from_type`, then
`CType::render`): `Bool`, `Long`, `String`, `decimal`, an extension type by its name, `Set<…>`,
a record with its attributes, an entity type by its name. -/
def renderCType : CedarType → String
  | .bool _ => "Bool"
  | .int => "Long"
  | .string => "String"
  | .entity ety => nameText ety
  | .set t => s!"Set<{renderCType t}>"
  | .record rty => "{ " ++ ", ".intercalate (renderCAttrs rty.toList) ++ " }"
  | .ext .decimal => "decimal"
  | .ext .ipAddr => "ipaddr"
  | .ext .datetime => "datetime"
  | .ext .duration => "duration"

def renderCAttrs : List (Attr × QualifiedType) → List String
  | [] => []
  | (a, .required t) :: rest => (a ++ ": " ++ renderCType t) :: renderCAttrs rest
  | (a, .optional t) :: rest => (a ++ "?: " ++ renderCType t) :: renderCAttrs rest

end

/-- A sort as the crate's runtime types render it (`CType::render`); a timepoint, which no value
type holds, as `timepoint`. -/
def renderCSort : Dogwood.Spec.Temporal.TType → String
  | .cedar t => renderCType t
  | .timepoint => "timepoint"

/-- A sort as the crate renders it: a timepoint is `timepoint`. -/
def renderSort : Dogwood.Spec.Temporal.TType → String
  | .cedar t => renderType t
  | .timepoint => "timepoint"

/-! ## Actions and entity types -/

/-- The declared action `(namespace, id)` and its schema entry. -/
def action? (S : Schema) (ns id : String) : Option (EntityUID × ActionSchemaEntry) :=
  let uid := actionUidOf ns id
  (S.acts.find? uid).map (uid, ·)

/-- The attributes the entity type declares, when it is declared (an enum declares none). -/
def entityAttrs? (S : Schema) (ety : EntityType) : Option RecordType :=
  S.ets.attrs? ety

/-! ## Scope narrowing -/

/-- Whether a rule's principal or resource narrowing admits the entity type `ety` (crate
`ActionHandle::admits`): `in G` admits `G`'s type and every type whose declared ancestors
include it. -/
def constraintAdmits (S : Schema) : ScopeConstraint → EntityType → Bool
  | .any, _ => true
  | .isType t, ety => nameText ety == t
  | .uid t m, ety =>
    nameText ety == t ||
      (m && match S.ets.find? ety with
        | some entry => entry.ancestors.toList.any (nameText · == t)
        | none => false)

/-- The root of a scope path. -/
inductive Root where
  | principal
  | resource
deriving DecidableEq, Repr, Inhabited

def Root.name : Root → String
  | .principal => "principal"
  | .resource => "resource"

def Root.toSpec : Root → Dogwood.Spec.ScopeRoot
  | .principal => .principal
  | .resource => .resource

def Root.ofSpec : Dogwood.Spec.ScopeRoot → Root
  | .principal => .principal
  | .resource => .resource

/-- The entity types an action admits for a scope root (`appliesTo`). -/
def appliesTo (entry : ActionSchemaEntry) : Root → List EntityType
  | .principal => entry.appliesToPrincipal.toList
  | .resource => entry.appliesToResource.toList

/-- The entity types an action admits for a root that the rule's narrowing admits too (crate
`ActionHandle::admitted_types`). -/
def admittedTypes (S : Schema) (entry : ActionSchemaEntry) (r : Root) (narrow : ScopeConstraint) :
    List EntityType :=
  (appliesTo entry r).filter (constraintAdmits S narrow)

/-- Whether the action admits a request environment under the rule's narrowing: some principal
type and some resource type survive it (crate `ActionHandle::admits_any_env`). -/
def admitsAnyEnv (S : Schema) (entry : ActionSchemaEntry) (p r : ScopeConstraint) : Bool :=
  (appliesTo entry .principal).any (constraintAdmits S p) &&
    (appliesTo entry .resource).any (constraintAdmits S r)

/-! ## Paths -/

/-- How a `context.<path>` resolves in an action's context record (crate `PathResolution`). -/
inductive PathResolution where
  | resolved (ty : CedarType)
  | headMissing
  | nestedMissing (segment : String)
  | nonRecord (segment : String)

/-- Descend `rest` from a type. -/
def descend : CedarType → List String → PathResolution
  | ty, [] => .resolved ty
  | .record rty, seg :: rest =>
    match rty.find? seg with
    | some q => descend q.getType rest
    | none => .nestedMissing seg
  | _, seg :: _ => .nonRecord seg

/-- Resolve `context.<path>` in the context record, whether or not an optional attribute along it
is present (crate `ActionHandle::resolve_context_path`). An attribute lowering hoisted does not
resolve: it is not part of the request a caller supplies. -/
def resolveContextPath (ctx : RecordType) : List String → PathResolution
  | [] => .headMissing
  | head :: rest =>
    if isHoistedName head then .headMissing
    else match ctx.find? head with
      | some q => descend q.getType rest
      | none => .headMissing

/-- The type of `context.<path>`, when it resolves (crate `context_path_cedar_type`). -/
def contextPathType? (ctx : RecordType) (path : List String) : Option CedarType :=
  match resolveContextPath ctx path with
  | .resolved ty => some ty
  | _ => none

/-- Why resolving a scope attribute path against one entity type failed. -/
inductive ScopeFailure where
  | missing (segment : String)
  | nonRecord (segment : String)
deriving BEq

/-- Resolve an attribute path against an entity type's attributes (crate `resolve_one`). `id`
and `type` are attributes like any other, as in Cedar. -/
def resolveOne (attrs : RecordType) (first : String) (rest : List String) :
    Except ScopeFailure CedarType :=
  match attrs.find? first with
    | none => .error (.missing first)
    | some q => go q.getType rest
where
  go : CedarType → List String → Except ScopeFailure CedarType
    | ty, [] => .ok ty
    | .record rty, seg :: rest =>
      match rty.find? seg with
      | some q => go q.getType rest
      | none => .error (.missing seg)
    | _, seg :: _ => .error (.nonRecord seg)

/-- The type of a scope attribute path on the entity type `ety` (crate
`ActionHandle::scope_attribute_type_of`). -/
def scopeAttrTypeOf? (S : Schema) (ety : EntityType) : List String → Option CedarType
  | [] => none
  | first :: rest =>
    match entityAttrs? S ety with
    | some attrs => (resolveOne attrs first rest).toOption
    | none => none

/-- The declared type of a scope attribute path (crate
`ActionHandle::scope_attribute_cedar_type`). -/
def scopeAttrCedarType? (S : Schema) (ety : EntityType) : List String → Option CedarType
  | [] => none
  | first :: rest =>
    match entityAttrs? S ety with
      | some attrs =>
        match attrs.find? first with
        | some q =>
          match descend q.getType rest with
          | .resolved ty => some ty
          | _ => none
        | none => none
      | none => none

/-- How a scope attribute path resolves across the entity types a rule admits (crate
`ScopePath`). -/
inductive ScopePath where
  | resolved
  | missing (entities : List String) (segment : String)
  | nonRecord (segment : String)
  | ambiguous (types : List String)
  | unknown

/-- Resolve `root.<path>` against every entity type the action admits for the root under the
rule's narrowing (crate `ActionHandle::resolve_scope_path`): it fails when it fails on any of
them, and is ambiguous when it resolves to different types. -/
def resolveScopePath (S : Schema) (entry : ActionSchemaEntry) (r : Root) (narrow : ScopeConstraint)
    (path : List String) : ScopePath :=
  match path with
  | [] => .unknown
  | first :: rest =>
    let etys := admittedTypes S entry r narrow
    if etys.isEmpty then .unknown
    else if etys.any (fun ety => (entityAttrs? S ety).isNone) then .unknown
    else
      let results := etys.map fun ety =>
        (nameText ety, (resolveOne ((entityAttrs? S ety).getD Cedar.Data.Map.empty) first rest))
      let failed := (results.filterMap fun (e, r) => match r with
        | .error f => some (e, f)
        | .ok _ => none).mergeSort (fun a b => decide (a.1 ≤ b.1))
      match failed with
      | (_, f) :: _ =>
        let same := failed.filter (·.2 == f)
        match f with
        | .missing seg => .missing (same.map (·.1)) seg
        | .nonRecord seg => .nonRecord seg
      | [] =>
        let types := (results.filterMap fun (_, r) => r.toOption).eraseDups
        if types.length > 1 then .ambiguous ((types.map renderType).mergeSort (fun a b => decide (a ≤ b)))
        else .resolved

end Dogwood.Frontend.Validate
