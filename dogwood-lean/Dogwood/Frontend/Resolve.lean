import Dogwood.Frontend.Types

/-!
# Cedar's schema resolution and compilation (WP2)

What Cedar does with a schema fragment before validation (`ValidatorSchema::from_schema_fragments`
in `cedar-policy-core`): resolve every name, inline the common types, check the fragment's
well-formedness, and compute the entity and action hierarchies. The result is cedar-lean's
`Cedar.Validation.Schema`, with *ancestor* sets.

**Definitions.** The declared names (`Defs`, Cedar's `AllDefs`) are, each qualified by its
namespace: the entity types, with the `Action` type of every namespace that declares actions; the
common types, with the builtins `__cedar::Bool`, `__cedar::Long`, `__cedar::String`,
`__cedar::decimal`, `__cedar::ipaddr`, `__cedar::datetime`, `__cedar::duration`, and, in the root
namespace, an alias of each builtin that the root namespace does not itself declare as an entity
or common type; and the actions.

**Names.** A name written unqualified in namespace `N` denotes `N::T` if that is declared, else
the root `T` (`candidates`); a qualified name denotes itself. A type reference (`T` in a type) is a
common type if the candidate is one, else an entity type, candidate by candidate
(`resolveRef`); an entity-type position (`memberOfTypes`, `appliesTo`) takes entity types only.

**Inlining.** A reference to a common type is replaced by the common type's definition, itself
resolved in the namespace that declares it (`convert`). A chain of references longer than the
number of common types repeats a name: a cycle, which Cedar rejects.

**Checks.** Each of the following is an error (category `cedarSchema`; the harness compares
Cedar's errors by category only): an entity type declared `external` with an enumerated ancestor;
a reference that denotes nothing; a cycle of common types; an
unknown extension type; an open record; an entity shape or action context that is not a record;
an `appliesTo` or `memberOfTypes` entity type that is not a declared entity type; an action
`memberOf` that names no declared action; a cycle of actions; an entity type named `Action`; an
action with attributes; a name an unqualified declaration of the root namespace shares with a
qualified one (RFC 70 shadowing), for types and for actions; and the declarations the Rust types
make impossible (a name declared twice, a reserved name).

**Hierarchies.** An entity type's ancestors are the entity types reachable through
`memberOfTypes`, an action's the actions reachable through `memberOf` (`closure`).
-/

namespace Dogwood.Frontend.CedarSchema

open Cedar.Spec (Name EntityType EntityUID)
open Cedar.Validation (CedarType QualifiedType RecordType Qualified ExtType Schema
  EntitySchemaEntry StandardSchemaEntry ActionSchemaEntry)
open Cedar.Data (Map Set)

namespace Resolve

/-! ## Names -/

/-- A name's text as a name (`A::B::T` is `T` in `A::B`). -/
def parseName (s : String) : Name :=
  let segs := s.splitOn "::"
  ⟨segs.getLast?.getD "", segs.dropLast⟩

/-- A namespace key as the name of the namespace. -/
def nsName (ns : Option String) : Option Name := ns.map parseName

/-- Whether a component of the name is `__cedar` (`InternalName::is_reserved`). -/
def isReserved (n : Name) : Bool := (n.id :: n.path).contains "__cedar"

/-- The declaration `id` of the namespace `ns`, or a name written in it, if unqualified, prefixed
by the namespace (`InternalName::qualify_with`). -/
def qualifyWith (ns : Option Name) (n : Name) : Name :=
  if n.path.isEmpty then
    match ns with
    | some ns => ⟨n.id, ns.path ++ [ns.id]⟩
    | none => n
  else n

/-- The names a name written in namespace `ns` may denote, in the order Cedar tries them
(`RawName::conditionally_qualify_with`): `ns::T` then `T` for an unqualified `T` in a namespace,
the name itself otherwise. -/
def candidates (ns : Option Name) (raw : String) : List Name :=
  let n := parseName raw
  if n.path.isEmpty then
    match ns with
    | some ns' => [qualifyWith (some ns') n, n]
    | none => [n]
  else [n]

/-- The `Action` entity type of a namespace. -/
def actionType (ns : Option Name) : EntityType := qualifyWith ns ⟨"Action", []⟩

/-! ## Declarations -/

/-- The builtin primitive and extension types, by name, as Cedar's `__cedar` namespace defines
them (`primitive_types`, `cedar_fragment`). -/
def builtins : List (String × SchemaType) :=
  [("Bool", .boolean), ("Long", .long), ("String", .string),
   ("decimal", .extension "decimal"), ("ipaddr", .extension "ipaddr"),
   ("datetime", .extension "datetime"), ("duration", .extension "duration")]

/-- A common type: its qualified name, the namespace its definition's names are written in, and
the definition. -/
structure CommonDef where
  name : Name
  ns : Option Name
  ty : SchemaType

/-- The names declared by a fragment (Cedar `AllDefs`), and the common types' definitions. -/
structure Defs where
  /-- The declared entity types (not the action types). -/
  declared : List EntityType
  /-- The names that are entity types for name resolution: the declared ones, and the `Action`
  type of every namespace with actions. -/
  entities : List Name
  /-- The common types, the builtins and the root aliases included. -/
  commons : List CommonDef
  /-- The actions. -/
  actions : List EntityUID

/-- The user's entity types, common types and actions, each qualified by its namespace. -/
def userEntities (f : Fragment) : List EntityType :=
  f.flatMap fun (ns, d) => d.entityTypes.map fun (id, _) => qualifyWith (nsName ns) ⟨id, []⟩

def userCommons (f : Fragment) : List CommonDef :=
  f.flatMap fun (ns, d) => d.commonTypes.map fun (id, ct) =>
    { name := qualifyWith (nsName ns) ⟨id, []⟩, ns := nsName ns, ty := ct.ty }

def userActions (f : Fragment) : List EntityUID :=
  f.flatMap fun (ns, d) => d.actions.map fun (id, _) => ⟨actionType (nsName ns), id⟩

/-- The common types of the `__cedar` namespace. -/
def cedarCommons : List CommonDef :=
  builtins.map fun (id, ty) => { name := ⟨id, ["__cedar"]⟩, ns := some ⟨"__cedar", []⟩, ty }

/-- The declarations of a fragment, after Cedar adds its builtins: the root aliases of the
builtins the root namespace leaves free, and the action types as entity types. -/
def Defs.ofFragment (f : Fragment) : Defs :=
  let declared := userEntities f
  let commons := userCommons f ++ cedarCommons
  let free := fun (id : String) =>
    !declared.contains ⟨id, []⟩ && !(commons.any (·.name == ⟨id, []⟩))
  let aliases := (builtins.filter (free ·.1)).map fun (id, _) =>
    ({ name := ⟨id, []⟩, ns := none, ty := .entityOrCommon s!"__cedar::{id}" } : CommonDef)
  let actionTypes := (f.filter fun (_, d) => !d.actions.isEmpty).map fun (ns, _) =>
    actionType (nsName ns)
  { declared, entities := declared ++ actionTypes, commons := commons ++ aliases,
    actions := userActions f }

/-- Whether `n` is a common type. -/
def Defs.isCommon (D : Defs) (n : Name) : Bool := D.commons.any (·.name == n)

/-- What a type reference written in `ns` denotes (`ConditionalName::resolve` with
`CommonOrEntity`): the first candidate that is a common type (`inl`) or an entity type (`inr`). -/
def Defs.resolveRef (D : Defs) (ns : Option Name) (raw : String) : Option (Name ⊕ EntityType) :=
  (candidates ns raw).findSome? fun p =>
    if D.isCommon p then some (.inl p)
    else if D.entities.contains p then some (.inr p)
    else none

/-- The common type a reference written in `ns` denotes (`ReferenceType::Common`). -/
def Defs.resolveCommon (D : Defs) (ns : Option Name) (raw : String) : Option Name :=
  (candidates ns raw).find? D.isCommon

/-- The entity type a name in an entity-type position written in `ns` denotes
(`ReferenceType::Entity`). -/
def Defs.resolveEntity (D : Defs) (ns : Option Name) (raw : String) : Option EntityType :=
  (candidates ns raw).find? D.entities.contains

/-- The action a `memberOf` entry written in `ns` denotes. -/
def Defs.resolveAction (D : Defs) (ns : Option Name) (m : ActionUid) : Option EntityUID :=
  ((candidates ns (m.ty.getD "Action")).map fun p => (⟨p, m.id⟩ : EntityUID)).find? fun u =>
    !isReserved u.ty && D.actions.contains u

/-! ## Types -/

/-- The extension type of an extension name. -/
def extType? : String → Option ExtType
  | "decimal" => some .decimal
  | "ipaddr" => some .ipAddr
  | "datetime" => some .datetime
  | "duration" => some .duration
  | _ => none

/-- An attribute's qualified type. -/
def qualified (required : Bool) (ty : CedarType) : QualifiedType :=
  if required then .required ty else .optional ty

mutual

/-- A schema type written in namespace `ns`, as a Cedar type: every name resolved, and each
common type it refers to replaced by `inl` of the common type's name. -/
def convertT (D : Defs) (inl : Name → Except String CedarType) (ns : Option Name) :
    SchemaType → Except String CedarType
  | .string => pure .string
  | .long => pure .int
  | .boolean => pure (.bool .anyBool)
  | .set e => do pure (.set (← convertT D inl ns e))
  | .record attrs additional =>
    if additional then throw "records with additional attributes are not supported"
    else do pure (.record (Map.make (← convertAttrsT D inl ns attrs)))
  | .entity n =>
    match D.resolveEntity ns n with
    | some e => pure (.entity e)
    | none => throw s!"undeclared entity type `{n}`"
  | .entityOrCommon n =>
    match D.resolveRef ns n with
    | some (.inl c) => inl c
    | some (.inr e) => pure (.entity e)
    | none => throw s!"undeclared type `{n}`"
  | .commonRef n =>
    match D.resolveCommon ns n with
    | some c => inl c
    | none => throw s!"undeclared common type `{n}`"
  | .extension n =>
    match extType? n with
    | some x => pure (.ext x)
    | none => throw s!"unknown extension type `{n}`"

/-- A record's attributes, resolved. -/
def convertAttrsT (D : Defs) (inl : Name → Except String CedarType) (ns : Option Name) :
    List (String × AttrType) → Except String (List (String × QualifiedType))
  | [] => pure []
  | (k, ⟨ty, required, _⟩) :: rest => do
    pure ((k, qualified required (← convertT D inl ns ty)) :: (← convertAttrsT D inl ns rest))

end

/-- A schema type written in namespace `ns`, as a Cedar type, every common type inlined:
resolved, in its own namespace, with one unit of `fuel` less. A chain of references that
exhausts the fuel is a cycle. -/
def convert (D : Defs) : Nat → Option Name → SchemaType → Except String CedarType
  | 0, ns, t => convertT D (fun c => throw s!"a cycle of common types through `{c}`") ns t
  | fuel + 1, ns, t => convertT D (fun c =>
      match D.commons.find? (·.name == c) with
      | some d => convert D fuel d.ns d.ty
      | none => throw s!"undeclared common type `{c}`") ns t

/-- The fuel that bounds a chain of inlined references: a longer chain repeats a common type. -/
def Defs.fuel (D : Defs) : Nat := D.commons.length + 1

/-- A shape or context, which must be a record. -/
def convertRecord (D : Defs) (ns : Option Name) (what : String) (ty : SchemaType) :
    Except String RecordType := do
  match ← convert D D.fuel ns ty with
  | .record r => pure r
  | _ => throw s!"the {what} is not a record"

/-! ## Hierarchies -/

/-- The nodes reachable from `start` through `parents`, in at most `fuel` rounds; a round adds
the parents of the nodes found so far, and the search stops when a round adds nothing. -/
def closure {α : Type} [DecidableEq α] (parents : α → List α) : Nat → List α → List α
  | 0, found => found
  | fuel + 1, found =>
    let next := (found ++ found.flatMap parents).eraseDups
    if next.length ≤ found.length then found else closure parents fuel next

/-- The ancestors of a node: the nodes reachable through one or more parent edges, `n` bounding
the number of nodes. -/
def ancestorsOf {α : Type} [DecidableEq α] (parents : α → List α) (n : Nat) (x : α) : List α :=
  closure parents (n + 1) (parents x).eraseDups

/-! ## Checks -/

/-- The common type names Cedar reserves for its JSON format (`CommonTypeId`). -/
def reservedCommonIds : List String :=
  ["Bool", "Boolean", "Entity", "Extension", "Long", "Record", "Set", "String"]

/-- An error unless `b`. -/
def check (b : Bool) (m : String) : Except String Unit := if b then pure () else throw m

/-- The checks of one namespace (`from_namespace_definition`, and the invariants of Cedar's
types): no entity type named `Action`, no action attributes, no name declared twice, no reserved
name. -/
def checkNamespace (ns : Option String) (d : NamespaceDef) : Except String Unit := do
  check (!(nsName ns).any isReserved) s!"reserved namespace `{ns.getD ""}`"
  check (!d.entityTypes.any (·.1 == "Action")) "an entity type named `Action` is declared"
  check (!d.actions.any (·.2.attributes.isSome)) "action attributes are not supported"
  check (d.commonTypes.map (·.1)).Nodup "a common type is declared twice"
  check (d.entityTypes.map (·.1)).Nodup "an entity type is declared twice"
  check (d.actions.map (·.1)).Nodup "an action is declared twice"
  check (!d.commonTypes.any fun (id, _) => reservedCommonIds.contains id || id == "__cedar")
    "a reserved common type name"
  check (!d.entityTypes.any (·.1 == "__cedar")) "a reserved entity type name"

/-- RFC 70: no unqualified type of the root namespace shares its basename with a qualified one
(other than a builtin), and no root action its id with a namespaced one. -/
def checkShadowing (f : Fragment) : Except String Unit := do
  let names := userEntities f ++ (userCommons f ++ cedarCommons).map (·.name)
  check (!names.any fun u => u.path.isEmpty &&
      names.any fun n => !n.path.isEmpty && !isReserved n && n.id == u.id)
    "a type of the root namespace is shadowed by a namespaced declaration"
  let acts := userActions f
  check (!acts.any fun a => a.ty.path.isEmpty &&
      acts.any fun b => !b.ty.path.isEmpty && b.eid == a.eid)
    "an action of the root namespace is shadowed by a namespaced action"

/-! ## The schema -/

/-- A declared entity type, resolved: its parents, and its entry without ancestors. -/
structure EntityEntry where
  name : EntityType
  parents : List EntityType
  kind : Option (RecordType × Option CedarType)
  choices : List String

/-- An entity type's declaration, resolved in its namespace. -/
def resolveEntityType (D : Defs) (ns : Option Name) (id : String) (d : EntityTypeDef) :
    Except String EntityEntry := do
  let name := qualifyWith ns ⟨id, []⟩
  match d.kind with
  | .enum choices =>
    check (!choices.isEmpty) s!"the enum entity type `{name}` has no choices"
    pure { name, parents := [], kind := none, choices }
  | .standard memberOf shape tags =>
    let parents ← memberOf.mapM fun p =>
      match D.resolveEntity ns p with
      | some e =>
        if D.declared.contains e then pure e
        else throw s!"the parent `{p}` of `{name}` is not a declared entity type"
      | none => throw s!"undeclared entity type `{p}`"
    let attrs ← convertRecord D ns s!"shape of `{name}`" shape
    let tags ← tags.mapM (convert D D.fuel ns)
    pure { name, parents, kind := some (attrs, tags), choices := [] }

/-- A declared action, resolved: its parents, and its entry without ancestors. -/
structure ActionEntry where
  uid : EntityUID
  parents : List EntityUID
  principals : List EntityType
  resources : List EntityType
  context : RecordType

/-- An `appliesTo` entity type, which must be a declared entity type. -/
def resolveApplies (D : Defs) (ns : Option Name) (raw : String) : Except String EntityType :=
  match D.resolveEntity ns raw with
  | some e =>
    if D.declared.contains e then pure e
    else throw s!"`{raw}` in an `appliesTo` is not a declared entity type"
  | none => throw s!"undeclared entity type `{raw}`"

/-- An action's declaration, resolved in its namespace. -/
def resolveAction (D : Defs) (ns : Option Name) (id : String) (d : ActionDef) :
    Except String ActionEntry := do
  let uid : EntityUID := ⟨actionType ns, id⟩
  let parents ← ((d.memberOf.getD []).mapM fun m =>
    match D.resolveAction ns m with
    | some u => pure u
    | none => throw s!"undeclared action `{m.id}` in the `memberOf` of `{id}`")
  match d.appliesTo with
  | none => pure { uid, parents, principals := [], resources := [], context := Map.empty }
  | some a => do
    let principals ← a.principalTypes.mapM (resolveApplies D ns)
    let resources ← a.resourceTypes.mapM (resolveApplies D ns)
    let context ← convertRecord D ns s!"context of `{id}`" a.context
    pure { uid, parents, principals, resources, context }

/-- Every common type resolves (Cedar converts each, used or not). -/
def checkCommons (D : Defs) : Except String Unit :=
  D.commons.forM fun d => do let _ ← convert D D.fuel d.ns d.ty

/-- The fragment's entity types, resolved, in the fragment's order. -/
def resolveEntityTypes (D : Defs) (f : Fragment) : Except String (List EntityEntry) :=
  f.flatMapM fun (ns, d) => d.entityTypes.mapM fun (id, e) => resolveEntityType D (nsName ns) id e

/-- The fragment's actions, resolved, in the fragment's order. -/
def resolveActions (D : Defs) (f : Fragment) : Except String (List ActionEntry) :=
  f.flatMapM fun (ns, d) => d.actions.mapM fun (id, a) => resolveAction D (nsName ns) id a

/-- The parents of an entity type. -/
def entityParents (ets : List EntityEntry) (n : EntityType) : List EntityType :=
  ((ets.find? (·.name == n)).map (·.parents)).getD []

/-- The parents of an action. -/
def actionParents (acts : List ActionEntry) (u : EntityUID) : List EntityUID :=
  ((acts.find? (·.uid == u)).map (·.parents)).getD []

/-- The ancestors of an action. -/
def actionAncestors (acts : List ActionEntry) (u : EntityUID) : List EntityUID :=
  ancestorsOf (actionParents acts) acts.length u

/-- An entity type's entry, with its ancestors among `ets`. -/
def entityEntryOf (ets : List EntityEntry) (e : EntityEntry) : EntitySchemaEntry :=
  match e.kind with
  | some (attrs, tags) =>
    .standard ⟨Set.make (ancestorsOf (entityParents ets) ets.length e.name), attrs, tags⟩
  | none => .enum (Set.make e.choices)

/-- An action's entry, with its ancestors among `acts`. -/
def actionEntryOf (acts : List ActionEntry) (a : ActionEntry) : ActionSchemaEntry :=
  ⟨Set.make a.principals, Set.make a.resources, Set.make (actionAncestors acts a.uid), a.context⟩

/-- The entity types as cedar-lean's entity schema, with their ancestors. -/
def entitySchema (ets : List EntityEntry) : Cedar.Validation.EntitySchema :=
  Map.make (ets.map fun e => (e.name, entityEntryOf ets e))

/-- The actions as cedar-lean's action schema, with their ancestors. -/
def actionSchema (acts : List ActionEntry) : Cedar.Validation.ActionSchema :=
  Map.make (acts.map fun a => (a.uid, actionEntryOf acts a))

/-! ## External declarations (Cedar 4.14, RFC 116) -/

/-- The entity types the fragment declares `external`, qualified, in the fragment's order. -/
def externalEntityTypes (f : Fragment) : List EntityType :=
  f.flatMap fun (ns, d) =>
    (d.entityTypes.filter (·.2.external)).map fun (id, _) => qualifyWith (nsName ns) ⟨id, []⟩

/-- The actions the fragment declares `external`, in the fragment's order. -/
def externalActions (f : Fragment) : List EntityUID :=
  f.flatMap fun (ns, d) =>
    (d.actions.filter (·.2.external)).map fun (id, _) => ⟨actionType (nsName ns), id⟩

/-- No entity type declared `external` has an enumerated entity type among its ancestors, which no
definition of it could list (Cedar's `check_no_external_with_enum_ancestor`). -/
def checkExternalAncestors (f : Fragment) (ets : List EntityEntry) : Except String Unit :=
  (externalEntityTypes f).forM fun e =>
    match (ancestorsOf (entityParents ets) ets.length e).find? fun a =>
        (ets.find? (·.name == a)).any (·.kind.isNone) with
    | some a =>
      let text := fun (n : Name) => "::".intercalate (n.path ++ [n.id])
      throw s!"external entity type `{text e}` cannot have the enum entity type `{text a}` as an ancestor"
    | none => pure ()

end Resolve

open Resolve

/-- The fragment as Cedar compiles it (`ValidatorSchema` from a `SchemaFragment`), with ancestor
sets. An error has category `cedarSchema`. -/
def resolveExcept (f : Fragment) : Except String Cedar.Validation.Schema := do
  f.forM fun (ns, d) => checkNamespace ns d
  check (f.map (·.1)).Nodup "a namespace is declared twice"
  checkShadowing f
  let D := Defs.ofFragment f
  checkCommons D
  let ets ← resolveEntityTypes D f
  let acts ← resolveActions D f
  check (!acts.any fun a => (actionAncestors acts a.uid).contains a.uid)
    "the action hierarchy has a cycle"
  checkExternalAncestors f ets
  pure { ets := entitySchema ets, acts := actionSchema acts }

/-- The fragment as Cedar compiles it. An error has category `cedarSchema`. -/
def resolve (fragment : Fragment) : Result Cedar.Validation.Schema :=
  (resolveExcept fragment).mapError fun m =>
    { stage := .resolveSchema, category := .cedarSchema, message := m }

end Dogwood.Frontend.CedarSchema
