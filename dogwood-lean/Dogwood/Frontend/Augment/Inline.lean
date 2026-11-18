import Dogwood.Frontend.Augment.Util

/-!
# Inlining action contexts that are common-type references

An action's context may be a reference to a common type (`context: Ctx`). Before the hoisted
fields can be added to the context record, the crate replaces the reference by an inlined copy
of the record it names (`inline_selected_context_references`, `schema_augment.rs`): it
resolves every name of the fragment as Cedar does
(`Fragment::to_internal_name_fragment_with_resolved_types`), follows the reference to its
terminal type, deep-inlines the common-type references nested in it, pins the bare extension
type names to `__cedar::`, and reads the result back as JSON schema (so that the common types
`String` and `Long` become the primitive types).

Cedar's name resolution (`ConditionalName::resolve`): a name written with a namespace is taken
as written; an unqualified name `N` written in the namespace `NS` is `NS::N` if that is defined,
else `N`. A common type is preferred to an entity type of the same name. The builtin types
`Bool`, `Long`, `String` and the extension types are common types in the `__cedar` namespace and,
unless the root namespace defines that name, in the root namespace too.

Cedar's own error messages are not reproduced: an undefined name is reported as `failed to
resolve type: <name>`, and the fragment-level checks Cedar runs before resolution
(`ValidatorSchemaFragment::from_schema_fragment`) and the resolution of action groups are not
modelled. For a schema whose common types refer to each other in a cycle through a record or a
set, the crate's deep inlining finds a reference to a type it is inlining around it, and reports
a cyclic chain; here the recursion is bounded instead, by more than any acyclic inlining needs,
and its exhaustion reports the same message.
-/

namespace Dogwood.Frontend.Augment

open CedarSchema

/-- Cedar's extension types (`Extensions::all_available().ext_types()`). -/
def extensionTypes : List String := ["datetime", "decimal", "duration", "ipaddr"]

/-- The type names Cedar defines: the primitive types and the extension types. -/
def builtinTypes : List String := ["Bool", "Long", "String"] ++ extensionTypes

/-- The type names a fragment defines (Cedar `AllDefs`, with the builtins), fully qualified. -/
structure Defs where
  common : List String
  entity : List String

/-- The fully qualified names the fragment defines. -/
def Defs.ofFragment (f : Fragment) : Defs :=
  let common := f.flatMap fun (ns, nd) => nd.commonTypes.map fun (id, _) => qualify ns id
  let entity := f.flatMap fun (ns, nd) => nd.entityTypes.map fun (id, _) => qualify ns id
  { common, entity }

/-- `n` is a common type: a user's, `__cedar::<builtin>`, or a builtin's root alias that the
root namespace does not define. -/
def Defs.isCommon (D : Defs) (n : String) : Bool :=
  D.common.contains n || builtinTypes.any (fun b => n == "__cedar::" ++ b) ||
    (builtinTypes.contains n && !D.entity.contains n)

/-- `n` is an entity type. -/
def Defs.isEntity (D : Defs) (n : String) : Bool := D.entity.contains n

/-- What a reference may name. -/
inductive RefKind where
  | common | entity | commonOrEntity
deriving DecidableEq, BEq

/-- The fully qualified name the name `n`, written in the namespace `ns`, resolves to (Cedar
`ConditionalName::resolve`). -/
def Defs.resolveName (D : Defs) (ns : Option String) (kind : RefKind) (n : String) :
    Except String String :=
  let candidates := if isUnqualified n then
      match ns with
      | some m => [m ++ "::" ++ n, n]
      | none => [n]
    else [n]
  match candidates.find? fun p =>
      (kind != .entity && D.isCommon p) || (kind != .common && D.isEntity p) with
  | some p => .ok p
  | none => .error s!"failed to resolve type: {n}"

mutual

/-- The type, written in the namespace `ns`, with every name fully qualified and each
entity-or-common reference resolved to an entity type or a common-type reference (Cedar's
`fully_qualify_type_references`, then `resolve_entity_or_common_type`). -/
def resolveType (D : Defs) (ns : Option String) : SchemaType → Except String SchemaType
  | .commonRef n => return .commonRef (← D.resolveName ns .common n)
  | .entity n => return .entity (← D.resolveName ns .entity n)
  | .entityOrCommon n => do
    let r ← D.resolveName ns .commonOrEntity n
    return if D.isCommon r then .commonRef r else .entity r
  | .set t => return .set (← resolveType D ns t)
  | .record attrs add => return .record (← resolveAttrs D ns attrs) add
  | .string => pure .string
  | .long => pure .long
  | .boolean => pure .boolean
  | .extension n => pure (.extension n)

def resolveAttrs (D : Defs) (ns : Option String) :
    List (String × AttrType) → Except String (List (String × AttrType))
  | [] => pure []
  | (k, ⟨t, req, anns⟩) :: rest => do
    return (k, ⟨← resolveType D ns t, req, anns⟩) :: (← resolveAttrs D ns rest)

end

/-- The fragment's common types, by fully qualified name, with their types resolved; an error
when some name of the fragment does not resolve (common types, entity types and action
`appliesTo`, in Cedar's order: namespaces, then a namespace's common types, entity types and
actions). -/
def resolvedDefs (f : Fragment) : Except String (List (String × SchemaType)) := do
  let D := Defs.ofFragment f
  let perNs ← f.mapM fun (ns, nd) => do
    let commons ← nd.commonTypes.mapM fun (id, ct) => do
      return (qualify ns id, ← resolveType D ns ct.ty)
    for (_, et) in nd.entityTypes do
      match et.kind with
      | .standard memberOf shape tags =>
        for m in memberOf do
          let _ ← D.resolveName ns .entity m
        let _ ← resolveType D ns shape
        if let some t := tags then
          let _ ← resolveType D ns t
      | .enum _ => pure ()
    for (_, a) in nd.actions do
      if let some ap := a.appliesTo then
        for p in ap.principalTypes ++ ap.resourceTypes do
          let _ ← D.resolveName ns .entity p
        let _ ← resolveType D ns ap.context
    return commons
  return perNs.flatten

/-- The name a context names, when it is a type reference (the crate's `context_reference_name`). -/
def contextReferenceName : SchemaType → Option String
  | .commonRef n => some n
  | .entityOrCommon n => some n
  | _ => none

/-- A resolved type read back as JSON schema: `{"type": "String"}` is the primitive `String`,
likewise `Long` and `Boolean`; any other name stays a common-type reference. -/
def readBack : SchemaType → SchemaType
  | .commonRef "String" => .string
  | .commonRef "Long" => .long
  | .commonRef "Boolean" => .boolean
  | t => t

/-- The message of a chain of references that comes back to a type it has visited. -/
def cyclicChain : String := "context type reference chain is cyclic and cannot be resolved"

/-- Follow a chain of common-type references through `defs` to its end; a bare extension type
name at the end is pinned to `__cedar::` (the chase of the crate's `normalize_value`). -/
def chase (defs : List (String × SchemaType)) : Nat → List String → SchemaType →
    Except String SchemaType
  | 0, _, _ => .error cyclicChain
  | fuel + 1, visited, .commonRef n =>
    match defs.lookup n with
    | some d => if visited.contains n then .error cyclicChain else chase defs fuel (n :: visited) d
    | none => .ok (if extensionTypes.contains n then .commonRef ("__cedar::" ++ n) else .commonRef n)
  | _ + 1, _, t => .ok t

mutual

/-- The resolved type with every nested common-type reference that `defs` defines inlined
(the crate's `normalize_resolved_type`), read back as JSON schema. An attribute keeps its
`required` flag and annotations. `fuel` bounds the depth. -/
def normalizeType (defs : List (String × SchemaType)) : Nat → SchemaType → Except String SchemaType
  | 0, _ => .error cyclicChain
  | fuel + 1, t => do
    match ← chase defs (defs.length + 1) [] t with
    | .record attrs add => return .record (← normalizeAttrs defs fuel attrs) add
    | .set e => return .set (← normalizeType defs fuel e)
    | t' => return readBack t'

def normalizeAttrs (defs : List (String × SchemaType)) (fuel : Nat) :
    List (String × AttrType) → Except String (List (String × AttrType))
  | [] => pure []
  | (k, ⟨t, req, anns⟩) :: rest => do
    return (k, ⟨← normalizeType defs fuel t, req, anns⟩) :: (← normalizeAttrs defs fuel rest)

end

mutual

/-- The number of nodes of a type. -/
def typeNodes : SchemaType → Nat
  | .set t => typeNodes t + 1
  | .record attrs _ => attrsNodes attrs + 1
  | _ => 1

def attrsNodes : List (String × AttrType) → Nat
  | [] => 0
  | (_, ⟨t, _, _⟩) :: rest => typeNodes t + attrsNodes rest

end

/-- Follow the context reference chain of the action `id` to its terminal type, through at most
`bound` references (the crate's top-level chase in `inline_selected_context_references`). -/
def chaseContext (defs : List (String × SchemaType)) (id : String) (bound : Nat) :
    Nat → Nat → SchemaType → Except String SchemaType
  | 0, _, t => .ok t
  | fuel + 1, steps, t =>
    match t with
    | .commonRef n =>
      if steps + 1 > bound then
        .error s!"action `{escapedActionId id}` context reference is cyclic and cannot be resolved"
      else match defs.lookup n with
        | some next => chaseContext defs id bound fuel (steps + 1) next
        | none => .ok t
    | _ => .ok t

/-- The inlined context of one action, `none` when it is not a reference once resolved. -/
def inlineContext (D : Defs) (defs : List (String × SchemaType)) (ns : Option String)
    (id : String) (context : SchemaType) : Except String (Option SchemaType) := do
  let resolved ← resolveType D ns context
  match resolved with
  | .commonRef _ =>
    let bound := defs.length + 1
    let terminal ← chaseContext defs id bound (bound + 1) 0 resolved
    let depth := attrsNodes (defs.map fun (k, t) => (k, ⟨t, true, []⟩)) + typeNodes terminal + 1
    match normalizeType defs depth terminal with
    | .ok t => return some t
    | .error m => throw s!"action `{escapedActionId id}`: {m}"
  | _ => return none

/-- The `(namespace, action id)` of every action of the fragment, in the fragment's order. -/
def actionKeys (f : Fragment) : List (Option String × String) :=
  f.flatMap fun (ns, nd) => nd.actions.map fun (id, _) => (ns, id)

/-- Inline the context of the action `id` of the namespace `ns`, when `selected` admits it and
its context is a type reference (one step of the crate's Phase A and Phase B). -/
def inlineStep (D : Defs) (defs : List (String × SchemaType)) (selected : Option String → String → Bool)
    (out : Fragment) (key : Option String × String) : Except String Fragment :=
  let (ns, id) := key
  if selected ns id then
    match actionAt out ns id with
    | some a =>
      match a.appliesTo with
      | some ap =>
        if (contextReferenceName ap.context).isSome then
          match inlineContext D defs ns id ap.context with
          | .ok (some t) => .ok (setAction out ns id { a with appliesTo := some { ap with context := t } })
          | .ok none => .ok out
          | .error e => .error e
        else .ok out
      | none => .ok out
    | none => .ok out
  else .ok out

/-- Some action that `selected` admits has a context that is a type reference. -/
def anyReference (f : Fragment) (selected : Option String → String → Bool) : Bool :=
  f.any fun (ns, nd) => nd.actions.any fun (id, a) =>
    selected ns id && (a.appliesTo.any fun ap => (contextReferenceName ap.context).isSome)

/-- Inline the contexts of the actions `selected` admits that are type references (the crate's
`inline_selected_context_references`). -/
def inlineSelectedContexts (f : Fragment) (selected : Option String → String → Bool) :
    Except String Fragment :=
  if !anyReference f selected then .ok f
  else
    match resolvedDefs f with
    | .error e => .error s!"resolve schema type references: {e}"
    | .ok defs => (actionKeys f).foldlM (inlineStep (Defs.ofFragment f) defs selected) f

end Dogwood.Frontend.Augment
