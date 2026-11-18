import Dogwood.Frontend.Augment.Check
import Dogwood.Frontend.Augment.Inline
import Dogwood.Frontend.Augment.TypeText

/-!
# Provider declarations, schema augmentation, and the providers of a lowered set (WP4)

The crate's `ProviderDeclarations::check` (`extension/provider/declarations.rs`, in
`Augment/Check.lean`), `cedarify::augment_schema` and `cedarify/schema_augment.rs` (without
`scope_target_actions`), and the provider resolution of `api::merge`.

Augmentation edits the action schema's fragment in three passes, as `augment_schema` does:

1. **Provider enums** (`add_provider_entity_types`): each declared enum a provider call uses is
   added to the *home* namespace (`ProviderDecls.providerEnumHome`) under its exported name,
   tagged `@dogwood_provider_enum("<declared>")`; a name that clashes with the action schema's
   is an error.
2. **Temporal fields** (`add_bool_context_fields`): when the set has a temporal leaf, every
   action context that is a common-type reference is inlined (`Augment/Inline.lean`); a context
   that declares a leaf's attribute name is refused; and each leaf's attribute `<name>: Bool`,
   required, is added to the context of each of its target actions.
3. **Provider fields** (`add_provider_context_fields`): the contexts of the target actions are
   inlined; a context that declares `providers`, other than as a reference to its namespace's
   shared provider type of an earlier lowering, is refused; each namespace holding a target
   action (or an earlier generated type) gets one common type `DogwoodProviders`
   (`DogwoodProviders_<n>` when the name is taken), tagged `@dogwood_provider_context("1.1")`,
   whose record holds every provider field, typed by parsing the text `type __PR = { f: T, … };`
   (`Augment/TypeText.lean`), a builtin name that some namespace declares pinned to `__cedar::`;
   each target action gets the required attribute `providers: DogwoodProviders`.

A hoisted field's target actions are those cedarify computed (`ContextField.targetActions`,
`ProviderField.targetActions`). The crate's temporal pass recomputes them with
`scope_target_actions` on the fragment as the passes leave it, which has the same actions, action
groups and `appliesTo` as the action schema, so the two agree; its provider pass uses
`ProviderField.target_actions` as cedarify computed them. The result is the fragment as the
export reads it back from Cedar's JSON form (`readBackFragment`). Not modelled: the errors of
Cedar's fragment conversion (`assemble augmented schema fragment: …`); every bundle of the corpus
that reaches augmentation passes it.
-/

namespace Dogwood.Frontend.Augment

open CedarSchema
open ProviderDecls (Declarations ProviderDecl EntityTypeDecl)

/-- An augmentation error, with the crate's category. -/
def augmentError (message : String) : Error :=
  { stage := .augment, category := .cedarify, message }

/-- An augmentation pass's error message, prefixed with the pass's name. -/
def withPrefix {α : Type} (pre : String) (r : Except String α) : Result α :=
  match r with
  | .ok a => .ok a
  | .error m => .error (augmentError (pre ++ m))

/-! ## Provider enums -/

/-- The annotation tagging an injected provider enum with its declared name. -/
def providerEnumAnnotation : String := "dogwood_provider_enum"

/-- The namespace `ns` declares a common or entity type named `base`. -/
def declaresType (f : Fragment) (ns : Option String) (base : String) : Bool :=
  match getNs f ns with
  | some nd => nd.commonTypes.any (·.1 == base) || nd.entityTypes.any (·.1 == base)
  | none => false

/-- The clash of one used provider enum with the action schema, if any (the checks of
`add_provider_entity_types`). -/
def enumClash (f : Fragment) (home : Option String) (declared exported : String) :
    Except String (Option String) := do
  if let some (ns, base) := rsplitOnce declared then
    if declaresType f (← nsKey ns) base then
      return some s!"entity type `{declared}` is also declared by the policy schema, so `{declared}::\"…\"` would be ambiguous; rename one of them"
  let base := ProviderDecls.exportedEnumBasename declared
  let reused := match getNs f home with
    | some nd => match nd.entityTypes.lookup base with
      | some et => annotationValue et.annotations providerEnumAnnotation == some (some declared)
      | none => false
    | none => false
  if !reused && declaresType f home base then
    return some s!"entity type `{declared}` is exported as `{exported}`, which the policy schema already declares; rename the policy schema's type"
  if home.isSome && declaresType f none base then
    return some s!"entity type `{declared}` is exported as `{exported}`, which would shadow `{base}` declared in the policy schema's root namespace"
  return none

/-- The entity type an enum declaration is injected as. -/
def enumEntityType (declared : String) (d : EntityTypeDecl) : EntityTypeDef :=
  { kind := .enum d.values
    annotations := (insertKey providerEnumAnnotation declared d.annotations).map fun (k, v) => (k, some v) }

/-- The clashes and the entity types of the used provider enums `names`, in order (the loop of
`add_provider_entity_types`). -/
def enumEntries (f : Fragment) (home : Option String) (d : Declarations)
    (names : List (String × String)) : Except String (List String × List (String × EntityTypeDef)) :=
  names.foldlM (init := ([], [])) fun (errors, entries) (declared, exported) => do
    match ← enumClash f home declared exported with
    | some e => pure (errors ++ [e], entries)
    | none =>
      let decl := (d.entityTypeDecls.lookup declared).getD default
      pure (errors, insertKey (ProviderDecls.exportedEnumBasename declared) (enumEntityType declared decl) entries)

/-- Every annotation key of the injected entity types is an identifier, as Cedar's JSON schema
requires. -/
def checkAnnotationKeys (entries : List (String × EntityTypeDef)) : Except String Unit :=
  match (entries.flatMap fun (_, et) => et.annotations.map (·.1)).find? (!isAnyIdent ·) with
  | some k => .error s!"provider entity types: invalid annotation key `{k}`"
  | none => .ok ()

/-- Inject the declared provider enums in `referenced` into the home namespace (crate
`add_provider_entity_types`). -/
def addProviderEntityTypes (f : Fragment) (d : Declarations) (referenced : List String) :
    Except String Fragment :=
  let names := ProviderDecls.providerEnumNames f d referenced
  if names.isEmpty then
    if d.entityTypeDecls.any fun (n, _) => referenced.contains n then
      .error "no namespace in the policy schema declares actions, so provider entity types have nowhere to go"
    else .ok f
  else
    match ProviderDecls.providerEnumHome f with
    | none => .error "internal: names are only built with a home"
    | some home => do
      let (errors, entries) ← enumEntries f home d names
      if !errors.isEmpty then throw ("\n".intercalate errors)
      checkAnnotationKeys entries
      match getNs f home with
      | some nd => pure (setNs f home
          { nd with entityTypes := entries.foldl (fun m (k, v) => insertKey k v m) nd.entityTypes })
      | none => throw "internal: the home namespace is not in the fragment"

/-! ## Temporal fields -/

/-- The attribute a temporal field is hoisted as: `Bool`, required, without annotations. -/
def boolAttr : AttrType := ⟨.boolean, true, []⟩

/-- The message of a context that is a reference after inlining. -/
def notARecordReference (id : String) : String :=
  s!"action `{escapedActionId id}` context does not resolve to a record type (an action's context must be a record)"

/-- Add the required attribute `name: Bool` to one action's context record (crate
`add_bool_to_named_action`, `add_bool_to_action`). -/
def addBoolToAction (f : Fragment) (name : String) (nsName id : String) : Except String Fragment :=
  match nsKey nsName with
  | .error e => .error e
  | .ok k =>
    match getNs f k with
    | none => .error s!"namespace `{nsName}` not found in schema"
    | some nd =>
      match nd.actions.lookup id with
      | none => .error s!"action `{escapedActionId id}` not found in schema"
      | some a =>
        match a.appliesTo with
        | none => .error s!"action `{escapedActionId id}` has no appliesTo"
        | some ap =>
          match ap.context with
          | .record attrs add =>
            .ok (setAction f k id { a with appliesTo := some { ap with context := .record (insertKey name boolAttr attrs) add } })
          | .commonRef _ => .error (notARecordReference id)
          | _ => .error s!"action `{escapedActionId id}` context is not a record type"

/-- Add one temporal field to the contexts of its target actions (crate `add_one`). -/
def addBoolField (f : Fragment) (field : ContextField) : Except String Fragment :=
  field.targetActions.foldlM (fun f (ns, id) => addBoolToAction f field.fieldName ns id) f

/-- An action's context, if it is an inline record (crate `inline_context_record`). -/
def inlineContextRecord (a : ActionDef) : Option (List (String × AttrType)) :=
  match a.appliesTo with
  | some ap => match ap.context with
    | .record attrs _ => some attrs
    | _ => none
  | none => none

/-- Refuse a fragment in which an action's context declares the name of a hoisted temporal
leaf, whatever its type and whichever actions the leaf targets (crate
`reject_declared_leaf_names`): the first action, in the fragment's order, and the first such
field. -/
def rejectDeclaredLeafNames (f : Fragment) (fields : List ContextField) : Except String Unit :=
  f.forM fun (_, nd) => nd.actions.forM fun (id, a) =>
    match inlineContextRecord a with
    | none => .ok ()
    | some attrs =>
      match fields.find? fun fld => (attrs.lookup fld.fieldName).isSome with
      | some fld => .error s!"action `{escapedActionId id}` declares a context attribute `{fld.fieldName}`, a name lowering reserves for the value of a temporal leaf; rename the attribute"
      | none => .ok ()

/-- Add each temporal field to the contexts of its target actions, after inlining every action
context that is a reference and refusing a context that declares a field's name (crate
`add_bool_context_fields`). -/
def addBoolContextFields (f : Fragment) (fields : List ContextField) : Except String Fragment :=
  if fields.isEmpty then .ok f
  else do
    let f ← inlineSelectedContexts f fun _ _ => true
    rejectDeclaredLeafNames f fields
    fields.foldlM addBoolField f

/-! ## Provider fields -/

/-- The basename of the shared provider type. -/
def sharedProviderTypeBasename : String := "DogwoodProviders"

/-- The annotation tagging the shared provider type, with its representation version. -/
def sharedProviderTypeAnnotation : String := "dogwood_provider_context"

/-- The representation version of the shared provider type. -/
def sharedProviderTypeVersion : String := "1.1"

/-- The common type was generated as the shared provider type (crate `is_dogwood_provider_type`). -/
def isDogwoodProviderType (c : CommonType) : Bool :=
  (annotationValue c.annotations sharedProviderTypeAnnotation).isSome

/-- The first of `DogwoodProviders`, `DogwoodProviders_1`, … that the namespace declares
neither as a common type nor as an entity type (crate `available_shared_provider_type_id`). -/
def availableSharedProviderTypeId (nd : NamespaceDef) : String :=
  let taken := fun (c : String) => nd.commonTypes.any (·.1 == c) || nd.entityTypes.any (·.1 == c)
  let candidate := fun (n : Nat) =>
    if n == 0 then sharedProviderTypeBasename else s!"{sharedProviderTypeBasename}_{n}"
  let bound := nd.commonTypes.length + nd.entityTypes.length + 1
  ((List.range (bound + 1)).find? fun n => !taken (candidate n)).elim sharedProviderTypeBasename candidate

/-- Merge the attributes `source` into `target`; an attribute declared in both must be the same
(crate `merge_provider_attributes`). -/
def mergeProviderAttributes (target source : List (String × AttrType)) :
    Except String (List (String × AttrType)) :=
  source.foldlM (init := target) fun acc (name, attr) =>
    match acc.lookup name with
    | some existing =>
      if existing == attr then .ok (insertKey name attr acc)
      else .error s!"provider field `{name}` was previously declared with a different type"
    | none => .ok (insertKey name attr acc)

/-- The type references the namespace's shared provider type, by its name or its qualified name
(crate `provider_type_reference_matches`). -/
def providerTypeReferenceMatches (ty : SchemaType) (nsName typeName : String) : Bool :=
  match contextReferenceName ty with
  | some r => r == typeName || (!nsName.isEmpty && r == nsName ++ "::" ++ typeName)
  | none => false

/-- The context record's `providers` attribute (crate `provider_attribute`). -/
def providerAttribute (context : SchemaType) (id : String) : Except String (Option AttrType) :=
  match context with
  | .record attrs _ => .ok (attrs.lookup "providers")
  | .commonRef _ => .error (notARecordReference id)
  | _ => .error s!"action `{escapedActionId id}` context is not a record"

/-- The shared provider types the fragment already holds, by namespace, and the provider fields
they declare (the first loop of `add_provider_context_fields`). -/
def existingSharedTypes (f : Fragment) :
    Except String (List (String × String) × List (String × AttrType)) :=
  f.foldlM (init := ([], [])) fun (ids, attrs) (k, nd) => do
    let nsName := namespaceString k
    match nd.commonTypes.filter fun (_, c) => isDogwoodProviderType c with
    | [] => pure (ids, attrs)
    | [(id, c)] =>
      let version := match annotationValue c.annotations sharedProviderTypeAnnotation with
        | some (some v) => if v.isEmpty then none else some v
        | _ => none
      let some version := version
        | throw s!"namespace `{nsName}` contains a Dogwood provider type without a representation version"
      if version != sharedProviderTypeVersion then
        throw s!"namespace `{nsName}` contains a Dogwood provider type with unsupported representation version `{version}`"
      match c.ty with
      | .record existing _ => pure (insertKey nsName id ids, ← mergeProviderAttributes attrs existing)
      | _ => throw s!"Dogwood shared provider type in namespace `{nsName}` is not a record"
    | _ => throw s!"namespace `{nsName}` contains multiple Dogwood-generated provider types"

/-- Give a target namespace without a shared provider type the name of a new one (the second
loop of `add_provider_context_fields`). -/
def assignSharedId (f : Fragment) (ids : List (String × String)) (nsName : String) :
    Except String (List (String × String)) :=
  if (ids.lookup nsName).isSome then .ok ids
  else match nsKey nsName with
    | .error e => .error e
    | .ok k =>
      match getNs f k with
      | some nd => .ok (insertKey nsName (availableSharedProviderTypeId nd) ids)
      | none => .error s!"namespace `{nsName}` not found"

/-- The name of the shared provider type of a target namespace. -/
def sharedNameOf (ids : List (String × String)) (nsName : String) : String :=
  (ids.lookup nsName).getD sharedProviderTypeBasename

/-- Refuse a fragment in which an action's context declares `providers`, a name lowering
reserves for the values of provider leaves, unless the attribute refers to its namespace's
Dogwood shared provider type (`shared`), as an earlier lowering's does (crate
`reject_declared_providers`). Every action is checked, on a copy of the fragment whose contexts
are all inline. -/
def rejectDeclaredProviders (f : Fragment) (shared : List (String × String)) :
    Except String Unit := do
  let inlined ← inlineSelectedContexts f fun _ _ => true
  inlined.forM fun (k, nd) => nd.actions.forM fun (id, a) =>
    match (inlineContextRecord a).bind (·.lookup "providers") with
    | none => .ok ()
    | some attr =>
      let fedForward := match shared.lookup (namespaceString k) with
        | some sid => providerTypeReferenceMatches attr.ty (namespaceString k) sid
        | none => false
      if fedForward then .ok ()
      else .error s!"action `{escapedActionId id}` declares a context attribute `providers`, a name lowering reserves for the values of provider leaves; rename the attribute"

/-- The existing `providers` attribute of a target action, which refers to Dogwood's shared
provider type (`rejectDeclaredProviders`), checked to be this namespace's (the third loop of
`add_provider_context_fields`). -/
def checkExistingProviders (f : Fragment) (sharedIds : List (String × String))
    (attrs : List (String × AttrType)) (nsName id : String) :
    Except String (List (String × AttrType)) := do
  let some nd := getNs f (← nsKey nsName) | throw s!"namespace `{nsName}` not found"
  let some a := nd.actions.lookup id | throw s!"action `{escapedActionId id}` not found"
  let some ap := a.appliesTo | throw s!"action `{escapedActionId id}` has no appliesTo"
  match ← providerAttribute ap.context id with
  | none => return attrs
  | some attr =>
    let sharedName := sharedNameOf sharedIds nsName
    if !providerTypeReferenceMatches attr.ty nsName sharedName then
      throw s!"action `{escapedActionId id}` already has a `providers` attribute that is not Dogwood's shared provider type"
    match nd.commonTypes.lookup sharedName with
    | none => throw s!"action `{escapedActionId id}` references missing Dogwood shared provider type"
    | some c =>
      if !isDogwoodProviderType c then
        throw s!"action `{escapedActionId id}` references `{sharedName}`, but that common type was not generated by Dogwood"
      return attrs

/-- Write the shared provider type `sharedId` of one namespace, with the record `allAttrs` (the
fourth loop of `add_provider_context_fields`). -/
def writeSharedType (allAttrs : List (String × AttrType)) (out : Fragment)
    (entry : String × String) : Except String Fragment :=
  let (nsName, sharedId) := entry
  match nsKey nsName with
  | .error e => .error e
  | .ok k =>
    match getNs out k with
    | none => .error s!"namespace `{nsName}` not found"
    | some nd =>
      let ty := SchemaType.record allAttrs false
      let common := match nd.commonTypes.lookup sharedId with
        | some c => { c with ty }
        | none => { ty, annotations := [(sharedProviderTypeAnnotation, some sharedProviderTypeVersion)] }
      .ok (setNs out k { nd with commonTypes := insertKey sharedId common nd.commonTypes })

/-- The attribute `providers` of a target action, pointing at the shared provider type
`shared`; `none` when the existing attribute is not such a reference. -/
def providersAttr (existing : Option AttrType) (nsName sharedName : String) : Option AttrType :=
  match existing with
  | some attr => if providerTypeReferenceMatches attr.ty nsName sharedName then some attr else none
  | none => some ⟨.commonRef sharedName, true, []⟩

/-- Point one target action's `providers` attribute at the shared provider type (crate
`insert_provider_reference`). -/
def insertProviderReference (f : Fragment) (nsName id sharedName : String) :
    Except String Fragment :=
  match nsKey nsName with
  | .error e => .error e
  | .ok k =>
    match actionAt f k id with
    | none => .error s!"action `{escapedActionId id}` not found"
    | some a =>
      match a.appliesTo with
      | none => .error s!"action `{escapedActionId id}` has no appliesTo"
      | some ap =>
        match ap.context with
        | .record attrs add =>
          match providersAttr (attrs.lookup "providers") nsName sharedName with
          | some attr =>
            .ok (setAction f k id { a with appliesTo := some { ap with context := .record (insertKey "providers" attr attrs) add } })
          | none => .error s!"action `{escapedActionId id}` already has a `providers` attribute that is not Dogwood's shared provider type"
        | .commonRef _ => .error (notARecordReference id)
        | _ => .error s!"action `{escapedActionId id}` context is not a record"

/-- The order of `(namespace, action)` pairs, as a `BTreeSet` of them iterates. -/
def pairLe (a b : String × String) : Bool := a.1 < b.1 || (a.1 == b.1 && decide (a.2 ≤ b.2))

/-- The target actions of the provider fields, sorted and without duplicates. -/
def providerTargets (fields : List ProviderField) : List (String × String) :=
  ((fields.flatMap (·.targetActions)).mergeSort pairLe).eraseDups

/-- The namespaces of the target actions, sorted and without duplicates. -/
def targetNamespaces (targets : List (String × String)) : List String :=
  ((targets.map (·.1)).mergeSort fun a b => decide (a ≤ b)).eraseDups

/-- The text the crate parses to type the provider fields: `type __PR = { f1: T1, … };`. -/
def providerTypeText (fields : List ProviderField) : String :=
  "type __PR = { " ++ ", ".intercalate (fields.map fun f => s!"{f.fieldName}: {f.cedarType}") ++ " };"

/-- The provider fields' attributes, as Cedar parses the text `providerTypeText`. -/
def synthesizedAttrs (fields : List ProviderField) : Except String (List (String × AttrType)) :=
  let synth := providerTypeText fields
  match TypeText.parseCommonTypeDecl synth with
  | .ok (.record attrs _) => .ok attrs
  | .ok _ => .error "internal: synthesized providers type is not a record"
  | .error e => .error s!"synthesize providers type: {e} (from `{synth}`)"

/-- The builtin types a provider field's type text may name bare: the primitives and Cedar's
extension types. -/
def builtinTypeNames : List String :=
  ["String", "Long", "Bool", "decimal", "ipaddr", "datetime", "duration"]

mutual

/-- A type with every bare reference to a builtin whose name is in `declared` written
`__cedar::<name>`, which no declaration captures (crate `pin_builtin_names`). -/
def pinBuiltinNames (declared : List String) : SchemaType → SchemaType
  | .entityOrCommon n =>
    if builtinTypeNames.contains n && declared.contains n then .entityOrCommon ("__cedar::" ++ n)
    else .entityOrCommon n
  | .set t => .set (pinBuiltinNames declared t)
  | .record attrs add => .record (pinBuiltinAttrs declared attrs) add
  | t => t

def pinBuiltinAttrs (declared : List String) : List (String × AttrType) → List (String × AttrType)
  | [] => []
  | (k, ⟨t, req, anns⟩) :: rest => (k, ⟨pinBuiltinNames declared t, req, anns⟩) :: pinBuiltinAttrs declared rest

end

/-- The basenames of the common and entity types the fragment declares, in any namespace. -/
def declaredTypeNames (f : Fragment) : List String :=
  f.flatMap fun (_, nd) => nd.commonTypes.map (·.1) ++ nd.entityTypes.map (·.1)

/-- Define every provider field in one shared common type per touched namespace, and reference
it from each target action (crate `add_provider_context_fields`). The fields' types are parsed
in the root namespace, and resolved in the namespace of a shared type: a builtin name that some
namespace declares is pinned to `__cedar::` (`pinBuiltinNames`). -/
def addProviderContextFields (f : Fragment) (fields : List ProviderField) : Except String Fragment :=
  if fields.isEmpty then .ok f
  else
    let targets := providerTargets fields
    if targets.isEmpty then .ok f
    else do
      let f ← inlineSelectedContexts f fun ns id => targets.contains (namespaceString ns, id)
      let newAttrs := pinBuiltinAttrs (declaredTypeNames f) (← synthesizedAttrs fields)
      let (existingIds, existingAttrs) ← existingSharedTypes f
      rejectDeclaredProviders f existingIds
      let sharedIds ← (targetNamespaces targets).foldlM (assignSharedId f) existingIds
      let allAttrs ← targets.foldlM (fun acc (ns, id) => checkExistingProviders f sharedIds acc ns id)
        existingAttrs
      let allAttrs ← mergeProviderAttributes allAttrs newAttrs
      let out ← sharedIds.foldlM (writeSharedType allAttrs) f
      targets.foldlM (fun out (ns, id) => insertProviderReference out ns id (sharedNameOf sharedIds ns)) out

/-! ## The augmented schema -/

/-- The names of common types that Cedar's JSON schema format cannot reference with
`{"type": …}` alone. -/
def jsonTypeKeywords : List String := ["Set", "Record", "Entity", "EntityOrCommon", "Extension"]

mutual

/-- A type as Cedar's JSON form reads it back (`readBack` at every node); an error for a
reference that the JSON form cannot express. -/
def readBackType : SchemaType → Except String SchemaType
  | .commonRef n => if jsonTypeKeywords.contains n then .error n else .ok (readBack (.commonRef n))
  | .set t => return .set (← readBackType t)
  | .record attrs add => return .record (← readBackAttrs attrs) add
  | t => .ok t

def readBackAttrs : List (String × AttrType) → Except String (List (String × AttrType))
  | [] => pure []
  | (k, ⟨t, req, anns⟩) :: rest => return (k, ⟨← readBackType t, req, anns⟩) :: (← readBackAttrs rest)

end

/-- The fragment as the export reads it back from Cedar's JSON form
(`SchemaFragment::to_json_value`, then `Fragment::from_json_value`). -/
def readBackFragment (f : Fragment) : Except String Fragment :=
  f.mapM fun (k, nd) => do
    let commonTypes ← nd.commonTypes.mapM fun (id, c) => return (id, { c with ty := ← readBackType c.ty })
    let entityTypes ← nd.entityTypes.mapM fun (id, e) => match e.kind with
      | .standard m shape tags => do
        return (id, { e with kind := .standard m (← readBackType shape) (← tags.mapM readBackType) })
      | .enum _ => pure (id, e)
    let actions ← nd.actions.mapM fun (id, a) => match a.appliesTo with
      | some ap => do return (id, { a with appliesTo := some { ap with context := ← readBackType ap.context } })
      | none => pure (id, a)
    return (k, { nd with commonTypes, entityTypes, actions })

/-- The export's error for a fragment that Cedar's JSON form cannot express. -/
def roundTripError : Error :=
  { stage := .augment, category := .«export»
    message := "the augmented fragment does not round-trip through JSON" }

/-- The first hoisted name declared twice, among the temporal fields, then among the provider
fields. -/
def duplicateHoistedName (contextFields : List ContextField) (providerFields : List ProviderField) :
    Option String :=
  (firstDuplicate (contextFields.map (·.fieldName))).orElse fun _ =>
    firstDuplicate (providerFields.map (·.fieldName))

/-- The provider-enum pass, when there are declarations. -/
def enumPass (fragment : CedarSchema.Fragment) (decls : Option Declarations)
    (referencedEnums : List String) : Result CedarSchema.Fragment :=
  match decls with
  | some d => withPrefix "provider entity types: " (addProviderEntityTypes fragment d referencedEnums)
  | none => .ok fragment

/-- Augment the action schema with the referenced provider enums and the hoisted fields (crate
`augment_schema`), before the conversion to Cedar's `SchemaFragment`. An error has category
`cedarify`. -/
def augmentSchema (fragment : CedarSchema.Fragment) (decls : Option Declarations)
    (referencedEnums : List String) (contextFields : List ContextField)
    (providerFields : List ProviderField) : Result CedarSchema.Fragment :=
  match duplicateHoistedName contextFields providerFields with
  | some name => .error (augmentError s!"hoisted context field `{name}` is declared more than once")
  | none => do
    let f ← enumPass fragment decls referencedEnums
    let f ← withPrefix "schema augmentation failed: " (addBoolContextFields f contextFields)
    withPrefix "provider schema augmentation failed: " (addProviderContextFields f providerFields)

/-- Augment the action schema with the referenced provider enums and the hoisted fields (crate
`augment_schema`), as the export records it: read back from Cedar's JSON form. The context
fields are those after pin injection. An error has category `cedarify`. -/
def augment (fragment : CedarSchema.Fragment) (decls : Option Declarations)
    (referencedEnums : List String) (contextFields : List ContextField)
    (providerFields : List ProviderField) : Result CedarSchema.Fragment := do
  let f ← augmentSchema fragment decls referencedEnums contextFields providerFields
  match readBackFragment f with
  | .ok f => pure f
  | .error _ => throw roundTripError

/-! ## The providers of the lowered set -/

/-- One provider field's declaration, the enum declarations its call references, and their
exported names (crate `api::merge`). -/
def resolveProvider (decls : Option Declarations) (enumNames : List (String × String))
    (f : ProviderField) : ResolvedProvider :=
  let declaration := decls.bind (·.get f.invocation.key)
  let entityTypes := match decls, declaration with
    | some d, some decl => (decl.referencedEntityTypes (f.methods.map (·.name))).filterMap
        fun n => (d.entityTypeDecls.lookup n).map (n, ·)
    | _, _ => []
  { id := f.fieldName, declaration, entityTypes
    entityTypeNames := entityTypes.filterMap fun (n, _) => (enumNames.lookup n).map (n, ·) }

/-- Each provider field's declaration, referenced enum declarations and their exported names
(crate `api::merge`). -/
def resolveProviders (decls : Option Declarations) (enumNames : List (String × String))
    (fields : List ProviderField) : Result (List ResolvedProvider) :=
  .ok (fields.map (resolveProvider decls enumNames))

end Dogwood.Frontend.Augment
