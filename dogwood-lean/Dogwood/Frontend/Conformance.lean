import Dogwood.Frontend.Signatures
import Dogwood.Frontend.Resolve
import Dogwood.Conformance.Json

/-!
# From the frontend's lowered set to the conformance export

`Lowered.toConformance` maps a lowered set, in the crate's terms, to the record the conformance
bridge exports for it (`Dogwood.Conformance.Lowered`): the typed event signatures, the
`max_window` cap, the temporal leaves as the specification's formulas, the action schema without
the hoisted attributes, the provider declarations as the specification's signatures, the rules
with each hoisted field put back as its leaf, and the provider calls. It is the Lean counterpart
of the bridge, written as the bridge writes each part (`bridge/src/schema.rs`, `decisions.rs`,
`lib.rs`), so that what the Lean frontend lowers can be compared with what the bridge exports,
and then validated and decided by the specification unchanged.

Two parts differ from the bridge on purpose: `maxWindow` is the derived schema's cap (the bridge
reads it off the DSL text), and where the bridge searches Cedar's entity types in hash order for
a provider's exported enum, this module takes the first in name order.
-/

namespace Dogwood.Frontend

open Lean (Json ToJson toJson)
open Dogwood.Spec (Expr ScopeRoot)
open Dogwood.Spec.Temporal (Formula Binder Window)
open Cedar.Validation (CedarType RecordType QualifiedType)
open Cedar.Data (Map Set)

/-- A conformance error. -/
abbrev Projection (α : Type) := Except String α

/-! ## Temporal leaves as the specification's formulas -/

namespace Surface.Temporal

/-- The entity uid of an entity literal `A::B::"id"`. -/
def entityUid (ty id : String) : Projection Cedar.Spec.EntityUID := do
  let segs := ty.splitOn "::"
  match segs.getLast? with
  | some last => pure ⟨⟨last, segs.dropLast⟩, id⟩
  | none => throw s!"empty entity type for `{id}`"

def BinderSlot.toName : BinderSlot → Projection String
  | .name n => pure n
  | .paramRef p => throw s!"unexpanded binder parameter `?{p}`"
  | .binderRef b => throw s!"unexpanded binder `${b}`"

def TypedBinder.toSpec (b : TypedBinder) : Projection Binder := do
  return ⟨← b.slot.toName, b.ty⟩

def WithinSpec.toSpec : WithinSpec → Projection Window
  | .concrete i => pure ⟨i.amount.toInt, i.unit⟩
  | .paramRef p => throw s!"unexpanded window parameter `?{p}`"

mutual

/-- The specification's form of an authored leaf (the bridge's `formula`): it has no `or`, no
array constants and no transient forms. -/
def Condition.toFormula : Condition → Projection Formula
  | ⟨_, k⟩ => ConditionKind.toFormula k

def ConditionKind.toFormula : ConditionKind → Projection Formula
  | .and l r => return .and (← l.toFormula) (← r.toFormula)
  | .or _ _ => throw "internal disjunction in an authored leaf"
  | .not c => return .not (← c.toFormula)
  | .formerly w c => return .formerly (← w.toSpec) (← c.toFormula)
  | .previous w c => return .previous (← w.toSpec) (← c.toFormula)
  | .since l w r => return .since (← l.toFormula) (← w.toSpec) (← r.toFormula)
  | .predicate ⟨_, ns, a, k, args⟩ => do
    let action ← entityUid ("::".intercalate ns) a
    return .pred action k (← NamedArg.toSpecList args)
  | .comparison op l r => return .cmp op (← l.toSpec) (← r.toSpec)
  | .exists x c => return .exist (← x.toSpec) (← c.toFormula)
  | .tp x => return .tp (← x.toName)
  | .call c => throw s!"unexpanded macro call `{c.name}`"
  | .sigilRef _ n => throw s!"unexpanded condition sigil `{n}`"
  | .refine _ _ _ => throw "unfolded field refinement"

def NamedArg.toSpecList : List NamedArg → Projection (List (Dogwood.Spec.Path × Dogwood.Spec.Temporal.Term))
  | [] => pure []
  | ⟨n, t⟩ :: rest => return (fieldPathSplit n, ← t.toSpec) :: (← NamedArg.toSpecList rest)

def Term.toSpec : Term → Projection Dogwood.Spec.Temporal.Term
  | .entity ty id => return .entity (← entityUid ty id)
  | .integer i => pure (.long i)
  | .decimal t => pure (.decimal t)
  | .string s => pure (.string s)
  | .bool b => pure (.bool b)
  | .contextField p => pure (.context p)
  | .scopeField ("principal" :: rest) => pure (.scope .principal rest)
  | .scopeField ("resource" :: rest) => pure (.scope .resource rest)
  | .scopeField p => throw s!"scope field rooted at {p}"
  | .var x => pure (.var x)
  | .wildcard => pure .wildcard
  | .array _ => throw "array constant"
  | .agg ⟨_, k⟩ => return .agg (← AggExprKind.toSpec k)
  | .arith op l r => return .arith op (← l.toSpec) (← r.toSpec)
  | .paramRef p => throw s!"unexpanded parameter `?{p}`"
  | .binderRef b => throw s!"unexpanded binder `${b}`"

def AggExprKind.toSpec : AggExprKind → Projection Dogwood.Spec.Temporal.Aggregate
  | .count vs b => return .count (← vs.mapM TypedBinder.toSpec) (← b.toFormula)
  | .sum v vs b => return .sum (← v.toName) (← vs.mapM TypedBinder.toSpec) (← b.toFormula)
  | .call c => throw s!"unexpanded aggregate macro `{c.name}`"

end

end Surface.Temporal

/-! ## Event signatures, typed against the compiled schema -/

/-- A name's text, `A::B::C`. -/
def nameText (n : Cedar.Spec.Name) : String := "::".intercalate (n.path ++ [n.id])

/-- The entity type of the compiled schema whose name's text is `text`. -/
def findEntityType (S : Cedar.Validation.Schema) (text : String) : Option Cedar.Spec.EntityType :=
  (S.ets.toList.find? fun (n, _) => nameText n == text).map (·.1)

/-- The type at `path` in a record type, and whether every attribute along the path is required
(the bridge's `path_type`). -/
def pathType (attrs : RecordType) : List String → Option (CedarType × Bool)
  | [] => none
  | [last] => (attrs.find? last).map fun q => (q.getType, q.isRequired)
  | seg :: rest =>
    match attrs.find? seg with
    | some (.required (.record inner)) => pathType inner rest
    | some (.optional (.record inner)) => (pathType inner rest).map fun (t, _) => (t, false)
    | _ => none

/-- A field type the event schema declares in text, as a Cedar type (the bridge's `text_type`):
a primitive, an extension type, a set, or an entity type the schema declares. -/
def textType (S : Cedar.Validation.Schema) (text : String) : Projection CedarType :=
  go text.length text
where
  go : Nat → String → Projection CedarType
    | 0, t => throw s!"field type `{t}`"
    | fuel + 1, text =>
      let t := text.trimAscii.toString
      match t with
      | "String" => pure .string
      | "Long" => pure .int
      | "Bool" | "Boolean" => pure (.bool .anyBool)
      | "decimal" => pure (.ext .decimal)
      | "ipaddr" => pure (.ext .ipAddr)
      | "datetime" => pure (.ext .datetime)
      | "duration" => pure (.ext .duration)
      | _ =>
        let afterSet := ((t.dropPrefix? "Set").map (·.toString.trimAscii.toString)).bind
          fun r => (r.dropPrefix? "<").map (·.toString)
        match afterSet with
        | some inner =>
          match inner.dropSuffix? ">" with
          | some body => return .set (← go fuel body.toString)
          | none => throw s!"field type `{t}`"
        | none =>
          match findEntityType S t with
          | some e => pure (.entity e)
          | none => throw s!"field type `{t}`"

/-- An entity type an event field names, resolved in the namespace of the event's action, or
as written (the bridge's `resolve_entity_type`). -/
def resolveEntityType (S : Cedar.Validation.Schema) (ns : List String) (name : String) :
    Projection Cedar.Spec.EntityType :=
  let home := ns.dropLast
  let qualified := if home.isEmpty then name else "::".intercalate home ++ "::" ++ name
  match findEntityType S qualified, findEntityType S name with
  | some e, _ => pure e
  | none, some e => pure e
  | none, none => throw s!"entity type `{name}` of an event field"

/-- A crate signature as the specification's (the bridge's `signature`): a field spliced from
`input` or `output` has the type the action's context declares at its path and is required when
every attribute along the path is; any other field is optional. -/
def EventSignature.toSpec (S : Cedar.Validation.Schema) (s : EventSignature) :
    Projection Dogwood.Spec.EventSignature := do
  let action := actionUid s.namespace s.action
  let pins ← s.pins.mapM Pin.toSpec
  let context := (S.acts.find? action).map (·.context)
  let fields ← s.fields.mapM fun (path, fty) => do
    let spliced := match path with
      | "input" :: _ | "output" :: _ => true
      | _ => false
    match spliced, context.bind (pathType · path) with
    | true, some (t, req) => pure { path, ty := .cedar t, required := req }
    | _, _ =>
      match fty with
      | .entityTypes names =>
        pure { path, ty := .entities (← names.mapM (resolveEntityType S s.namespace)),
               required := false }
      | .cedar text => pure { path, ty := .cedar (← textType S text), required := false }
  return { action, kind := s.kind, decision := s.decision, pins, fields }

/-- The derived schema's signatures, typed against the compiled schema. -/
def typedSignatures (d : DerivedEventSchema) (S : Cedar.Validation.Schema) :
    Projection Dogwood.Spec.EventSchema :=
  (d.events.map DerivedEvent.signature).mapM (EventSignature.toSpec S)

/-! ## The action schema without the hoisted attributes -/

/-- The compiled schema in the validator's descendant form (`Conformance.ActionSchemaJson`),
without the context attributes in `drop`: the inverse of `ActionSchemaJson.toSchema`. -/
def actionSchemaJson (S : Cedar.Validation.Schema) (drop : List String) :
    Conformance.ActionSchemaJson :=
  let ets := S.ets.toList
  let acts := S.acts.toList
  { ets := ets.map fun (n, e) =>
      let descendants := (ets.filter fun (_, e') => e'.ancestors.contains n).map (·.1)
      match e with
      | .standard ⟨_, attrs, tags⟩ => { name := n, descendants, attrs, tags }
      | .enum eids => { name := n, descendants, attrs := Map.empty, «enum» := some eids.toList }
    acts := acts.map fun (a, e) =>
      { name := a, principals := e.appliesToPrincipal.toList,
        resources := e.appliesToResource.toList,
        descendants := (acts.filter fun (_, e') => e'.ancestors.contains a).map (·.1),
        context := Map.make (e.context.toList.filter fun (k, _) => !drop.contains k) } }

/-- The context attributes lowering hoisted: each temporal field, and `providers`. -/
def Lowered.hoistedNames (l : Lowered) : List String :=
  l.temporal.map (·.id) ++ (if l.providers.isEmpty then [] else ["providers"])

/-! ## Provider declarations as the specification's signatures -/

/-- A provider parameter type as a Cedar type (the bridge's `param_type`): a provider enum is the
entity type the schema exports for it (`<namespace>::<declared with :: as _>`), any other entity
type keeps its name; an unknown kind, a set without items and an entity without a type are
`String`. -/
def paramTypeToCedar (S : Cedar.Validation.Schema) : ProviderDecls.ParamType → Projection CedarType
  | ⟨kind, fields, items, required, et⟩ =>
    match kind with
    | "string" => pure .string
    | "integer" | "long" => pure .int
    | "bool" | "boolean" => pure (.bool .anyBool)
    | "decimal" => pure (.ext .decimal)
    | "set" => match items with
      | some i => return .set (← paramTypeToCedar S i)
      | none => pure (.set .string)
    | "record" => do
      let attrs ← fieldsToCedar required fields
      pure (.record (Map.make attrs))
    | "entity" => match et with
      | some declared =>
        let basename := ProviderDecls.exportedEnumBasename declared
        let exported := (S.ets.toList.find? fun (n, _) => n.id == basename).map (·.1)
        match exported, findEntityType S declared with
        | some e, _ => pure (.entity e)
        | none, some e => pure (.entity e)
        | none, none => throw s!"the entity type `{declared}`"
      | none => pure .string
    | _ => pure .string
where
  fieldsToCedar (required : List String) :
      List (String × ProviderDecls.ParamType) → Projection (List (String × QualifiedType))
    | [] => pure []
    | (k, p) :: rest => do
      let t ← paramTypeToCedar S p
      let q : QualifiedType := if required.contains k then .required t else .optional t
      return (k, q) :: (← fieldsToCedar required rest)

/-- One method of a declaration as the specification's. -/
def methodDeclToSpec (S : Cedar.Validation.Schema) (m : String) (md : ProviderDecls.MethodDecl) :
    Projection Dogwood.Spec.Provider.MethodSig := do
  return { name := m, args := ← md.argumentTypes.mapM (paramTypeToCedar S),
           input := ← md.inputType.mapM (paramTypeToCedar S),
           output := ← paramTypeToCedar S md.outputType }

/-- One declaration as the specification's signature (the bridge's `provider_decl`). A method
whose type names an entity type the schema does not declare is left out: no invocation calls it,
or lowering would have injected the enum. -/
def providerDeclToSpec (S : Cedar.Validation.Schema) (name : String) (d : ProviderDecls.ProviderDecl) :
    Projection Dogwood.Spec.Provider.Signature := do
  let segs := name.splitOn "::"
  let function : Cedar.Spec.Name := ⟨segs.getLast?.getD "", segs.dropLast⟩
  let methods := d.methods.filterMap fun (m, md) => (methodDeclToSpec S m md).toOption
  return { function, args := ← d.argumentTypes.mapM (paramTypeToCedar S),
           output := ← paramTypeToCedar S d.outputType, methods }

/-- The declarations as the specification's, and the names of those left out because their
argument or output type names an entity type the schema does not declare (the bridge's
`provider_decls`). -/
def providerDeclsToSpec (decls : Option ProviderDecls.Declarations) (S : Cedar.Validation.Schema) :
    Dogwood.Spec.Provider.Declarations × List String :=
  match decls with
  | none => ([], [])
  | some d => d.available.foldl (init := ([], [])) fun (out, skipped) (name, decl) =>
    match providerDeclToSpec S name decl with
    | .ok s => (out ++ [s], skipped)
    | .error _ => (out, skipped ++ [name])

/-! ## Provider calls and the rules with their leaves -/

def Provider.Arg.toSpec : Provider.Arg → Projection Dogwood.Spec.Provider.Arg
  | .field ("context" :: rest) => pure (.context rest)
  | .field ("principal" :: rest) => pure (.scope .principal rest)
  | .field ("resource" :: rest) => pure (.scope .resource rest)
  | .field p => throw s!"provider argument path {p}"
  | .string s => pure (.string s)
  | .integer i => pure (.long i)
  | .decimal t => pure (.decimal t)
  | .bool b => pure (.bool b)
  | .set xs => return .set (← argsToSpec xs)
where
  argsToSpec : List Provider.Arg → Projection (List Dogwood.Spec.Provider.Arg)
    | [] => pure []
    | x :: rest => return (← Provider.Arg.toSpec x) :: (← argsToSpec rest)

/-- A provider field's call, as the specification's (the bridge's `call`). -/
def LoweredProviderField.toCall (f : LoweredProviderField) : Projection Dogwood.Spec.Provider.Call := do
  let segs := f.invocation.function
  let function : Cedar.Spec.Name ← match segs.getLast? with
    | some id => pure ⟨id, segs.dropLast⟩
    | none => throw "a provider invocation without a name"
  return { function, args := ← f.invocation.args.mapM Provider.Arg.toSpec,
           methods := ← f.methods.mapM fun m => do
             return { name := m.name, args := ← m.args.mapM Provider.Arg.toSpec } }

/-- `context`. -/
def isContext : Expr → Bool
  | .var .context => true
  | _ => false

/-- `context.providers`. -/
def isContextProviders : Expr → Bool
  | .getAttr (.var .context) "providers" => true
  | _ => false

mutual

/-- The expression with each hoisted field put back as its leaf: `context.<id>` of a temporal
field as `temporal φ`, and `context.providers.<id>` of a provider field as `provider c` (the
bridge's `Gen`). -/
def putBack (T : List (String × Formula)) (P : List (String × Dogwood.Spec.Provider.Call)) :
    Expr → Expr
  | .getAttr e a =>
    match (if isContext e then T.lookup a else none),
        (if isContextProviders e then P.lookup a else none) with
    | some φ, _ => .temporal φ
    | none, some c => .provider c
    | none, none => .getAttr (putBack T P e) a
  | .lit p => .lit p
  | .var v => .var v
  | .ite c t e => .ite (putBack T P c) (putBack T P t) (putBack T P e)
  | .and a b => .and (putBack T P a) (putBack T P b)
  | .or a b => .or (putBack T P a) (putBack T P b)
  | .unaryApp op e => .unaryApp op (putBack T P e)
  | .binaryApp op a b => .binaryApp op (putBack T P a) (putBack T P b)
  | .hasAttr e a => .hasAttr (putBack T P e) a
  | .extHasAttr e a as => .extHasAttr (putBack T P e) a as
  | .set ls => .set (putBackList T P ls)
  | .record m => .record (putBackRecord T P m)
  | .call f args => .call f (putBackList T P args)
  | .temporal φ => .temporal φ
  | .provider c => .provider c

def putBackList (T : List (String × Formula)) (P : List (String × Dogwood.Spec.Provider.Call)) :
    List Expr → List Expr
  | [] => []
  | e :: rest => putBack T P e :: putBackList T P rest

def putBackRecord (T : List (String × Formula)) (P : List (String × Dogwood.Spec.Provider.Call)) :
    List (String × Expr) → List (String × Expr)
  | [] => []
  | (k, e) :: rest => (k, putBack T P e) :: putBackRecord T P rest

end

/-- A lowered rule with its leaves put back. -/
def putBackPolicy (T : List (String × Formula)) (P : List (String × Dogwood.Spec.Provider.Call))
    (p : Dogwood.Spec.Policy) : Dogwood.Spec.Policy :=
  { p with condition := p.condition.map fun c => { c with body := putBack T P c.body } }

/-! ## The conformance record -/

/-- The window's length in seconds, saturating at the range of a `Long` (crate
`Interval::seconds`). -/
def Surface.Temporal.Interval.seconds (i : Surface.Temporal.Interval) : Int :=
  let s := i.amount.toInt * i.unit.toSeconds
  max Int64.minValue.toInt (min Int64.maxValue.toInt s)

/-- The temporal leaves, by field id, as the specification's formulas. -/
def Lowered.leafFormulas (l : Lowered) : Projection (List (String × Formula)) :=
  l.temporal.mapM fun f => return (f.id, ← f.condition.condition.toFormula)

/-- The provider calls, by field id. -/
def Lowered.providerCalls (l : Lowered) : Projection (List (String × Dogwood.Spec.Provider.Call)) :=
  l.providers.mapM fun f => return (f.id, ← f.toCall)

/-- The lowered set as the conformance bridge exports it (`Dogwood.Conformance.Lowered`),
without the crate's validation findings and decisions, which are not the frontend's. -/
def Lowered.toConformance (l : Lowered) : Projection Conformance.Lowered := do
  let T ← l.leafFormulas
  let P ← l.providerCalls
  let (decls, skipped) := providerDeclsToSpec l.declarations l.schema
  return {
    schema := ← typedSignatures l.eventSchema l.schema
    maxWindow := l.eventSchema.maxWindow.seconds
    maxHorizon := l.eventSchema.maxHorizon.map (·.seconds)
    leaves := T.map (·.2)
    actionSchema := { actionSchemaJson l.schema l.hoistedNames with
      externalTypes := CedarSchema.Resolve.externalEntityTypes l.augmentedSchema
      externalActions := CedarSchema.Resolve.externalActions l.augmentedSchema }
    providerDecls := decls
    providerDeclsSkipped := skipped
    policies := l.policies.map (putBackPolicy T P)
    providers := P }

end Dogwood.Frontend
