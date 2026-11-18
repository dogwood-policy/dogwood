import Dogwood.Frontend.Types
import Dogwood.Frontend.Escape

/-!
# Event-schema derivation (WP2)

The crate's `event_schema/derive.rs`: the event-schema DSL bound to the action schema. For each
namespace of the action schema (in the fragment's order), each action of it (in name order),
and each declaration of the DSL (in order), derivation produces one event, whose fields come
from evaluating the declaration's field specs against the action:

* `...inputs(A)` and `...outputs(A)` splice the record of the action's `context.input` and
  `context.output` attribute as the field groups `input` and `output`, resolving common-type
  references (a bare one in the action's namespace, a qualified one in the namespace it names) and
  descending into nested records (`contextSubrecord`, `typeToNode`);
* `principalType(A)` and `resourceType(A)` give the action's `appliesTo` entity types, as written;
* a concrete type is a leaf with that type's name, and a record type nests.

A leaf's type text is Cedar's rendering of the schema type (`renderType`, Cedar's `Display` of
`json_schema::Type`), for example `Set<String>` or `__cedar::Long`. A field tree is a map in key
order (a `BTreeMap` in the crate): `insertKey` keeps the keys sorted and distinct, and replaces
the value of a key inserted twice, as `BTreeMap::insert` does. Two bounds guard the expansion of
the action schema's records, which derivation reads before Cedar has checked the schema: a
nesting depth of 64 and a budget of 10,000 nodes per spliced group.
-/

namespace Dogwood.Frontend.Derive

open CedarSchema
open EventSchemaDsl
open Surface.Temporal (Interval)

/-! ## Helpers -/

/-- Insert into a field map kept in key order (`BTreeMap::insert`): a new key goes to its place,
an existing key gets the new value. -/
def insertKey {α : Type} (k : String) (v : α) : List (String × α) → List (String × α)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k < k' then (k, v) :: (k', v') :: rest
    else if k = k' then (k, v) :: rest
    else (k', v') :: insertKey k v rest

/-- Whether the map has the key. -/
def hasKey {α : Type} (k : String) (m : List (String × α)) : Bool :=
  m.any (·.1 == k)

/-- The declarations of the fragment's namespace `ns` (`Fragment::0.get`). -/
def namespace? (f : Fragment) (ns : Option String) : Option NamespaceDef :=
  (f.find? (·.1 == ns)).map (·.2)

/-- The identifiers Cedar reserves (`RESERVED_IDS`). -/
def reservedIds : List String :=
  ["true", "false", "if", "then", "else", "in", "is", "like", "has", "__cedar"]

/-- An identifier: `[_a-zA-Z][_a-zA-Z0-9]*`. -/
def isIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all fun c => c.isAlphanum || c == '_'

/-- An identifier that needs no quotes as a record attribute (Cedar `is_normalized_ident`). -/
def isNormalizedIdent (s : String) : Bool :=
  isIdent s && !reservedIds.contains s

/-- A string as Rust's `str::escape_debug` writes it (`Escape.strEscapeDebug`). -/
def escapeDebug (s : String) : String := Escape.strEscapeDebug s

/-! ## Cedar's rendering of a schema type -/

/-- `n` spaces. -/
def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- Annotations, one per line, at the indentation `n` (Cedar `Annotations::fmt_indented`). -/
def renderAnnotations (n : Nat) (anns : Annotations) : String :=
  String.join (anns.map fun (k, v) => match v with
    | some v => s!"{spaces n}@{k}(\"{escapeDebug v}\")\n"
    | none => s!"{spaces n}@{k}\n")

mutual

/-- A schema type in the Cedar schema syntax, with the base indentation `base` (Cedar's
`IndentedDisplay` of `json_schema::Type`). -/
def renderType (base : Nat) : SchemaType → String
  | .commonRef n => n
  | .string => "__cedar::String"
  | .long => "__cedar::Long"
  | .boolean => "__cedar::Bool"
  | .set e => "Set<" ++ renderType base e ++ ">"
  | .record attrs _ =>
    "{" ++ (if attrs.isEmpty then "" else "\n") ++ renderAttrs (base + 2) attrs ++ spaces base ++
      "}"
  | .entity n => n
  | .entityOrCommon n => n
  | .extension n => "__cedar::" ++ n

/-- A record's attributes, one per line, at the indentation `member`, a comma after each but the
last. -/
def renderAttrs (member : Nat) : List (String × AttrType) → String
  | [] => ""
  | (n, ⟨ty, required, anns⟩) :: rest =>
    renderAnnotations member anns ++ spaces member ++
      (if isNormalizedIdent n then n else "\"" ++ escapeDebug n ++ "\"") ++
      (if required then "" else "?") ++ ": " ++ renderType member ty ++
      (if rest.isEmpty then "" else ",") ++ "\n" ++ renderAttrs member rest

end

/-! ## Records of the action schema -/

/-- The nesting bound (`MAX_RECORD_DEPTH`). -/
def maxRecordDepth : Nat := 64

/-- The node budget of a spliced group (`MAX_RECORD_NODES`). -/
def maxRecordNodes : Nat := 10000

/-- The namespace key a qualified reference's prefix names (crate `qualify`): `none` for the
empty prefix; an error unless every segment is an unreserved identifier. -/
def qualify (ns : String) : Except String (Option String) :=
  if ns.isEmpty then pure none
  else if (ns.splitOn "::").all fun s => isIdent s && !reservedIds.contains s then pure (some ns)
  else throw s!"bad namespace `{ns}` in type reference: invalid name `{ns}`"

/-- A reference's text cut at its last `::` (`str::rsplit_once`). -/
def splitLast (full : String) : Option (String × String) :=
  let segs := full.splitOn "::"
  if segs.length ≤ 1 then none else some ("::".intercalate segs.dropLast, segs.getLast?.getD "")

/-- The name a type refers to, if it is a reference (`commonRef` or `entityOrCommon`). -/
def refName? : SchemaType → Option String
  | .commonRef n | .entityOrCommon n => some n
  | _ => none

/-- What a namespace declares under a basename (one step of crate `resolve_to_record`'s search):
`some (some ty)` a common type of type `ty`, `some none` an entity type, `none` nothing, or no such
namespace in the fragment. A common type comes first. -/
def declaredAs (f : Fragment) (ns : Option String) (base : String) : Option (Option SchemaType) :=
  match namespace? f ns with
  | none => none
  | some nsDef =>
    match nsDef.commonTypes.find? (·.1 == base) with
    | some (_, ct) => some (some ct.ty)
    | none => if nsDef.entityTypes.any (·.1 == base) then some none else none

/-- The first of the candidates that declares something, and what. -/
def firstDeclared (f : Fragment) :
    List (Option String × String) → Option (Option String × Option SchemaType)
  | [] => none
  | (ns, base) :: rest =>
    match declaredAs f ns base with
    | some d => some (ns, d)
    | none => firstDeclared f rest

/-- The namespaces and basenames a reference may name, in Cedar's order
(`RawName::conditionally_qualify_with`): a qualified reference its own namespace; a bare one the
home namespace, and then the root namespace. -/
def refCandidates (full : String) (home : Option String) :
    Except String (List (Option String × String)) :=
  match splitLast full with
  | some (ns, base) => do pure [((← qualify ns), base)]
  | none =>
    match home with
    | some _ => pure [(home, full), (none, full)]
    | none => pure [(none, full)]

/-- Resolve a type to a record and the namespace its members resolve in (crate
`resolve_to_record`): an inline record is declared in `home`; a reference resolves to the common
type it names, recursively, in the namespace that declares it: a bare reference in `home`, and
then in the root namespace, as Cedar resolves it (`refCandidates`); a qualified one in its
namespace. In each namespace a common type comes before an entity type. `none` when the type is
not a record: a primitive, a set, a reference into `__cedar`, to an entity type, to an undeclared
namespace, or a bare reference to nothing. A qualified reference into a declared namespace to
neither a common nor an entity type is an error. `fuel` is what is left of the depth bound: the
crate's depth `d` is `maxRecordDepth + 1 - d` here, and each alias hop takes one. -/
def resolveToRecordF (f : Fragment) :
    Nat → SchemaType → Option String →
      Except String (Option (List (String × AttrType) × Option String))
  | 0, _, _ =>
    throw s!"event-schema field type aliases through more than {maxRecordDepth} common types; \
      the action schema likely has a cyclic type definition"
  | fuel + 1, ty, home =>
    match ty with
    | .record attrs _ => pure (some (attrs, home))
    | _ =>
      match refName? ty with
      | none => pure none
      | some full =>
        if (full.splitOn "::").head? == some "__cedar" then pure none
        else do
          let cands ← refCandidates full home
          match firstDeclared f cands with
          | some (targetNs, some ty') => resolveToRecordF f fuel ty' targetNs
          | some (_, none) => pure none
          | none =>
            if (full.splitOn "::").length > 1 && cands.any (fun c => (namespace? f c.1).isSome) then
              throw s!"type reference `{full}` does not resolve to a declared common type"
            else pure none

/-- `resolveToRecordF` at the crate's depth `depth`. -/
def resolveToRecord (f : Fragment) (ty : SchemaType) (home : Option String) (depth : Nat) :
    Except String (Option (List (String × AttrType) × Option String)) :=
  resolveToRecordF f (maxRecordDepth + 1 - depth) ty home

/-- A record's attributes as field nodes, each computed by `node` (which threads the node count),
inserted in order into `acc`. -/
def attrsToNodes (node : SchemaType → Nat → Except String (DerivedFieldNode × Nat)) :
    List (String × AttrType) → Nat → List (String × DerivedFieldNode) →
      Except String (List (String × DerivedFieldNode) × Nat)
  | [], nodes, acc => pure (acc, nodes)
  | (n, a) :: rest, nodes, acc => do
    let (nd, nodes) ← node a.ty nodes
    attrsToNodes node rest nodes (insertKey n nd acc)

/-- A member type as a field node (crate `type_to_node`): a record (inline, or through common
types) is a group of its members' nodes, any other type a leaf with its rendered text. `nodes`
counts the nodes produced so far in the group being spliced; `fuel` is what is left of the depth
bound, as in `resolveToRecordF`, and a member is one level deeper. -/
def typeToNodeF (f : Fragment) :
    Nat → SchemaType → Option String → Nat → Except String (DerivedFieldNode × Nat)
  | 0, _, _, _ =>
    throw s!"event-schema field record nests deeper than {maxRecordDepth} levels; the action \
      schema likely has a cyclic type definition"
  | fuel + 1, ty, home, nodes =>
    if nodes + 1 > maxRecordNodes then
      throw s!"event-schema field record expands to more than {maxRecordNodes} fields; the \
        action schema likely has a type whose nesting fans out exponentially"
    else do
      match ← resolveToRecordF f (fuel + 1) ty home with
      | some (attrs, recNs) =>
        let (members, nodes) ←
          attrsToNodes (fun t n => typeToNodeF f fuel t recNs n) attrs (nodes + 1) []
        pure (.group members, nodes)
      | none => pure (.leaf (.cedar (renderType 0 ty)), nodes + 1)

/-- `typeToNodeF` at the crate's depth `depth`. -/
def typeToNode (f : Fragment) (ty : SchemaType) (home : Option String) (depth nodes : Nat) :
    Except String (DerivedFieldNode × Nat) :=
  typeToNodeF f (maxRecordDepth + 1 - depth) ty home nodes

/-- The field tree of the action's `context.<attr>` record (crate `context_subrecord`): empty
when the action has no `appliesTo`, its context is not a record, it has no such attribute, or the
attribute is not a record. The context's members resolve in the namespace the context record
was declared in. -/
def contextSubrecord (f : Fragment) (action : ActionDef) (home : Option String) (attr : String) :
    Except String (List (String × DerivedFieldNode)) := do
  match action.appliesTo with
  | none => pure []
  | some at_ =>
    match ← resolveToRecord f at_.context home 0 with
    | none => pure []
    | some (ctx, ctxNs) =>
      match ctx.find? (·.1 == attr) with
      | none => pure []
      | some (_, sub) =>
        match (← typeToNode f sub.ty ctxNs 0 0).1 with
        | .group members => pure members
        | .leaf _ => pure []

/-! ## Deriving one event -/

/-- What deriving a declaration's fields reads: the fragment, the action, its id and namespace,
and the declaration's kind. -/
structure Ctx where
  fragment : Fragment
  actionId : String
  kind : String
  action : ActionDef
  home : Option String

/-- The fields derived so far at one level: the map, the names a spread produced, and the pins
collected so far (over the whole event, in declaration order). -/
structure Acc where
  fields : List (String × DerivedFieldNode)
  spreadNames : List String
  pins : List Pin

/-- A selector's name in the DSL (crate `Selector::as_str`). -/
def selectorName : Selector → String
  | .inputs => "inputs"
  | .outputs => "outputs"
  | .principalType => "principalType"
  | .resourceType => "resourceType"

/-- The action's display in an error, `<id>::<kind>`, the id escaped as Cedar escapes an
entity id. -/
def Ctx.display (c : Ctx) : String := s!"{escapeDebug c.actionId}::{c.kind}"

/-- The `appliesTo` principal types, as written; none without `appliesTo`. -/
def Ctx.principalTypes (c : Ctx) : List String :=
  (c.action.appliesTo.map (·.principalTypes)).getD []

/-- The `appliesTo` resource types, as written; none without `appliesTo`. -/
def Ctx.resourceTypes (c : Ctx) : List String :=
  (c.action.appliesTo.map (·.resourceTypes)).getD []

mutual

/-- Derive a list of field specs into the accumulator, in order (crate `derive_fields`). -/
def deriveSpecs (c : Ctx) (pfx : List String) : List FieldSpec → Acc → Except String Acc
  | [], acc => pure acc
  | s :: rest, acc => do
    let acc ← deriveSpec c pfx s acc
    deriveSpecs c pfx rest acc

/-- Derive one field spec into the accumulator. A spread inserts its group, a named field its
node; a name defined twice at one level is an error. -/
def deriveSpec (c : Ctx) (pfx : List String) : FieldSpec → Acc → Except String Acc
  | .spread sel _, acc => do
    let (group, members) ← match sel with
      | .inputs => do pure ("input", ← contextSubrecord c.fragment c.action c.home "input")
      | .outputs => do pure ("output", ← contextSubrecord c.fragment c.action c.home "output")
      | .principalType | .resourceType =>
        throw s!"selector `{selectorName sel}` cannot be spread (it yields entity types, not a \
          field record); use it as a field type instead"
    if hasKey group acc.fields then
      throw s!"the `{group}` field group produced by `...{selectorName sel}(A)` (on `{c.display}`) \
        collides with another field named `{group}`; a spread group and a named field may not \
        share a name"
    pure { acc with fields := insertKey group (.group members) acc.fields,
                    spreadNames := acc.spreadNames ++ [group] }
  | .named name ty pin _, acc => do
    let path := pfx ++ [name]
    let (node, pins) ← deriveType c path ty acc.pins
    let pins := match pin with
      | some pv => pins ++ [{ fieldPath := path, contextPath := pv.contextPath, root := pv.root }]
      | none => pins
    if hasKey name acc.fields then
      if acc.spreadNames.contains name then
        throw s!"event-schema field `{name}` (injected on `{c.display}`) collides with the \
          `{name}` field group produced by a spread; a named field may not shadow a spread group"
      else
        throw s!"event-schema field `{name}` is defined more than once on `{c.display}`; field \
          names must be unique at each level"
    pure { acc with fields := insertKey name node acc.fields, pins }

/-- The node of a named field's type at `path`, and the pins collected, a nested record's
included. -/
def deriveType (c : Ctx) (path : List String) : TypeExpr → List Pin →
    Except String (DerivedFieldNode × List Pin)
  | .selector .principalType, pins => pure (.leaf (.entityTypes c.principalTypes), pins)
  | .selector .resourceType, pins => pure (.leaf (.entityTypes c.resourceTypes), pins)
  | .selector s, _ =>
    throw s!"selector `{selectorName s}` cannot be used as a field type (it yields a field \
      record, not a type); spread it with `...` instead"
  | .concrete p, pins => pure (.leaf (.cedar ("::".intercalate p)), pins)
  | .record inner, pins => do
    let acc ← deriveSpecs c path inner ⟨[], [], pins⟩
    pure (.group acc.fields, acc.pins)

end

/-- The event of one declaration on one action (crate `derive_one`). -/
def deriveOne (f : Fragment) (nsPath : List String) (home : Option String) (actionId : String)
    (action : ActionDef) (decl : EventDecl) : Except String DerivedEvent := do
  let c : Ctx := { fragment := f, actionId, kind := decl.kind, action, home }
  let acc ← deriveSpecs c [] decl.fields ⟨[], [], []⟩
  pure { «namespace» := nsPath ++ ["Action"], action := actionId, kind := decl.kind,
         decision := decl.decision, fields := acc.fields, pins := acc.pins }

/-- The default cap on `within` windows, 24 hours (`DEFAULT_MAX_WINDOW`). -/
def defaultMaxWindow : Interval := ⟨24, .hours⟩

/-! ## The default event schema -/

/-- The fields of a default declaration: the action's inputs (and, for a response, its outputs),
the caller's principal, pinned to the request's principal, the caller's resource, and the
request and session ids. -/
def defaultFields (outputs : Bool) : List FieldSpec :=
  [.spread .inputs default] ++ (if outputs then [.spread .outputs default] else []) ++
  [.named "callerPrincipal" (.selector .principalType)
      (some { contextPath := ["principal"], root := .scope, span := default }) default,
   .named "callerResource" (.selector .resourceType) none default,
   .named "requestId" (.concrete ["String"]) none default,
   .named "sessionId" (.concrete ["String"]) none default]

/-- The default event schema (`configuration/event-schemas/pinned.dwschema`, which the crate's
service schema uses when a bundle declares none), as the parser reads it, without source spans:
a `request` decision kind and `response` and `error` history kinds, each pinning
`callerPrincipal` to the request's principal, and no `max_window` directive. -/
def defaultEventSchema : EventSchemaDsl.EventSchema where
  maxWindow := none
  maxHorizon := none
  decls := [
    { span := default, decision := true, binder := "A", kind := "request",
      fields := defaultFields false },
    { span := default, decision := false, binder := "A", kind := "response",
      fields := defaultFields true },
    { span := default, decision := false, binder := "A", kind := "error",
      fields := defaultFields false }]

/-- The path of a namespace key: its segments, none for the root namespace. -/
def nsPath : Option String → List String
  | some n => n.splitOn "::"
  | none => []

/-- The events of the declarations on each action of the fragment: namespaces in the fragment's
order, actions in name order, declarations in order. -/
def deriveEvents (f : Fragment) (decls : List EventDecl) : Except String (List DerivedEvent) :=
  f.flatMapM fun (ns, nsDef) =>
    nsDef.actions.flatMapM fun (id, action) =>
      decls.mapM (deriveOne f (nsPath ns) ns id action)

/-- An interval as written, `<amount><unit>` (crate `Interval::render`). -/
def renderInterval (i : Interval) : String :=
  -- `toString` on the `Int64` itself would print it as a Cedar `decimal` (`0.0048`).
  toString i.amount.toInt ++ match i.unit with
    | .seconds => "s" | .minutes => "m" | .hours => "h" | .days => "d"

/-- An interval's length in seconds, saturating at the range of a `Long` (crate
`Interval::seconds`). -/
def intervalSeconds (i : Interval) : Int :=
  let s := i.amount.toInt * i.unit.toSeconds
  max Int64.minValue.toInt (min Int64.maxValue.toInt s)

/-- The resolved `max_window` and `max_horizon` caps (crate `EventSchema::limits`): the horizon
is the directive, if any; the window is the directive, else the declared horizon, else 24h. A
window longer than a declared horizon is an error. -/
def limits (dsl : EventSchemaDsl.EventSchema) : Except String (Interval × Option Interval) :=
  let w := match dsl.maxWindow, dsl.maxHorizon with
    | some w, _ => w
    | none, some h => h
    | none, none => defaultMaxWindow
  match dsl.maxHorizon with
  | some h =>
    if intervalSeconds w > intervalSeconds h then
      .error s!"`max_window = {renderInterval w}` is longer than `max_horizon = {renderInterval h}`; a temporal condition can never look back further than `max_horizon`, so no window could use its full cap. Set `max_horizon` to at least `{renderInterval w}`, or lower `max_window`"
    else .ok (w, some h)
  | none => .ok (w, none)

/-- Derive one event per namespace (in the fragment's order), action (in name order) and
declaration (in DSL order) (crate `derive`). An error has category `eventSchema`. -/
def derive (dsl : EventSchemaDsl.EventSchema) (fragment : CedarSchema.Fragment) :
    Result DerivedEventSchema :=
  match deriveEvents fragment dsl.decls with
  | .ok events =>
    match limits dsl with
    | .ok (w, h) => pure { events, maxWindow := w, maxHorizon := h }
    | .error m => throw { stage := .derive, category := .eventSchema, message := m }
  | .error m => throw { stage := .derive, category := .eventSchema, message := m }

end Dogwood.Frontend.Derive
