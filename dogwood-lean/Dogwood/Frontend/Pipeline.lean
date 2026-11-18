import Dogwood.Frontend.Driver
import Dogwood.Frontend.Json
import Dogwood.Frontend.Ids
import Dogwood.Frontend.Validate
import Dogwood.Frontend.Cedarify.Reads
import Dogwood.Frontend.CedarPrint
import Dogwood.Frontend.SchemaJson

/-!
# The frontend in one call

A total function from the parsers' outputs to everything the crate's frontend produces, for one
policy set (`lowerAll`: crate `ParsedPolicySet::parse`, `with_ids`, `lower` or
`lower_with_distincter`, then `Validator::validate`) and for several lowered together
(`lowerManyAll`: each entry parsed and given its ids, then `policy_set::lower_many`), and the
first phase alone (`parseAll`). Each reads and writes JSON, in the encoding of the crate's
frontend export (`Dogwood.Frontend.Json`); the shapes are those of the frontend's FFI format.

The checks run in the crate's order: the service
schema's (the provider declarations' and the event schema's parsers, the declarations' check),
then each entry's parsers, macro library merge, expansion and id assignment, then the
distincters, then lowering (`Driver.lowerEntries`).

The lowered set (`Full`) is the crate's `api::Lowered` with its `SetIdentity`: the rules as
Cedar policies (Cedar's policy JSON and text, `CedarPrint`), each rule's source span and entry,
the revisions (`RuleIdentity`), the version hash over Cedar's JSON of the augmented schema
(`SchemaJson`), and the reads of the request context lowering does not preserve. The validator's
findings (`Validate.validateLocated`, the findings of `Validate.validate`) come with the rule each
is about and its span in that rule's source, where the lowered set locates them.
-/

namespace Dogwood.Frontend.Driver

open Lean (Json FromJson ToJson fromJson? toJson)
open Surface.Temporal (Condition)

/-! ## Inputs -/

/-- What the service schema and the action schema's parsers produced, shared by every entry:
the macro library's definitions (none for a blank library), the event-schema DSL, the provider
declarations (none when there are none), and the action schema. -/
structure SharedInput where
  library : Option (Result (List Surface.MacroDef)) := none
  eventSchema : Result EventSchemaDsl.EventSchema
  providers : Option (Result ProviderDecls.Declarations) := none
  actionSchema : Result CedarSchema.Fragment

/-- One policy set to lower: what the policy parser produced, its distincter, and its id
source. -/
structure EntryInput where
  policy : Result Surface.PolicySet
  distincter : Option String := none
  ids : IdSource := .positional

/-! ## The lowered set, whole -/

/-- Everything the crate's lowered set holds (crate `api::Lowered` and
`identity::SetIdentity`), besides what is printed when it is encoded. -/
structure Full where
  lowered : Lowered
  /-- Each rule as a Cedar policy with the crate's names, and its source annotations. -/
  rules : List (Cedar.Spec.Policy × List Surface.Annotation)
  /-- Each rule's span in its entry's policy source (crate `rule_locs`). -/
  ruleSpans : List Span
  /-- Each rule's entry (crate `rule_sources`). -/
  ruleSources : List Nat
  ruleRevisions : List String
  /-- Whether every entry has stable ids (crate `SetIdentity::stable`). -/
  stableIds : Bool
  contextReads : List ContextRead

/-- A sorted list without duplicates (crate `BTreeSet` iteration). -/
def sortedStrings (xs : List String) : List String :=
  (xs.mergeSort fun a b => decide (a ≤ b)).eraseDups

/-- A map sorted by key (crate `BTreeMap` iteration). -/
def sortedPairs (xs : List (String × String)) : List (String × String) :=
  xs.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- Each entry's rules: their revisions, spans, annotations and Cedar policies, and the reads of
the request context, numbered from the entry's first rule. -/
structure EntryFacts where
  revisions : List String
  spans : List Span
  annotations : List (List Surface.Annotation)
  reads : List ContextRead

/-- What identifies an entry's rules (crate `lower_entry`): each rule's revision, over its
canonical Cedar text and the canonical encodings of its leaves. -/
def entryFacts (b : Base) (e : Entry) : Result EntryFacts := do
  let c := e.lowered.cedarified
  let leaves ← RuleIdentity.leaves c (withConditions c.contextFields e.pinned)
  let canonical ← CedarPrint.ruleCanonical e.input.expanded b.declarations c.enumNames
  return { revisions := RuleIdentity.ruleRevisions canonical leaves
           spans := e.input.expanded.policies.map (·.span)
           annotations := e.input.expanded.policies.map (·.annotations)
           reads := Cedarify.contextReads e.input.expanded }

/-- The whole lowered set, from the merged set and its entries. -/
def full (b : Base) (l : Lowered) (es : List Entry) : Result Full := do
  let facts ← es.mapM (entryFacts b)
  let counts := es.map (·.lowered.cedarified.ruleIds.length)
  -- The index of each entry's first rule in the merged set.
  let starts := (List.range es.length).map fun k => (counts.take k).sum
  let sources := (counts.zipIdx).flatMap fun (n, k) => List.replicate n k
  return {
    lowered := { l with ruleSources := sources }
    rules := (es.flatMap (·.lowered.cedar)).zip (facts.flatMap (·.annotations))
    ruleSpans := facts.flatMap (·.spans)
    ruleSources := sources
    ruleRevisions := facts.flatMap (·.revisions)
    stableIds := es.all (·.input.ids.isSome)
    contextReads := (facts.zip starts).flatMap fun (f, start) =>
      f.reads.map fun r => { r with rule := r.rule + start } }

/-- The augmented fragment of entries (`mergeEntries` up to augmentation), for a schema Cedar
rejects. -/
def augmentedOf (b : Base) (es : List Entry) : Option CedarSchema.Fragment :=
  match es.foldlM (init := ({} : MergedEntries)) MergedEntries.add with
  | .ok m =>
    let c := m.cedarified
    (Augment.augment b.actionSchema b.declarations c.referencedEnums
      (withConditions c.contextFields m.pinned) c.providerFields).toOption
  | .error _ => none

/-! ## The pipeline -/

/-- The service schema's checks (crate `ServiceSchema` construction): the provider
declarations' parser, the event schema's parser, then the declarations' check. -/
def checkShared (s : SharedInput) :
    Result (EventSchemaDsl.EventSchema × Option ProviderDecls.Declarations) := do
  let decls ← match s.providers with
    | none => pure none
    | some r => some <$> r
  let es ← s.eventSchema
  if let some d := decls then Augment.checkDeclarations d
  return (es, decls)

/-- Phase 1 for one entry (crate `ParsedPolicySet::parse`, then `with_ids`): the policy's and the
library's parsers, the library's merge, expansion, and the stable ids. -/
def parseEntry (s : SharedInput) (e : EntryInput) :
    Result (Surface.PolicySet × Option (List String)) := do
  let p ← e.policy
  let lib ← match s.library with
    | none => pure []
    | some r => r
  let merged ← Macros.mergeLibrary p lib
  let expanded ← Macros.expand merged
  let ids ← Ids.assignIds expanded.policies e.ids
  return (expanded, ids)

/-- The prefix of the action schema parser's error (crate `cedarify::parse_base_schema`). -/
def baseSchemaPrefix : String := "parse base schema: "

/-- The prefix derivation gives the same parser's error (crate `event_schema::derive`). -/
def actionSchemaPrefix : String := "parse action schema: "

/-- The action schema, as derivation reads it: one Cedar cannot parse fails derivation, in the
event-schema category, with derivation's message (crate `Base::derive`, whose derivation parses
the schema first, with the same parser). -/
def actionSchemaOf (s : SharedInput) : Result CedarSchema.Fragment :=
  s.actionSchema.mapError fun e =>
    let message := match e.message.dropPrefix? baseSchemaPrefix with
      | some rest => actionSchemaPrefix ++ rest.toString
      | none => e.message
    { e with stage := .derive, category := .eventSchema, message }

/-- Lower entries and merge them, with the whole lowered set; on an error of the schema Cedar
compiles, the augmented fragment. -/
def lowerAndMerge (b : Base) (es : List EntryIn) (tag : Bool) :
    Except (Error × Option CedarSchema.Fragment) Full := do
  let entries ← (lowerEach b tag 0 es).mapError (·, none)
  match mergeEntries b entries with
  | .error e => throw (e, if e.stage == .compileSchema then augmentedOf b entries else none)
  | .ok l => (full b l entries).mapError (·, none)

/-- One policy set, parsed, given its ids, and lowered (crate `LoweredPolicySet::from_str`, with
`with_ids` and `lower_with_distincter`). -/
def lowerFull (s : SharedInput) (e : EntryInput) :
    Except (Error × Option CedarSchema.Fragment) Full := do
  let (evs, decls) ← (checkShared s).mapError (·, none)
  let (expanded, ids) ← (parseEntry s e).mapError (·, none)
  if let some d := e.distincter then (Ids.checkDistincter d).mapError (·, none)
  let frag ← (actionSchemaOf s).mapError (·, none)
  let b ← (Base.derive evs frag decls).mapError (·, none)
  lowerAndMerge b [{ expanded, distincter := e.distincter, ids }] false

/-- An entry's error, naming the entry. -/
def atEntry (k : Nat) (e : Error) : Error := { e with entry := some k }

/-- Several policy sets, each parsed and given its ids, then lowered together (crate
`policy_set::lower_many`): the distincters are checked after every entry is parsed (each is a
Cedar identifier, none repeats, and there is an entry). -/
def lowerManyFull (s : SharedInput) (es : List EntryInput) :
    Except (Error × Option CedarSchema.Fragment) Full := do
  let (evs, decls) ← (checkShared s).mapError (·, none)
  let parsed ← es.zipIdx.mapM fun (e, k) => (parseEntry s e).mapError (atEntry k ·, none)
  let ds := es.map (·.distincter.getD "")
  for (d, k) in ds.zipIdx do
    (Ids.checkDistincter d).mapError (atEntry k ·, none)
  if let some d := Ids.firstRepeat [] ds then
    throw ({ stage := .distincters, category := .duplicateDistincter, message := d }, none)
  if es.isEmpty then
    throw ({ stage := .distincters, category := .noPolicies, message := "" }, none)
  let frag ← (actionSchemaOf s).mapError (·, none)
  let b ← (Base.derive evs frag decls).mapError (·, none)
  lowerAndMerge b ((parsed.zip ds).map fun ((expanded, ids), d) =>
    { expanded, distincter := some d, ids }) true

/-! ## JSON -/

/-- A recorded result, `{"ok": v}` or `{"error": e}`. -/
def resultOfJson {α : Type} [FromJson α] (j : Json) : Except String (Result α) :=
  match j.getObjVal? "ok", j.getObjVal? "error" with
  | .ok v, _ => .ok <$> fromJson? v
  | _, .ok e => .error <$> fromJson? e
  | _, _ => throw s!"not a result: {(j.compress.take 120).toString}"

/-- An optional recorded result: `null` or absent is none. -/
def optResultOfJson {α : Type} [FromJson α] (j : Json) (k : String) :
    Except String (Option (Result α)) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => pure none
  | .ok v => some <$> resultOfJson v

/-- The macro library's definitions as the export records them. -/
structure LibraryJson where
  defs : List Surface.MacroDef
deriving FromJson

/-- An id source: `null`, `"positional"`, `"annotation"`, or `{"explicit": [ids]}`. -/
def idSourceOfJson : Json → Except String IdSource
  | .null => pure .positional
  | .str "positional" => pure .positional
  | .str "annotation" => pure .annotation
  | j => match j.getObjVal? "explicit" with
    | .ok ids => .explicit <$> fromJson? ids
    | .error _ => throw s!"not an id source: {(j.compress.take 120).toString}"

/-- The shared inputs of a record. -/
def sharedOfJson (j : Json) : Except String SharedInput := do
  let library ← (optResultOfJson (α := LibraryJson) j "library").map (·.map (·.map (·.defs)))
  let eventSchema ← resultOfJson (← j.getObjVal? "eventSchema")
  let providers ← optResultOfJson j "providers"
  let actionSchema ← resultOfJson (← j.getObjVal? "actionSchema")
  return { library, eventSchema, providers, actionSchema }

/-- One entry of a record. -/
def entryOfJson (j : Json) : Except String EntryInput := do
  let policy ← resultOfJson (← j.getObjVal? "policy")
  let distincter ← match j.getObjVal? "distincter" with
    | .ok .null | .error _ => pure none
    | .ok d => some <$> fromJson? d
  let ids ← idSourceOfJson ((j.getObjVal? "ids").toOption.getD .null)
  return { policy, distincter, ids }

/-- A finding of the validator, as the crate's conformance record writes it. -/
def findingToJson (f : Conformance.CrateFinding) : Json :=
  Json.mkObj [("code", toJson f.code), ("message", toJson f.message), ("warning", toJson f.warning)]

/-- A located finding: the finding, the index of the rule it is about (`null` for none) and its
span in that rule's source (`null` for the whole rule, or none). -/
def locatedToJson (f : Validate.Located) : Json :=
  Json.mkObj [("code", toJson f.finding.code), ("message", toJson f.finding.message),
    ("warning", toJson f.finding.warning), ("rule", toJson f.rule), ("span", toJson f.span)]

/-- Each rule as Cedar prints it, in rule order: `{"id", "est", "text"}`, its id, Cedar's policy
JSON of it with its annotations (`CedarPrint.policyEst`, crate `Policy::to_json`), and its text
on one line (`CedarPrint.policyText`, crate `Policy`'s `Display`). -/
def Full.policiesJson (f : Full) : Json :=
  Json.arr ((f.rules.zip f.lowered.ruleIds).map fun ((p, anns), id) =>
    Json.mkObj [("id", Lean.toJson id), ("est", CedarPrint.policyEst p anns),
      ("text", Lean.toJson (CedarPrint.policyText p anns))]).toArray

/-- The lowered set's Cedar part, as Cedar prints it: `{"policies", "augmentedSchema"}`, the rules
(`Full.policiesJson`) and the augmented schema in Cedar's JSON schema form
(`SchemaJson.fragmentJson`, crate `SchemaFragment::to_json_value`). Both are the values of the
same keys of `Full.toJson`. A dependent crate whose own Lean code lowers a set with this library
hands this to Rust, where `dogwood_language::frontend_export::cedar_policy_set` builds the Cedar
policy set from the policies' JSON, with their ids and annotations, as the crate's decoder
does. -/
def Full.cedar (f : Full) : Json :=
  Json.mkObj [("policies", f.policiesJson),
    ("augmentedSchema", SchemaJson.fragmentJson f.lowered.augmentedSchema)]

/-- The whole lowered set, as JSON (the FFI format's `Lowered`). -/
def Full.toJson (f : Full) : Json :=
  let l := f.lowered
  let schema := SchemaJson.fragmentJson l.augmentedSchema
  Json.mkObj [
    ("policies", f.policiesJson),
    ("ruleIds", Lean.toJson l.ruleIds),
    ("ruleSpans", Lean.toJson f.ruleSpans),
    ("ruleSources", Lean.toJson f.ruleSources),
    ("ruleRevisions", Lean.toJson f.ruleRevisions),
    ("stableIds", Lean.toJson f.stableIds),
    ("versionHash", Lean.toJson (SchemaJson.versionHash (l.ruleIds.zip f.ruleRevisions) (some schema)
      (sortedStrings l.decisionKinds) l.partitionKeys)),
    ("augmentedSchema", schema),
    ("temporal", Lean.toJson l.temporal),
    ("temporalExecutable", Lean.toJson l.temporalExecutable),
    ("temporalRewritten", Lean.toJson l.temporalRewritten),
    ("partitionKeys", Lean.toJson l.partitionKeys),
    ("providers", Lean.toJson l.providers),
    ("temporalRules", Lean.toJson l.temporalRules),
    ("providerRules", Lean.toJson l.providerRules),
    ("eventSchema", Lean.toJson l.eventSchema),
    ("decisionKinds", Lean.toJson (sortedStrings l.decisionKinds)),
    ("enumNames", Lean.toJson (sortedPairs l.enumNames)),
    ("contextReads", Lean.toJson f.contextReads),
    ("contentHashes", Lean.toJson (l.temporal.map RuleIdentity.contentHash))]

/-- An undecodable input, as an error record (with no augmented schema). -/
def inputError (why : String) : Json :=
  let e : Error :=
    { stage := .pipeline, category := .«export», message := s!"the input does not decode: {why}" }
  Json.mkObj [("error", Lean.toJson e), ("augmentedSchema", .null)]

/-- A pipeline's outcome as JSON: the lowered set and the validator's findings, or the error
(with the augmented schema when Cedar rejected it). -/
def outcomeToJson (r : Except (Error × Option CedarSchema.Fragment) Full) : Json :=
  match r with
  | .error (e, aug) =>
    Json.mkObj [("error", Lean.toJson e),
      ("augmentedSchema", match aug with
        | some f => SchemaJson.fragmentJson f
        | none => .null)]
  | .ok f =>
    let findings := match Validate.validateLocated f.lowered with
      | .ok fs => Json.mkObj [("ok", Json.arr (fs.map locatedToJson).toArray)]
      | .error e => Json.mkObj [("error", Lean.toJson e)]
    Json.mkObj [("ok", Json.mkObj [("lowered", f.toJson), ("findings", findings)])]

/-- Parse, give ids, lower and validate one policy set (the FFI format's `lowerAll`). -/
def lowerAll (j : Json) : Json :=
  match (do return (← sharedOfJson j, ← entryOfJson j)) with
  | .error why => inputError why
  | .ok (s, e) => outcomeToJson (lowerFull s e)

/-- Parse, give ids, lower together and validate several policy sets (the FFI format's
`lowerManyAll`). -/
def lowerManyAll (j : Json) : Json :=
  match (do
      let s ← sharedOfJson j
      let es ← (← j.getObjVal? "entries").getArr?
      return (s, ← es.toList.mapM entryOfJson)) with
  | .error why => inputError why
  | .ok (s, es) => outcomeToJson (lowerManyFull s es)

/-- Phase 1 alone for one policy set (the FFI format's `parseAll`): the expanded set and its
stable ids, or the first error. -/
def parseAll (j : Json) : Json :=
  match (do return (← sharedOfJson j, ← entryOfJson j)) with
  | .error why => inputError why
  | .ok (s, e) =>
    match (do
        let _ ← checkShared s
        let (expanded, ids) ← parseEntry s e
        if let some d := e.distincter then Ids.checkDistincter d
        return (expanded, ids)) with
    | .error e => Json.mkObj [("error", Lean.toJson e)]
    | .ok (expanded, ids) =>
      Json.mkObj [("ok", Json.mkObj [("expanded", Lean.toJson expanded), ("ids", Lean.toJson ids)])]

/-- A JSON function on JSON text: the input parsed (an error record when it is not JSON), the
output compact. -/
def onText (f : Json → Json) (text : String) : String :=
  match Json.parse text with
  | .ok j => (f j).compress
  | .error why => (inputError s!"not JSON: {why}").compress

def lowerAllStr : String → String := onText lowerAll
def lowerManyAllStr : String → String := onText lowerManyAll
def parseAllStr : String → String := onText parseAll

end Dogwood.Frontend.Driver
