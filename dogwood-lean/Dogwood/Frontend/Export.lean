import Dogwood.Frontend.Json
import Dogwood.Frontend.Driver

/-!
# One bundle of the crate's frontend export

A bundle's record, as `bridge/ --frontend` writes it: the parsers' outputs (`inputs`), each
stage's observable (`stages`, keyed by `Stage.name`), the outcome of the crate's public pipeline
(`outcome`), the compiled base and augmented schemas (`baseValidatorSchema`,
`validatorSchema`), and the bundle's record of the default conformance export (`conformance`).

The record is kept as JSON and decoded piece by piece, so that a piece that does not decode
fails only the checks that read it. `BundleExport.crateLowered` assembles the crate's lowered set
from its observables, exactly as the Lean pipeline assembles its own (`assemble`).
-/

namespace Dogwood.Frontend

open Lean (Json FromJson ToJson fromJson? toJson)

/-- A bundle of the frontend export. -/
structure BundleExport where
  name : String
  inputs : Json
  stages : Json
  outcome : Json
  baseValidatorSchema : Json
  validatorSchema : Json
  conformance : Json
  /-- For several policy sets lowered together, their record (`{inputs, outcome}`); then the
  other pieces are absent. -/
  many : Json := Json.null

def BundleExport.ofJson (j : Json) : Except String BundleExport := do
  let name ← field j "name"
  let f ← j.getObjVal? "frontend"
  let get := fun (k : String) => (f.getObjVal? k).toOption.getD Json.null
  return { name, inputs := get "inputs", stages := get "stages", outcome := get "outcome",
           baseValidatorSchema := get "baseValidatorSchema",
           validatorSchema := get "validatorSchema", conformance := get "conformance",
           many := get "many" }

/-- A recorded result, `{"ok": v}` or `{"error": e}`, decoded. -/
def decodeResult {α : Type} [FromJson α] (j : Json) : Except String (Result α) :=
  match j.getObjVal? "ok", j.getObjVal? "error" with
  | .ok v, _ => .ok <$> fromJson? v
  | _, .ok e => .error <$> fromJson? e
  | _, _ => throw s!"not a result: {j.compress.take 200}"

/-- An observable the export did not record: the crate did not run the stage, or a parser
rejected an input. -/
inductive Missing where
  /-- The export has no record for this stage. -/
  | notRun (what : String)
  /-- The record does not decode. -/
  | undecodable (what : String) (why : String)

def Missing.render : Missing → String
  | .notRun w => s!"{w}: not run"
  | .undecodable w why => s!"{w}: does not decode: {why}"

/-- A piece of the record, decoded: `none` when the record has no such piece (`null`). -/
def decodePiece? {α : Type} [FromJson α] (what : String) (j : Json) : Except Missing (Option (Result α)) :=
  match j with
  | .null => pure none
  | _ => match decodeResult j with
    | .ok r => pure (some r)
    | .error e => throw (.undecodable what e)

/-- The crate's observable of `stage`. -/
def BundleExport.stage {α : Type} [FromJson α] (b : BundleExport) (stage : Stage) :
    Except Missing (Result α) := do
  match ← decodePiece? stage.name ((b.stages.getObjVal? stage.name).toOption.getD Json.null) with
  | some r => pure r
  | none => throw (.notRun stage.name)

/-- The crate's observable of `stage`, when it succeeded. -/
def BundleExport.stageOk {α : Type} [FromJson α] (b : BundleExport) (stage : Stage) :
    Except Missing α := do
  match ← b.stage (α := α) stage with
  | .ok v => pure v
  | .error e => throw (.notRun s!"{stage.name} (the crate failed: {e.message.take 120})")

/-- The parsed input `key`, when its parser accepted it; `none` when the bundle has no such
input (no provider declarations, a blank macro library). -/
def BundleExport.input? {α : Type} [FromJson α] (b : BundleExport) (key : String) :
    Except Missing (Option α) := do
  match ← decodePiece? (α := α) key ((b.inputs.getObjVal? key).toOption.getD Json.null) with
  | none => pure none
  | some (.ok v) => pure (some v)
  | some (.error e) => throw (.notRun s!"input {key} (the parser rejected it: {e.message.take 120})")

/-- The parsed input `key`, which every bundle has. -/
def BundleExport.input {α : Type} [FromJson α] (b : BundleExport) (key : String) :
    Except Missing α := do
  match ← b.input? (α := α) key with
  | some v => pure v
  | none => throw (.notRun s!"input {key}")

/-- The macro library's definitions, as the parser read them; none for a blank library. -/
structure Library where
  defs : List Surface.MacroDef
deriving FromJson

/-- The frontend's inputs, when every parser accepted its source. -/
def BundleExport.parsedInputs (b : BundleExport) : Except Missing Inputs := do
  let policy ← b.input (α := Surface.PolicySet) "policy"
  let library ← b.input? (α := Library) "library"
  let eventSchema ← b.input (α := EventSchemaDsl.EventSchema) "eventSchema"
  let providers ← b.input? (α := ProviderDecls.Declarations) "providers"
  let actionSchema ← b.input (α := CedarSchema.Fragment) "actionSchema"
  return { policy, library := (library.map (·.defs)).getD [], eventSchema, providers, actionSchema }

/-- A compiled schema as the bridge records it: `{"ok": ActionSchemaJson}` or
`{"error": message}`. -/
def decodeValidatorSchema (j : Json) : Except Missing (Except String Cedar.Validation.Schema) :=
  match j with
  | .null => throw (.notRun "compiled schema")
  | _ =>
    match j.getObjVal? "ok", j.getObjVal? "error" with
    | .ok v, _ => match fromJson? (α := Conformance.ActionSchemaJson) v with
      | .ok a => pure (.ok a.toSchema)
      | .error e => throw (.undecodable "compiled schema" e)
    | _, .ok e => pure (.error (e.getStr?.toOption.getD e.compress))
    | _, _ => throw (.undecodable "compiled schema" "not a result")

/-- The merged definitions the crate's library merge produced. -/
structure Merged where
  defs : List Surface.MacroDef
deriving FromJson

/-- One cedarified rule as the export records it: its id, and its policy in the
specification's form with the crate's names. -/
structure ExportedPolicy where
  id : String
  spec : Json

instance : FromJson ExportedPolicy where
  fromJson? j := return { id := ← field j "id", spec := ← j.getObjVal? "spec" }

/-- Cedarify's observable, as the export records it. -/
instance : FromJson Cedarified where
  fromJson? j := do
    let ps : List ExportedPolicy ← field j "policies"
    let policies ← ps.mapM fun p => do
      match ← decodeResult (α := Dogwood.Spec.Policy) p.spec with
      | .ok q => pure q
      | .error e => throw s!"rule {p.id}: the bridge could not translate it: {e.message}"
    return { policies, contextFields := ← field j "contextFields",
             providerFields := ← field j "providerFields", ruleIds := ← field j "ruleIds",
             ruleKeys := ← field j "ruleKeys", temporalRules := ← field j "temporalRules",
             providerRules := ← field j "providerRules",
             referencedEnums := ← field j "referencedEnums", enumNames := ← field j "enumNames" }

instance : ToJson Cedarified where
  toJson c := Json.mkObj [
    ("policies", toJson c.policies), ("contextFields", toJson c.contextFields),
    ("providerFields", toJson c.providerFields), ("ruleIds", toJson c.ruleIds),
    ("ruleKeys", toJson c.ruleKeys), ("temporalRules", toJson c.temporalRules),
    ("providerRules", toJson c.providerRules), ("referencedEnums", toJson c.referencedEnums),
    ("enumNames", toJson c.enumNames)]

/-- The crate's lowered set, assembled from its observables. -/
def BundleExport.crateLowered (b : BundleExport) : Except Missing Lowered := do
  let derived ← b.stageOk (α := DerivedEventSchema) .derive
  let pins ← b.stageOk (α := List Pin) .universalPins
  let kinds ← b.stageOk (α := List String) .decisionKinds
  let cedarified ← b.stageOk (α := Cedarified) .cedarify
  let pinned ← b.stageOk (α := List Surface.Temporal.Condition) .injectPins
  let executable ← b.stageOk (α := List Surface.Temporal.Condition) .unorder
  let rewritten ← b.stageOk (α := List Surface.Temporal.Condition) .relativize
  let augmented ← b.stageOk (α := CedarSchema.Fragment) .augment
  let resolved ← b.stageOk (α := List ResolvedProvider) .resolveProviders
  let schema ← match ← decodeValidatorSchema b.validatorSchema with
    | .ok s => pure s
    | .error e => throw (.notRun s!"compiled schema (Cedar rejected it: {e.take 120})")
  let declarations ← b.input? (α := ProviderDecls.Declarations) "providers"
  let expanded ← b.stageOk (α := Surface.PolicySet) .expand
  let pieces : Pieces := {
    derived := derived
    universalPins := pins
    decisionKinds := kinds
    cedarified := cedarified
    pinned := pinned
    executable := executable
    rewritten := rewritten
    augmented := augmented
    schema := schema
    resolved := resolved
    declarations := declarations
    contextReads := Cedarify.authoredReads expanded }
  return assemble pieces

/-- What the crate's public pipeline reports of a set it lowered: the rule ids, the rule
revisions, the content hash of each temporal leaf as authored (after pin injection), the
version hash, and the components on which the export's stages disagree with the pipeline (none,
for a sound export). -/
structure PipelineResult where
  ruleIds : List String
  ruleRevisions : List String
  contentHashes : List String
  versionHash : String
  mismatches : List String
deriving FromJson, ToJson

/-- The crate's public pipeline on the bundle: the error it rejected the bundle with, or what it
reports of the lowered set. -/
inductive CrateOutcome where
  | rejected (e : Error)
  | lowered (r : PipelineResult)

def BundleExport.crateOutcome (b : BundleExport) : Except Missing CrateOutcome :=
  match b.outcome.getObjVal? "rejected", b.outcome.getObjVal? "lowered" with
  | .ok e, _ => match fromJson? e with
    | .ok e => pure (.rejected e)
    | .error why => throw (.undecodable "outcome" why)
  | _, .ok l => match fromJson? l with
    | .ok r => pure (.lowered r)
    | .error why => throw (.undecodable "outcome" why)
  | _, _ => throw (.undecodable "outcome" "neither rejected nor lowered")

/-- The bundle's record of the default conformance export: the stage at which the bridge
rejected the bundle and why, or what it exported. -/
def BundleExport.conformanceOutcome (b : BundleExport) : Except Missing Conformance.Outcome :=
  match b.conformance with
  | .null => throw (.notRun "conformance record")
  | j => match fromJson? j with
    | .ok o => pure o
    | .error why => throw (.undecodable "conformance record" why)

end Dogwood.Frontend
