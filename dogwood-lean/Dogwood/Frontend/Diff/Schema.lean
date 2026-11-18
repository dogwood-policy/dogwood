import Dogwood.Frontend.Diff
import Dogwood.Frontend.SchemaJson

/-! # Checks of the differential harness: Cedar's JSON schema and the version hash

* `augmentJson`: `SchemaJson.fragmentJson` of the crate's augmented fragment against Cedar's own
  JSON of it (`stages.augmentJson`, `SchemaFragment::to_json_value`), as JSON values, with every
  key compared (an attribute may be named `span`).
* `baseJson`: `fragmentJson` of the parsed action schema against the same JSON, on the bundles
  whose augmentation changes nothing (no hoisted field, no provider enum, no pinned builtin
  name).
* `versionHash`: `SchemaJson.versionHash` of the crate's rule ids and revisions (the public
  pipeline's), of `fragmentJson` of the crate's augmented fragment, and of the crate's decision
  kinds and universal pins, against the version hash the crate's pipeline reports. A bundle
  lowered with a distincter, and several policy sets lowered together, are compared whole by
  `lowerAll` and `lowerMany`.
-/

namespace Dogwood.Frontend.Diff.Schema

open Lean (Json ToJson toJson)

/-- The crate's observable recorded under `key` in the stages, which no `Stage` names. -/
def rawStage (b : BundleExport) (key : String) : Except Missing (Result Json) := do
  match ← decodePiece? (α := Json) key ((b.stages.getObjVal? key).toOption.getD Json.null) with
  | some r => pure r
  | none => throw (.notRun key)

/-- The crate's observable under `key`, when it succeeded. -/
def rawStageOk (b : BundleExport) (key : String) : Except Missing Json := do
  match ← rawStage b key with
  | .ok v => pure v
  | .error e => throw (.notRun s!"{key} (the crate failed: {e.message.take 120})")

/-- Compare two JSON values exactly, every key included. -/
def compareJson (lean crate : Json) : Verdict :=
  if lean == crate then .agree else .disagree ((firstDiff "" lean crate).getD "the values differ")

def checks : List Check := [
  { name := "augmentJson", owner := "gaps", run := fun _ b => withInputs (do
      return (← b.stageOk (α := CedarSchema.Fragment) .augment, ← rawStage b "augmentJson"))
      fun (aug, crate) =>
      match crate with
      | .ok j => compareJson (SchemaJson.fragmentJson aug) j
      | .error e => .disagree s!"the crate recorded no JSON: {Error.render e}" },
  { name := "baseJson", owner := "gaps", run := fun _ b => withInputs (do
      return (← b.input (α := CedarSchema.Fragment) "actionSchema",
        ← b.stageOk (α := CedarSchema.Fragment) .augment, ← rawStageOk b "augmentJson"))
      fun (frag, aug, crate) =>
      if toJson frag != toJson aug then .skipped "augmentation changes the fragment"
      else compareJson (SchemaJson.fragmentJson frag) crate },
  { name := "versionHash", owner := "gaps", run := fun _ b =>
      if b.many != Json.null then .skipped "several policy sets (see `lowerMany`)" else
      if (b.inputs.getObjVal? "distincter").toOption.getD .null != .null then
        .skipped "lowered with a distincter, the stages without (see `lowerAll`)"
      else withInputs (do
      match ← b.crateOutcome with
      | .rejected e => throw (.notRun s!"the pipeline (rejected: {e.message.take 80})")
      | .lowered r =>
        return (r, ← b.stageOk (α := CedarSchema.Fragment) .augment,
          ← b.stageOk (α := List String) .decisionKinds, ← b.stageOk (α := List Pin) .universalPins))
      fun (r, aug, kinds, pins) =>
      let lean := SchemaJson.versionHash (r.ruleIds.zip r.ruleRevisions)
        (some (SchemaJson.fragmentJson aug)) kinds pins
      if lean == r.versionHash then .agree
      else .disagree s!"Lean {lean} ≠ crate {r.versionHash}" }
]

end Dogwood.Frontend.Diff.Schema
