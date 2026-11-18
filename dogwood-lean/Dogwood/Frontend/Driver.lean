import Dogwood.Frontend.Signatures
import Dogwood.Frontend.Macros
import Dogwood.Frontend.Derive
import Dogwood.Frontend.Resolve
import Dogwood.Frontend.Cedarify
import Dogwood.Frontend.Cedarify.Reads
import Dogwood.Frontend.Augment
import Dogwood.Frontend.LeafPasses
import Dogwood.Frontend.Identity
import Dogwood.Frontend.Ids

/-!
# The frontend's pipeline

`parse` and `lower` compose the stages in the order the crate runs them (`api::parse`,
`api::lower`: `Base::derive`, `lower_entry`, `merge`), so that the first stage to fail is the
crate's. `assemble` builds the lowered set from the stages' results, as `merge` does for a single
entry; the differential harness assembles the crate's own lowered set from its observables the
same way.
-/

namespace Dogwood.Frontend

open Surface.Temporal (Condition)

/-- `r`, its error reported at `stage`. -/
def Result.atStage {α : Type} (stage : Stage) (r : Result α) : Result α :=
  r.mapError fun e => { e with stage }

/-- The context fields with their conditions replaced by `conditions`, in order. -/
def withConditions (fields : List ContextField) (conditions : List Condition) : List ContextField :=
  (fields.zip conditions).map fun (f, c) => { f with temporal := { f.temporal with condition := c } }

/-- A context field, as a temporal leaf of the lowered set, with the condition `c`. -/
def ContextField.toTemporalField (f : ContextField) (c : Condition) : TemporalField :=
  { id := f.fieldName, action := f.action, targetActions := f.targetActions,
    principal := f.principal, resource := f.resource,
    condition := { f.temporal with condition := c } }

/-- A provider field and its resolved declaration, as a provider leaf of the lowered set. -/
def ProviderField.toLowered (f : ProviderField) (r : ResolvedProvider) : LoweredProviderField :=
  { id := f.fieldName, action := f.action, targetActions := f.targetActions,
    principal := f.principal, resource := f.resource, invocation := f.invocation,
    methods := f.methods, bodyBase := f.bodyBase, declaration := r.declaration,
    entityTypes := r.entityTypes, entityTypeNames := r.entityTypeNames }

/-- The pieces of a lowered set, as the stages produce them. -/
structure Pieces where
  derived : DerivedEventSchema
  universalPins : List Pin
  decisionKinds : List String
  cedarified : Cedarified
  /-- The context fields' conditions after pin injection. -/
  pinned : List Condition
  executable : List Condition
  rewritten : List Condition
  augmented : CedarSchema.Fragment
  schema : Cedar.Validation.Schema
  resolved : List ResolvedProvider
  declarations : Option ProviderDecls.Declarations
  /-- The reads of the request context the expanded rules make (`Cedarify.authoredReads`). -/
  contextReads : List (Bool × String) := []

/-- The lowered set the pieces make (crate `api::merge`, for one entry). -/
def assemble (p : Pieces) : Lowered :=
  let c := p.cedarified
  let fields := fun (cs : List Condition) =>
    (c.contextFields.zip cs).map fun (f, φ) => f.toTemporalField φ
  { policies := c.policies, augmentedSchema := p.augmented, schema := p.schema,
    temporal := fields p.pinned, temporalExecutable := fields p.executable,
    temporalRewritten := fields p.rewritten, partitionKeys := p.universalPins,
    providers := (c.providerFields.zip p.resolved).map fun (f, r) => f.toLowered r,
    ruleIds := c.ruleIds, temporalRules := c.temporalRules, providerRules := c.providerRules,
    eventSchema := p.derived, decisionKinds := p.decisionKinds, enumNames := c.enumNames,
    declarations := p.declarations, contextReads := p.contextReads }

/-- Phase 1 (crate `ParsedPolicySet::parse`, after the service schema is built): the provider
declarations' check, then the macro library merge and macro expansion. -/
def parse (i : Inputs) : Result Surface.PolicySet := do
  if let some d := i.providers then Augment.checkDeclarations d
  let merged ← Macros.mergeLibrary i.policy i.library
  Macros.expand merged

/-- Phase 2 (crate `ParsedPolicySet::lower`) on an expanded set. -/
def lowerParsed (i : Inputs) (expanded : Surface.PolicySet) : Result Lowered := do
  let derived ← Derive.derive i.eventSchema i.actionSchema
  let pins ← universalPins derived
  let kinds ← decisionKinds derived
  Macros.rejectArrays expanded
  let c ← Cedarify.cedarify expanded i.actionSchema i.providers
  let pinned ← c.contextFields.mapM fun f => LeafPasses.injectPins derived f.temporal.condition
  let augmented ← Augment.augment i.actionSchema i.providers c.referencedEnums
    (withConditions c.contextFields pinned) c.providerFields
  let executable ← pinned.mapM LeafPasses.unorderTimepoints
  let rewritten ← executable.mapM (LeafPasses.relativize derived pins)
  let resolved ← Augment.resolveProviders i.providers c.enumNames c.providerFields
  let schema ← (CedarSchema.resolve augmented).atStage .compileSchema
  let pieces : Pieces := {
    derived := derived
    universalPins := pins
    decisionKinds := kinds
    cedarified := c
    pinned := pinned
    executable := executable
    rewritten := rewritten
    augmented := augmented
    schema := schema
    resolved := resolved
    declarations := i.providers
    contextReads := Cedarify.authoredReads expanded }
  pure (assemble pieces)

/-- Parse and lower (crate `LoweredPolicySet::from_str`). -/
def lower (i : Inputs) : Result Lowered := do
  lowerParsed i (← parse i)

/-! ## Several entries, merged (crate `lower_many`) -/

/-- What lowering derives once from the service schema and the action schema, and shares among
the entries it lowers (crate `api::Base`). -/
structure Base where
  derived : DerivedEventSchema
  universalPins : List Pin
  decisionKinds : List String
  actionSchema : CedarSchema.Fragment
  declarations : Option ProviderDecls.Declarations

/-- Derive the event schema and read its universal pins and decision kinds (crate
`Base::derive`). -/
def Base.derive (eventSchema : EventSchemaDsl.EventSchema) (actionSchema : CedarSchema.Fragment)
    (declarations : Option ProviderDecls.Declarations) : Result Base := do
  let derived ← Derive.derive eventSchema actionSchema
  let pins ← Frontend.universalPins derived
  let kinds ← Frontend.decisionKinds derived
  return { derived, universalPins := pins, decisionKinds := kinds, actionSchema, declarations }

/-- One entry to lower: its expanded policy set, its distincter, and its stable ids. -/
structure EntryIn where
  expanded : Surface.PolicySet
  distincter : Option String := none
  ids : Option (List String) := none

/-- One entry lowered against a base, before augmentation (crate `api::Entry`): cedarify's
result with the rules in Cedar's and the specification's forms, and the context fields'
conditions after pin injection. -/
structure Entry where
  input : EntryIn
  lowered : Cedarify.WithSpec
  pinned : List Condition

/-- Lower one entry (crate `api::lower_entry`): the array check, cedarify under the entry's
distincter and ids, and pin injection. -/
def lowerEntry (b : Base) (e : EntryIn) : Result Entry := do
  Macros.rejectArrays e.expanded
  let w ← Cedarify.cedarifyFull e.expanded b.actionSchema b.declarations e.distincter e.ids
  let pinned ← w.cedarified.contextFields.mapM fun f =>
    LeafPasses.injectPins b.derived f.temporal.condition
  return { input := e, lowered := w, pinned }

/-- The union of two sorted sets, sorted (crate `BTreeSet::extend`); the second as is when the
first is empty. -/
def unionSorted : List String → List String → List String
  | [], b => b
  | a, b => ((a ++ b).mergeSort fun x y => decide (x ≤ y)).eraseDups

/-- A map sorted by key with `(k, v)` inserted, replacing `k`'s value (crate
`BTreeMap::insert`). -/
def insertSorted : List (String × String) → String × String → List (String × String)
  | [], kv => [kv]
  | (k', v') :: rest, (k, v) =>
    if k == k' then (k, v) :: rest
    else if decide (k < k') then (k, v) :: (k', v') :: rest
    else (k', v') :: insertSorted rest (k, v)

/-- A map extended with another's entries (crate `BTreeMap::extend`); the second as is when the
first is empty. -/
def extendSorted : List (String × String) → List (String × String) → List (String × String)
  | [], b => b
  | a, b => b.foldl insertSorted a

/-- The entries merged so far (crate `api::merge`'s accumulators). -/
structure MergedEntries where
  policies : List Dogwood.Spec.Policy := []
  contextFields : List ContextField := []
  providerFields : List ProviderField := []
  ruleIds : List String := []
  ruleKeys : List String := []
  temporalRules : List Nat := []
  providerRules : List Nat := []
  referencedEnums : List String := []
  enumNames : List (String × String) := []
  pinned : List Condition := []
  contextReads : List (Bool × String) := []

/-- The error of a policy id two entries emit (Cedar's `PolicySetError::AlreadyDefined`, as
`PolicySet::add` reports it). -/
def duplicatePolicyError (id : String) : Error :=
  { stage := .merge, category := .policySet,
    message := s!"duplicate template or policy id `{id}`" }

/-- Merge one more entry: its rules after the others', its leaves' rule indices shifted by the
rules before it. Each entry's own ids are distinct (cedarify checks them); an id of a later
entry that an earlier one has is an error, as Cedar's `PolicySet::add` makes it. -/
def MergedEntries.add (m : MergedEntries) (e : Entry) : Result MergedEntries := do
  let c := e.lowered.cedarified
  match m.ruleIds with
  | [] => pure ()
  | ids =>
    match c.ruleIds.find? (ids.contains ·) with
    | some id => throw (duplicatePolicyError id)
    | none => pure ()
  let offset := m.ruleIds.length
  return {
    policies := m.policies ++ c.policies
    contextFields := m.contextFields ++ c.contextFields
    providerFields := m.providerFields ++ c.providerFields
    ruleIds := m.ruleIds ++ c.ruleIds
    ruleKeys := m.ruleKeys ++ c.ruleKeys
    temporalRules := m.temporalRules ++ c.temporalRules.map (· + offset)
    providerRules := m.providerRules ++ c.providerRules.map (· + offset)
    referencedEnums := unionSorted m.referencedEnums c.referencedEnums
    enumNames := extendSorted m.enumNames c.enumNames
    pinned := m.pinned ++ e.pinned
    contextReads := m.contextReads ++ Cedarify.authoredReads e.input.expanded }

/-- The merged entries as one cedarify result. -/
def MergedEntries.cedarified (m : MergedEntries) : Cedarified :=
  { policies := m.policies, contextFields := m.contextFields, providerFields := m.providerFields,
    ruleIds := m.ruleIds, ruleKeys := m.ruleKeys, temporalRules := m.temporalRules,
    providerRules := m.providerRules, referencedEnums := m.referencedEnums,
    enumNames := m.enumNames }

/-- Merge lowered entries, in order, into one lowered set over the base (crate `api::merge`):
the schema augmented once with every entry's hoisted fields, then the executable and
relativized leaves, the providers' declarations, and the compiled schema. -/
def mergeEntries (b : Base) (es : List Entry) : Result Lowered := do
  let m ← es.foldlM (init := ({} : MergedEntries)) MergedEntries.add
  let c := m.cedarified
  let augmented ← Augment.augment b.actionSchema b.declarations c.referencedEnums
    (withConditions c.contextFields m.pinned) c.providerFields
  let executable ← m.pinned.mapM LeafPasses.unorderTimepoints
  let rewritten ← executable.mapM (LeafPasses.relativize b.derived b.universalPins)
  let resolved ← Augment.resolveProviders b.declarations c.enumNames c.providerFields
  let schema ← (CedarSchema.resolve augmented).atStage .compileSchema
  let pieces : Pieces := {
    derived := b.derived
    universalPins := b.universalPins
    decisionKinds := b.decisionKinds
    cedarified := c
    pinned := m.pinned
    executable := executable
    rewritten := rewritten
    augmented := augmented
    schema := schema
    resolved := resolved
    declarations := b.declarations
    contextReads := m.contextReads }
  pure (assemble pieces)

/-- An entry's error, naming the entry (`k`) when `tag`. -/
def tagEntry {α : Type} (tag : Bool) (k : Nat) (r : Result α) : Result α :=
  if tag then r.mapError fun err => { err with entry := some k } else r

/-- Lower each entry, in order; with `tag`, an error names the entry it belongs to, counted from
`k`. -/
def lowerEach (b : Base) (tag : Bool) : Nat → List EntryIn → Result (List Entry)
  | _, [] => pure []
  | k, e :: es => do
    let x ← tagEntry tag k (lowerEntry b e)
    let xs ← lowerEach b tag (k + 1) es
    pure (x :: xs)

/-- Lower entries against a base and merge them (crate `lower_many`, after its checks of the
distincters): the lowered set, and each entry's lowering. With `tag`, an error of an entry's
lowering names the entry. -/
def lowerEntries (b : Base) (es : List EntryIn) (tag : Bool := true) :
    Result (Lowered × List Entry) := do
  let entries ← lowerEach b tag 0 es
  let l ← mergeEntries b entries
  return (l, entries)

/-- The checks `lower_many` makes before it lowers anything (crate `policy_set::lower_many`): no
distincter repeats, there is an entry, and each distincter is a Cedar identifier (the crate's
`Distincter` values are checked when they are made). -/
def checkDistincters (ds : List String) : Result Unit := do
  for d in ds do Ids.checkDistincter d
  if let some d := Ids.firstRepeat [] ds then
    throw { stage := .distincters, category := .duplicateDistincter, message := d }
  if ds.isEmpty then
    throw { stage := .distincters, category := .noPolicies, message := "" }

/-- Lower several policy sets, each under a distincter, and merge them (crate `lower_many`).
The entries share the service schema and the action schema, which are the first entry's (the
crate requires every entry to be parsed with one service schema); each entry's own policy set
and macro library are parsed and expanded, then lowered. -/
def lowerMany (entries : List (Inputs × String)) : Result Lowered := do
  checkDistincters (entries.map (·.2))
  match entries with
  | [] => throw { stage := .distincters, category := .noPolicies, message := "" }
  | (i₀, _) :: _ =>
    if let some d := i₀.providers then Augment.checkDeclarations d
    let expanded ← entries.mapM fun (i, _) => do
      let merged ← Macros.mergeLibrary i.policy i.library
      Macros.expand merged
    let b ← Base.derive i₀.eventSchema i₀.actionSchema i₀.providers
    let (l, _) ← lowerEntries b ((expanded.zip entries).map fun (e, (_, d)) =>
      { expanded := e, distincter := some d })
    return l

end Dogwood.Frontend
