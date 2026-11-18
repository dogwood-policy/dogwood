import Dogwood.Spec
import Dogwood.Eval.Decision
import Dogwood.Eval.Validity

/-!
# Conformance harness

Bundles exported by `bridge/` (as JSON, read by `Dogwood.Conformance.Json`) record what the
`dogwood-language` crate in this repository did with each bundle: the stage at which it rejected
the bundle, or, when the bundle lowered, everything the specification needs to validate and
decide it the specification's way:

* the typed event signatures (`EventSignature`, with `FieldDecl`s), and the `max_window` cap;
* the action schema, as Cedar's validator stores it (`ActionSchemaJson`, converted to
  `Cedar.Validation.Schema` by `ActionSchemaJson.toSchema`), without the context attributes the
  crate hoisted;
* the provider declarations;
* the rules, written from the crate's Cedar form with each hoisted temporal field put back as its
  leaf and each hoisted provider field as its invocation;
* every finding the crate's `Validator` reported, with its dialect code;
* for a bundle with traces, the crate's verdict at every event of each trace.

The harness compares the bundle with the specification in three ways.

**Validation, by category.** The specification's decision procedure for validity
(`PolicySet.validationFindings`, which `Dogwood.Thm.validationFindings_eq_nil_iff` proves decides
`PolicySet.Valid`) reports findings by category (`Finding`). The crate's findings are sorted into
the same categories by their messages (`crateCategory`). For each category, the two must report a
finding together, or not at all. A crate finding no category matches is reported as
uncategorized.

**Decisions.** Each trace is replayed with the verified evaluator under the clamping reading,
the crate's (`Dogwood.Eval.authorize`, which `Dogwood.Thm.authorize_eq` proves equal to
`PolicySet.authorize` under a total reading), over the trace an authorizer that stamps in
nanoseconds builds from it: each recorded time, in seconds, is the clock reading of its event in
ticks, and each event is stamped with its reading, or one tick after the last stamp
(`stampedOf`, `Dogwood.Thm.ingest_readings`). The verdict must be the crate's at every event,
except where the specification fails closed on nonconforming or missing data (`FailClosed`):
there the crate's verdict is recorded as a **runtime gap** of that kind, and the verdict the
specification would give on conforming data (`lenientOutcome`) is compared instead, so that the
comparison of the temporal semantics is kept. A trace whose recorded times do not strictly
increase is reported apart: the crate takes its times as given, and a verdict that differs is a
disagreement of stamping.

**Pins.** Every predicate of every exported leaf carries the pins of its event, since the crate
exports its leaves after pin injection (`pinsCarried`).

Every disagreement has a key (`Disagreement.key`). A **baseline** lists the disagreements that
are expected: the known gaps between the crate and the specification. The run fails only on a
disagreement the baseline does not list.
-/

namespace Dogwood.Conformance

open Dogwood.Spec Dogwood.Spec.Temporal
open Dogwood.Eval (Finding)
open Cedar.Spec (EntityType EntityUID)
open Cedar.Validation (CedarType RecordType)
open Cedar.Data (Set Map)

/-! ## The exported bundle -/

/-- A finding the crate's `Validator` reported, with its code, its message, and whether it is a
warning. -/
structure CrateFinding where
  code : String
  message : String
  warning : Bool

/-- An entity type of the action schema, as Cedar's Rust validator stores it: with the entity
types that can be its descendants. -/
structure EntityDecl where
  name : EntityType
  descendants : List EntityType
  attrs : RecordType
  tags : Option CedarType := none
  «enum» : Option (List String) := none

/-- An action of the action schema, with the actions that can be its descendants. -/
structure ActionDecl where
  name : EntityUID
  principals : List EntityType
  resources : List EntityType
  descendants : List EntityUID
  context : RecordType

structure ActionSchemaJson where
  ets : List EntityDecl
  acts : List ActionDecl
  /-- The entity types the schema declares `external` (Cedar 4.14, RFC 116). `ets` holds each as
  Cedar's validator stores one: a standard entity type without attributes or tags. -/
  externalTypes : List EntityType := []
  /-- The actions the schema declares `external`. `acts` holds each as an action that applies to
  no principal and no resource. -/
  externalActions : List EntityUID := []

/-- The action schema in cedar-lean's form, with *ancestor* information: an entity type's
ancestors are the types it is a descendant of, and likewise for actions. This is the conversion
cedar-lean's protobuf decoder makes (`CedarProto/Schema.lean`). -/
def ActionSchemaJson.toSchema (A : ActionSchemaJson) : Cedar.Validation.Schema where
  ets := Map.make (A.ets.map fun d =>
    let ancestors := Set.make ((A.ets.filter fun d' => d'.descendants.contains d.name).map (·.name))
    (d.name, match d.enum with
      | some eids => .enum (Set.make eids)
      | none => .standard ⟨ancestors, d.attrs, d.tags⟩))
  acts := Map.make (A.acts.map fun d =>
    let ancestors := Set.make ((A.acts.filter fun d' => d'.descendants.contains d.name).map (·.name))
    (d.name, ⟨Set.make d.principals, Set.make d.resources, ancestors, d.context⟩))

/-- The provider outputs the crate's policy engine received at each event of a trace, by
provider field: `none` at an event where its policy engine did not run. -/
abbrev ProviderOutputs := List (Option (List (String × Cedar.Spec.Value)))

/-- One trace of a bundle, and the crate's verdict at each of its events: `none` for an event
that decides nothing, `some true` for `Allow`, `some false` for `Deny`. -/
structure TraceCase where
  name : String
  trace : Trace
  verdicts : List (Option Bool)
  /-- The errors the crate's diagnostics report at each event. A decision with errors failed
  closed, in whole or in part. -/
  crateErrors : List (List String) := []
  /-- For a bundle with information providers, the outputs the crate computed. -/
  providerOutputs : Option ProviderOutputs := none
  /-- Whether the crate ingested each event into its history. The crate rejects an event that
  does not conform to the event schema, as ingestion does; an empty list means it ingested every
  event. -/
  ingested : List Bool := []

structure Decisions where
  traces : List TraceCase

structure Lowered where
  schema : EventSchema
  maxWindow : Int
  /-- The `max_horizon` cap, in seconds, if the event schema declares one. -/
  maxHorizon : Option Int := none
  leaves : List Formula
  actionSchema : ActionSchemaJson
  providerDecls : Provider.Declarations := []
  /-- Provider declarations the bridge left out: a type of theirs names an entity type the
  augmented schema does not declare. -/
  providerDeclsSkipped : List String := []
  policies : Policies
  /-- Each hoisted provider field: its id and its invocation. -/
  providers : List (String × Provider.Call) := []
  crateFindings : List CrateFinding := []
  decisions : Option Decisions := none
  /-- Why a bundle with traces was not replayed. -/
  decisionsSkipped : Option String := none

inductive Outcome where
  | rejected (stage message : String)
  | lowered (l : Lowered)

structure Case where
  name : String
  outcome : Outcome

/-- The policy set the bundle is validated and decided against. -/
def Lowered.policySet (l : Lowered) : PolicySet where
  policies := l.policies
  schema := l.schema
  actionSchema := l.actionSchema.toSchema
  maxWindow := l.maxWindow
  maxHorizon := l.maxHorizon
  providerDecls := l.providerDecls
  externalTypes := l.actionSchema.externalTypes
  externalActions := l.actionSchema.externalActions

/-! ## Validation, by category -/

def _root_.Dogwood.Eval.Finding.name : Finding → String
  | .eventName => "event names"
  | .window => "windows"
  | .horizon => "horizons"
  | .binder => "binders"
  | .unbound => "unbound variables"
  | .timepoint => "timepoints"
  | .operand => "comparison operands"
  | .argument => "predicate arguments"
  | .path => "paths"
  | .optional => "optional attributes"
  | .extension => "extension types"
  | .pin => "pins"
  | .summand => "summands"
  | .placement => "placement"
  | .safety => "safety"
  | .timeDependence => "time dependence"
  | .cedar => "cedar"
  | .contextRead => "context reads"
  | .provider => "providers"
  | .schema => "schema well-formedness"

def allFindings : List Finding :=
  [.eventName, .window, .horizon, .binder, .unbound, .timepoint, .operand, .argument, .path, .optional,
   .extension, .pin, .summand, .placement, .safety, .timeDependence, .cedar, .contextRead, .provider, .schema]

/-- `s` contains `t`. -/
def strHas (s t : String) : Bool := (s.splitOn t).length > 1

/-- The category of a crate finding, from its message: `none` for a finding no category of the
specification covers (a warning, say). An impossible policy is a warning of Cedar's Rust
validator, and an error of cedar-lean's; the crate reports it as an error, in the `cedar`
category (a warning of it counts there too). A finding with the code
`context` is about how the Cedar part reads the request context. -/
def crateCategory (f : CrateFinding) : Option Finding :=
  let m := f.message
  if f.warning then
    if f.code == "cedar" && strHas m "policy is impossible" then some .cedar else none
  else if f.code == "cedar" then some .cedar
  else if f.code == "provider" then some .provider
  else if f.code == "context" then some .contextRead
  else if f.code == "schema" then some .schema
  else if strHas m "does not vary with the current timepoint" then some .timeDependence
  else if m.startsWith "predicate `" && (strHas m "does not name a declared event" ||
      strHas m "which is a field group" || strHas m "which is not declared on that event") then
    some .eventName
  else if m.startsWith "temporal window `" then some .window
  else if m.startsWith "temporal condition looks back up to `" then some .horizon
  else if m.startsWith "cannot sum `" then some .summand
  else if strHas m "binds `" && strHas m "to the current timepoint" then some .timepoint
  else if (strHas m "comparison requires numeric operands" ||
      m.startsWith "equality requires both sides") && strHas m "`timepoint`" then
    some .timepoint
  else if m.startsWith "equality requires both sides" || strHas m "ordering requires" ||
      strHas m "comparison requires" then some .operand
  else if m.startsWith "argument `" && strHas m "expects" then some .argument
  else if strHas m "has no context field" || strHas m "record has no field" ||
      strHas m "does not resolve for every entity" ||
      strHas m "accesses a field of a non-record type" || strHas m "is an enum entity type" ||
      strHas m "unknown entity type" || strHas m "is not a declared entity type" ||
      strHas m "is not a declared action" || strHas m "does not parse as a `decimal`" then
    some .path
  else if strHas m "wildcard" then some .placement
  else if strHas m "reads the optional attribute" && strHas m "`has` test" then some .optional
  else if m.startsWith "pin `" then some .pin
  else if strHas m "binds `" && strHas m "more than once" then some .binder
  else if strHas m "the binder `" && strHas m "names no declared entity type" then some .binder
  else if m.startsWith "the binder `" &&
      strHas m "temporal conditions do not support Cedar's" then some .binder
  else if strHas m "temporal conditions do not support Cedar's" then some .extension
  else none

/-- The categories of the specification's findings. -/
def Lowered.specCategories (l : Lowered) : List Finding := l.policySet.validationFindings.eraseDups

def Lowered.crateCategories (l : Lowered) : List Finding :=
  (l.crateFindings.filterMap crateCategory).eraseDups

/-- The crate's error findings no category covers. -/
def Lowered.uncategorized (l : Lowered) : List CrateFinding :=
  l.crateFindings.filter fun f => !f.warning && (crateCategory f).isNone

/-! ## Decisions -/

def noProviders : Provider.Providers := Provider.total fun _ => .prim (.bool false)

mutual

/-- Two resolved arguments are the same. -/
def argValueBeq : Provider.ArgValue → Provider.ArgValue → Bool
  | .absent, .absent => true
  | .value v, .value w => decide (v = w)
  | .list xs, .list ys => argValuesBeq xs ys
  | _, _ => false

def argValuesBeq : List Provider.ArgValue → List Provider.ArgValue → Bool
  | [], [] => true
  | x :: xs, y :: ys => argValueBeq x y && argValuesBeq xs ys
  | _, _ => false

end

/-- Two resolved invocations are the same. -/
def resolvedBeq (a b : Provider.ResolvedCall) : Bool :=
  decide (a.function = b.function) && argValuesBeq a.args b.args &&
    a.methods.length == b.methods.length &&
    (a.methods.zip b.methods).all fun (m, m') => m.1 == m'.1 && argValuesBeq m.2 m'.2

/-- The providers of a decision at the event `e`, read off the outputs `outs` the crate bound
there: an invocation that one of the provider fields `fields` resolves to on `e` has the output
the crate bound for that field. Where the crate recorded no outputs, its policy engine did not
run, and every invocation fails. -/
def providersAt (fields : List (String × Provider.Call)) (e : Event) :
    Option (List (String × Cedar.Spec.Value)) → Provider.Providers
  | none => fun _ => .error
  | some outs => fun rc =>
    match fields.find? (fun f => resolvedBeq (f.2.resolve e) rc) with
    | some (id, _) =>
      match outs.lookup id with
      | some v => .value v
      | none => .error
    | none => .value (.prim (.bool false))

/-- A verdict, as the crate's export records it. -/
def verdict : Dogwood.Spec.Outcome → Option Bool
  | .noDecision => none
  | .failClosed _ => some false
  | .decided r => some (r.decision == .allow)

def showVerdict : Option Bool → String
  | none => "no decision"
  | some true => "ALLOW"
  | some false => "DENY"

/-- The kinds of nonconforming or missing data on which a decision fails closed. -/
def _root_.Dogwood.Spec.FailClosed.nonconforming? : FailClosed → Option String
  | .nonconformingEvent => some "nonconforming decision event"
  | .nonconformingContext => some "nonconforming request context"
  | .nonconformingEntities => some "nonconforming entity store"
  | .missingScopeEntity => some "missing scope entity"
  | .nonconformingProviderOutput => some "nonconforming provider output"
  | _ => none

/-- The outcome the specification gives at timepoint `n` when the data the decision reads
conform and are supplied: `PolicySet.decideWith` without its conformance checks and its check of
the scope entities. At an event whose data conform and are supplied it is `Eval.authorize`'s
(`Dogwood.Thm.decideWith_of_admits`). Where a scope entity is missing, the temporal leaves read
its attributes as values that do not resolve, as the crate's bare entity does. -/
def lenientOutcome (ι : ImplChoices) (P : PolicySet) (ω : Provider.Providers) (σ : Trace)
    (n : Nat) : Dogwood.Spec.Outcome :=
  match σ[n]? with
  | none => .noDecision
  | some p =>
    if !P.schema.isDecisionKind p.event.kind then .noDecision
    else
      match p.event.principal, p.event.resource with
      | none, _ => .failClosed .noPrincipal
      | some _, none => .failClosed .noResource
      | some pr, some rs =>
        if P.policies.providersFail ω p.event then .failClosed .providerError
        else .decided (isAuthorized (Eval.leaves ι P ω σ n p.event) (p.event.request pr rs)
          (P.decisionEntities p.event) P.policies)

/-- The specification's outcome at timepoint `n`, and the outcome on conforming data. -/
structure Replayed where
  outcome : Dogwood.Spec.Outcome
  lenient : Dogwood.Spec.Outcome

/-- The specification's outcomes at each timepoint of `σ`, with each decision's providers read
off the crate's outputs when there are any. -/
def replay (P : PolicySet) (fields : List (String × Provider.Call)) (σ : Trace)
    (outputs : Option ProviderOutputs) : List Replayed :=
  (List.range σ.length).map fun n =>
    let ω := match outputs, σ[n]? with
      | some outs, some p => providersAt fields p.event outs[n]?.join
      | _, _ => noProviders
    ⟨Eval.authorize ImplChoices.clamp P ω σ n, lenientOutcome ImplChoices.clamp P ω σ n⟩

/-- A disagreement between the crate and the specification on one bundle. -/
inductive Disagreement where
  /-- The specification reports findings of the category and the crate none, or the converse. -/
  | validation (category : Finding) (specOnly : Bool)
  /-- A crate finding no category covers. -/
  | uncategorized (message : String)
  /-- The specification fails a decision closed on nonconforming or missing data that the crate
  decided. -/
  | runtime (kind : String) (trace : String) (events : List Nat)
  /-- A verdict differs, at an event whose data conform, or on conforming data. -/
  | decision (trace : String) (event : Nat) (spec crate : Option Bool)
  /-- A verdict differs on a trace whose recorded times do not strictly increase: the
  specification decides over the trace its authorizer stamps, the crate over the times as
  recorded. -/
  | stamping (trace : String) (event : Nat) (spec crate : Option Bool)
  /-- A trace's replay could not be compared. -/
  | replay (trace : String) (why : String)
  /-- An exported leaf has a predicate without a pin of its event. -/
  | pins (leaves : List Nat)

/-- The key of a disagreement, which a baseline lists. -/
def Disagreement.key : Disagreement → String
  | .validation c specOnly =>
    s!"validation {c.name}: " ++ (if specOnly then "specification only" else "crate only")
  | .uncategorized m => s!"uncategorized: {m}"
  | .runtime k _ _ => s!"runtime: {k}"
  | .decision t i _ _ => s!"decision: {t}@{i}"
  | .stamping t i _ _ => s!"stamping: {t}@{i}"
  | .replay t _ => s!"replay: {t}"
  | .pins _ => "pins"

/-- The kind of a disagreement, for summaries. -/
def Disagreement.kind : Disagreement → String
  | .validation c specOnly =>
    s!"validation {c.name} (" ++ (if specOnly then "specification only" else "crate only") ++ ")"
  | .uncategorized _ => "uncategorized crate finding"
  | .runtime k _ _ => s!"runtime gap, {k}"
  | .decision _ _ _ _ => "decision"
  | .stamping _ _ _ _ => "decision on a stamped trace"
  | .replay _ _ => "replay"
  | .pins _ => "pin injection"

def Disagreement.render : Disagreement → String
  | .validation c true => s!"validation, {c.name}: the specification reports a finding; the crate none"
  | .validation c false => s!"validation, {c.name}: the crate reports a finding; the specification none"
  | .uncategorized m => s!"uncategorized crate finding: {m}"
  | .runtime k t evs => s!"runtime gap, {k}: the crate decided {t} @{evs}"
  | .decision t i a b => s!"{t} @{i}: the specification says {showVerdict a}, the crate {showVerdict b}"
  | .stamping t i a b =>
    s!"{t} @{i}: over the stamped trace the specification says {showVerdict a}; over the " ++
      s!"recorded times the crate says {showVerdict b}"
  | .replay t why => s!"{t}: {why}"
  | .pins ls => s!"pin injection: leaves {ls} have a predicate without a pin of its event"

/-- Where one trace's verdicts disagree with the crate's. At an event where the specification
fails closed on nonconforming or missing data that the crate decided without failing, the
disagreement is a runtime gap, and the outcome on conforming data is compared too. Where the
crate denied and reported errors, it failed as well. A crate that allowed did not fail, whatever
errors it reported: a rule whose Cedar part errs is skipped, and another rule allows. -/
def compareTrace (name : String) (spec : List Replayed) (crate : List (Option Bool))
    (errors : List (List String)) : List Disagreement :=
  if spec.length != crate.length then
    [.replay name s!"the specification replays {spec.length} events, the crate {crate.length}"]
  else
    let indexed := (spec.zip crate).zipIdx
    let crateFailed := fun (i : Nat) => !(errors[i]?.getD []).isEmpty
    let gaps : List (String × Nat) := indexed.filterMap fun ((r, c), i) =>
      match r.outcome with
      | .failClosed reason =>
        match reason.nonconforming?, c with
        | some k, some allowed => if crateFailed i && !allowed then none else some (k, i)
        | _, _ => none
      | _ => none
    let kinds := (gaps.map (·.1)).eraseDups
    let runtime := kinds.map fun k => Disagreement.runtime k name ((gaps.filter (·.1 == k)).map (·.2))
    let decisions := indexed.filterMap fun ((r, c), i) =>
      let gap := gaps.any (·.2 == i)
      let v := verdict (if gap then r.lenient else r.outcome)
      if v != c then some (Disagreement.decision name i v c) else none
    runtime ++ decisions

/-- The positions of the events of `σ` that conform to the event schema of `P`
(`Trace.conforming`). -/
def conformingPositions (P : PolicySet) (σ : Trace) : List Nat :=
  (σ.zipIdx.filter fun (p, _) => decide (p.event.Conforms P.actionSchema P.schema)).map (·.2)

/-- The clock readings of a recorded trace: its events at their recorded times, which the crate's
traces give in seconds, in ticks of the policy set's clock (`PolicySet.tickRate`, nanoseconds;
`Trace.readings`). -/
def readingsOf (P : PolicySet) (σ : Trace) : Trace := σ.scale P.tickRate.perSecond

/-- The trace an authorizer built with `P` stamps from a recorded trace: each event stamped with
its reading, or one tick after the last stamp (`Trace.stamp`; `Dogwood.Thm.ingest_readings`). -/
def stampedOf (P : PolicySet) (σ : Trace) : Trace := (readingsOf P σ).stamp

/-- The recorded times of the trace strictly increase, so that stamping changes none of them
(`Dogwood.Thm.stamp_of_strictlyIncreasing`), and the crate, which takes them as given, decides
over the same times. -/
def TraceCase.increasing (t : TraceCase) : Bool :=
  (t.trace.zip t.trace.tail).all fun (p, q) => p.ts < q.ts

/-- The crate ingested the event at position `i` of the trace. -/
def TraceCase.crateIngested (t : TraceCase) (i : Nat) : Bool := (t.ingested[i]?).getD true

/-- The specification's outcomes at each timepoint of `t.trace` when its history holds the
events the crate ingested, stamped as the specification's authorizer stamps them (`stampedOf`):
the outcome at an ingested event is the replay's over the ingested events, and at another event,
the replay's over the whole trace. For a crate that ingests the conforming events alone, the
history is what ingestion keeps (`Dogwood.Thm.ingest_readings`); for one that ingests every event,
this is the replay over the whole trace. -/
def replayIngested (P : PolicySet) (fields : List (String × Provider.Call)) (t : TraceCase) :
    List Replayed :=
  let whole := replay P fields (stampedOf P t.trace) t.providerOutputs
  let kept := (List.range t.trace.length).filter t.crateIngested
  if kept.length == t.trace.length then whole
  else
    let outputs := t.providerOutputs.map fun outs => kept.map fun i => outs[i]?.join
    let sub := replay P fields (stampedOf P (kept.filterMap (t.trace[·]?))) outputs
    (List.range t.trace.length).filterMap fun i =>
      match kept.idxOf? i with
      | some k => sub[k]?
      | none => whole[i]?

/-- Where ingestion's rejection of nonconforming events changes a decision: the specification's
verdicts over the conforming events, stamped (`Dogwood.Thm.ingest_readings`), against the crate's
at the same events. The events of the trace that do not conform, and that the crate ingested, are
reported too. -/
def ingestionChanges (P : PolicySet) (fields : List (String × Provider.Call)) (t : TraceCase) :
    List Disagreement :=
  let kept := conformingPositions P t.trace
  if kept.length == t.trace.length then []
  else
    let rejected := (List.range t.trace.length).filter (!kept.contains ·)
    let ingested := rejected.filter t.crateIngested
    let outputs := t.providerOutputs.map fun outs => kept.map fun i => outs[i]?.join
    let spec := replay P fields (stampedOf P (Trace.conforming P t.trace)) outputs
    let crateFailed := fun (i : Nat) => !(t.crateErrors[i]?.getD []).isEmpty
    -- Where the specification fails closed on missing or nonconforming data that the crate
    -- decided without an error, the outcome on conforming data is compared, as `compareTrace`
    -- does: that runtime gap is reported there, not again here.
    let changed := (spec.zip kept).filterMap fun (r, i) =>
      let c := t.verdicts[i]?.join
      let gap := match r.outcome, c with
        | .failClosed reason, some allowed => reason.nonconforming?.isSome && (allowed || !crateFailed i)
        | _, _ => false
      if verdict (if gap then r.lenient else r.outcome) != c then some i else none
    (if ingested.isEmpty then [] else [.runtime "nonconforming event ingested" t.name ingested]) ++
      (if changed.isEmpty then []
       else [.runtime "decision changed by an event ingestion rejects" t.name changed])

/-- Where the replay of one trace disagrees with the crate. The specification decides over the
trace its authorizer stamps from the recorded times; the crate takes the times as given. When the
recorded times strictly increase, the two traces have the same times. When they do not, a verdict
that differs is a disagreement of stamping (`Disagreement.stamping`). -/
def TraceCase.disagreements (P : PolicySet) (fields : List (String × Provider.Call))
    (t : TraceCase) : List Disagreement :=
  let ds := compareTrace t.name (replayIngested P fields t) t.verdicts t.crateErrors ++
    ingestionChanges P fields t
  if t.increasing then ds
  else
    -- A decision that stamping changes is reported once, as stamping: where ingestion keeps the
    -- events the crate ingested, the change ingestion would show is the same.
    let stamped := ds.filterMap fun
      | .decision _ i _ _ => some i
      | _ => none
    ds.filterMap fun
      | .decision n i a b => some (.stamping n i a b)
      | .runtime k n evs =>
        if k == "decision changed by an event ingestion rejects" then
          let evs := evs.filter (!stamped.contains ·)
          if evs.isEmpty then none else some (.runtime k n evs)
        else some (.runtime k n evs)
      | d => some d

/-- What a trace whose recorded times do not strictly increase shows about the crate: the events
whose reading is not after the last stamp, which the authorizer stamps one tick after it, how
many of them the crate decided, and at how many events the specification's verdict over the
stamped trace differs from the crate's over the recorded times. -/
structure Restamped where
  name : String
  restamped : Nat
  restampedDecided : Nat
  changed : Nat

def TraceCase.restamped? (P : PolicySet) (fields : List (String × Provider.Call)) (bundle : String)
    (t : TraceCase) : Option Restamped :=
  if t.increasing then none
  else
    let late := ((readingsOf P t.trace).zip (stampedOf P t.trace)).zipIdx.filterMap
      fun ((p, q), i) => if p.ts != q.ts then some i else none
    let decided := late.filter fun i => (t.verdicts[i]?.join).isSome
    let changed := (t.disagreements P fields).filter fun
      | .stamping _ _ _ _ => true
      | _ => false
    some ⟨s!"{bundle}/{t.name}", late.length, decided.length, changed.length⟩

/-- The events of the trace that ingestion rejects as nonconforming (`Rejection.nonconforming`). -/
def countNonconforming (P : PolicySet) (σ : Trace) : Nat :=
  (σ.filter fun p => !decide (p.event.Conforms P.actionSchema P.schema)).length

/-! ## Pins -/

end Dogwood.Conformance

namespace Dogwood.Spec.Temporal

open Cedar.Spec (EntityUID)

mutual

/-- Every predicate of the condition, with its action, kind, and arguments, including those in
aggregates. -/
def Formula.preds : Formula → List (EntityUID × String × List (Path × Term))
  | .and φ ψ | .since φ _ ψ => Formula.preds φ ++ Formula.preds ψ
  | .not φ | .formerly _ φ | .previous _ φ | .exist _ φ => Formula.preds φ
  | .pred a k args => [(a, k, args)]
  | .cmp _ l r => Term.preds l ++ Term.preds r
  | .tp _ => []

def Term.preds : Term → List (EntityUID × String × List (Path × Term))
  | .agg (.count _ body) | .agg (.sum _ _ body) => Formula.preds body
  | .arith _ l r => Term.preds l ++ Term.preds r
  | _ => []

end

end Dogwood.Spec.Temporal

namespace Dogwood.Conformance

open Dogwood.Spec Dogwood.Spec.Temporal
open Dogwood.Eval (Finding)

/-- The term is the request-side reference of the pin. -/
def pinIsTerm : PinRef → Term → Bool
  | .scope r p, .scope r' p' => r == r' && p == p'
  | .context p, .context p' => p == p'
  | _, _ => false

/-- Every predicate of the leaf, including those in aggregates, carries an argument for each pin
of its event: what pin injection guarantees (`Formula.injectPins`). -/
def pinsCarried (S : EventSchema) (φ : Formula) : Bool :=
  φ.preds.all fun (a, k, args) =>
    (S.pinsOf a k).all fun pin => args.any fun (f, t) => f == pin.field && pinIsTerm pin.ref t

/-! ## A lowered bundle -/

/-- Where the specification and the crate disagree on a lowered bundle. -/
def Lowered.disagreements (l : Lowered) : List Disagreement :=
  let P := l.policySet
  let spec := l.specCategories
  let crate := l.crateCategories
  let validation := allFindings.filterMap fun c =>
    match spec.contains c, crate.contains c with
    | true, false => some (Disagreement.validation c true)
    | false, true => some (Disagreement.validation c false)
    | _, _ => none
  let uncategorized := (l.uncategorized.map (·.message)).eraseDups.map Disagreement.uncategorized
  let decisions := match l.decisions with
    | some d => d.traces.flatMap (TraceCase.disagreements P l.providers)
    | none => []
  let unpinned := (l.leaves.zipIdx.filter fun (φ, _) => !pinsCarried l.schema φ).map (·.2)
  validation ++ uncategorized ++ decisions ++ (if unpinned.isEmpty then [] else [.pins unpinned])

/-! ## Baselines and reports -/

/-- A baseline: the disagreements that are expected, as `<group> | <bundle> | <key>` lines.
Blank lines and lines starting with `#` are ignored. -/
abbrev Baseline := List (String × String × String)

def parseBaseline (text : String) : Baseline :=
  (text.splitOn "\n").filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none
    else match line.splitOn " | " with
      | [g, b, k] => some (g.trimAscii.toString, b.trimAscii.toString, k.trimAscii.toString)
      | _ => none

/-- The baseline entries of one group, as `(bundle, key)` pairs. -/
def Baseline.forGroup (B : Baseline) (group : String) : List (String × String) :=
  (B.filter (·.1 == group)).map (·.2)

/-- The baseline lines that list every disagreement of a group. -/
def baselineLines (group : String) (cases : List Case) : List String :=
  cases.flatMap fun c =>
    match c.outcome with
    | .lowered l => (l.disagreements.map (·.key)).eraseDups.map fun k => s!"{group} | {c.name} | {k}"
    | .rejected _ _ => []

structure Report where
  total : Nat := 0
  lowered : Nat := 0
  rejected : List (String × String) := []
  /-- Bundles with disagreements the baseline does not list, and the disagreements. -/
  unexpected : List (String × List Disagreement) := []
  /-- Bundles with disagreements the baseline lists, and the disagreements. -/
  expected : List (String × List Disagreement) := []
  /-- Baseline entries for this group's bundles that no disagreement matched. -/
  stale : List (String × String) := []
  /-- Bundles whose traces were replayed, the traces, and their events. -/
  replayed : Nat := 0
  traces : Nat := 0
  events : Nat := 0
  /-- Bundles with traces that were not replayed, and why. -/
  skipped : List (String × String) := []
  /-- Replayed bundles with information providers. -/
  withProviders : Nat := 0
  /-- Traces whose recorded times do not strictly increase. -/
  restamped : List Restamped := []
  /-- Per category, the bundles in which the specification, and the crate, report a finding. -/
  specFindings : List (Finding × Nat) := []
  crateFindings : List (Finding × Nat) := []
  /-- Per kind of nonconforming or missing data, the decisions the crate made that the
  specification fails closed. -/
  runtimeGaps : List (String × Nat) := []
  /-- Events of replayed traces that ingestion would reject as nonconforming. -/
  nonconformingEvents : Nat := 0

def bump {α : Type} [BEq α] (xs : List (α × Nat)) (a : α) (n : Nat := 1) : List (α × Nat) :=
  if xs.any (·.1 == a) then xs.map fun (b, m) => if b == a then (b, m + n) else (b, m)
  else xs ++ [(a, n)]

instance : BEq Finding := ⟨fun a b => decide (a = b)⟩

/-- Add one lowered bundle's disagreements and counts to the report. -/
def Report.addLowered (r : Report) (baseline : List (String × String)) (name : String)
    (l : Lowered) : Report :=
  let ds := l.disagreements
  let listed := fun (d : Disagreement) => baseline.contains (name, d.key)
  let surprises := ds.filter (!listed ·)
  let known := ds.filter listed
  let stale := baseline.filter fun (b, k) => b == name && !ds.any (·.key == k)
  let r := { r with total := r.total + 1 }
  let r := { r with lowered := r.lowered + 1 }
  let r := if surprises.isEmpty then r else { r with unexpected := r.unexpected ++ [(name, surprises)] }
  let r := if known.isEmpty then r else { r with expected := r.expected ++ [(name, known)] }
  let r := { r with stale := r.stale ++ stale }
  let r := { r with specFindings := l.specCategories.foldl (fun acc f => bump acc f) r.specFindings }
  let r := { r with crateFindings := l.crateCategories.foldl (fun acc f => bump acc f) r.crateFindings }
  let addGap := fun (acc : List (String × Nat)) (d : Disagreement) => match d with
    | .runtime k _ evs => bump acc k evs.length
    | _ => acc
  let r := { r with runtimeGaps := ds.foldl addGap r.runtimeGaps }
  let r := match l.decisions with
    | some (d : Decisions) =>
      let ts : List TraceCase := d.traces
      let r := { r with replayed := r.replayed + 1 }
      let r := { r with traces := r.traces + ts.length }
      let r := { r with events := r.events + (ts.map fun (t : TraceCase) => t.trace.length).sum }
      let r := { r with withProviders := r.withProviders + (if l.providers.isEmpty then 0 else 1) }
      let restamped := ts.filterMap (TraceCase.restamped? l.policySet l.providers name)
      let r := { r with restamped := r.restamped ++ restamped }
      { r with nonconformingEvents := r.nonconformingEvents +
          (ts.map fun (t : TraceCase) => countNonconforming l.policySet t.trace).sum }
    | none => r
  match l.decisionsSkipped with
  | some why => { r with skipped := r.skipped ++ [(name, why)] }
  | none => r

def report (baseline : List (String × String)) (cases : List Case) : Report :=
  cases.foldl (init := ({} : Report)) fun r c =>
    match c.outcome with
    | .rejected stage _ => { r with total := r.total + 1, rejected := r.rejected ++ [(c.name, stage)] }
    | .lowered l => r.addLowered baseline c.name l

/-- `n` events, in words. -/
private def countEvents (n : Nat) : String := if n == 1 then "1 event" else s!"{n} events"

def Report.render (r : Report) : String :=
  let stages := r.rejected.map (·.2) |>.eraseDups
  let byStage := stages.map fun s => s!"{s}: {(r.rejected.filter (·.2 == s)).length}"
  let reasons := r.skipped.map (·.2) |>.eraseDups
  let byReason := reasons.map fun s => s!"{s}: {(r.skipped.filter (·.2 == s)).length}"
  let count (xs : List (Finding × Nat)) (f : Finding) : Nat :=
    (xs.find? (·.1 == f)).map (·.2) |>.getD 0
  let categories := allFindings.filterMap fun f =>
    let s := count r.specFindings f
    let c := count r.crateFindings f
    if s == 0 && c == 0 then none else some s!"{f.name} {s}/{c}"
  let gaps := r.runtimeGaps.map fun (k, n) => s!"{k}: {n}"
  let breaks :=
    if r.restamped.isEmpty then ""
    else
      s!"\n  {r.restamped.length} traces whose recorded times do not strictly increase; " ++
      "the specification decides over the trace its authorizer stamps:" ++
      String.join (r.restamped.map fun b =>
        s!"\n    {b.name}: the authorizer stamps {countEvents b.restamped} one tick after " ++
        s!"the last stamp, of which the crate decided {b.restampedDecided}; the verdicts differ " ++
        s!"at {countEvents b.changed}")
  let expectedKinds := r.expected.foldl (fun acc (_, ds) =>
    ds.foldl (fun acc d => bump acc (d.kind)) acc) ([] : List (String × Nat))
  let expectedSummary :=
    if expectedKinds.isEmpty then ""
    else "\n  expected disagreements, by kind: " ++
      "; ".intercalate (expectedKinds.map fun (k, n) => s!"{k}: {n}")
  let block (title : String) (xs : List (String × List Disagreement)) : String :=
    if xs.isEmpty then ""
    else s!"\n  {title}:" ++ String.join (xs.map fun (n, ds) =>
      "\n    " ++ n ++ String.join (ds.map ("\n      " ++ ·.render)))
  s!"{r.total} bundles: {r.lowered} lowered, {r.rejected.length} rejected ({", ".intercalate byStage}); " ++
  s!"replayed {r.traces} traces ({r.events} events) of {r.replayed} bundles " ++
  s!"({r.withProviders} with information providers), " ++
  s!"{r.skipped.length} not replayed ({"; ".intercalate byReason})" ++
  s!"\n  bundles with findings, specification/crate: {", ".intercalate categories}" ++
  s!"\n  runtime gaps (decisions the crate made on nonconforming or missing data): " ++
  (if gaps.isEmpty then "none" else "; ".intercalate gaps) ++
  s!"\n  events ingestion rejects as nonconforming: {r.nonconformingEvents}" ++
  s!"\n  {r.unexpected.length} bundles disagree unexpectedly; {r.expected.length} as the baseline expects" ++
  (if r.stale.isEmpty then "" else s!"; {r.stale.length} baseline entries matched nothing") ++
  block "unexpected disagreements" r.unexpected ++
  expectedSummary ++
  (if r.stale.isEmpty then ""
   else "\n  stale baseline entries:" ++ String.join (r.stale.map fun (b, k) => s!"\n    {b} | {k}")) ++
  breaks

end Dogwood.Conformance
