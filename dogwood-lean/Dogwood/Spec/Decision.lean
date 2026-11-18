import Dogwood.Spec.Authorizer
import Dogwood.Spec.Temporal.Horizon
import Dogwood.Spec.Temporal.Readings
import Dogwood.Spec.Conformance

/-!
# Decisions over a trace

Authorization in Dogwood is event-driven (guide chapter 8, §6). Every event
is ingested into the history; an event of a **decision kind** additionally
produces a response, decided against the history up to and including it.

`PolicySet.authorize ι P ω σ n` is the outcome of ingesting the event at
timepoint `n` of the trace `σ`. Every decision makes the same checks, in this
order (`PolicySet.decideWith`):

1. an event of a non-decision kind produces no response;
2. a decision event with no principal, or no resource, fails closed;
3. a decision event whose logged record does not conform to its signature
   fails closed (`FailClosed.nonconformingEvent`, `Event.Conforms`);
4. a request whose context does not conform to the action schema fails closed
   (`FailClosed.nonconformingContext`, Cedar's `validateRequest`);
5. an entity store that does not conform to the action schema fails closed
   (`FailClosed.nonconformingEntities`, Cedar's `validateEntities`);
6. when a rule whose scope holds at the request has a temporal leaf that reads
   an attribute of a scope entity the event does not supply, the decision fails
   closed (`FailClosed.missingScopeEntity`, `PolicySet.scopeEntitiesSupplied`);
7. when an information-provider invocation of the policy set fails on the
   decision event, the decision fails closed (`FailClosed.providerError`).
   Every invocation in the policy set is evaluated for every decision event
   (guide chapter 5, "The provider contract"), so the decision fails whichever
   rule the failing invocation belongs to;
8. when a provider's output is not a value of its declared type, the decision
   fails closed (`FailClosed.nonconformingProviderOutput`);
9. otherwise the Cedar request is built from the event — its principal,
   action, resource and request context — and decided by the per-request
   authorizer, with every temporal leaf valued by whether it holds at `n` and
   every provider leaf by the output of the providers `ω`;
10. under a reading `ι` that reports an error for some out-of-range results,
   the response is the one every completion of `ι` gives; when two completions
   respond differently, the decision fails closed
   (`FailClosed.temporalError`, `Dogwood.Spec.Temporal.Readings`). Under a
   total reading, such as widening or clamping, this is the response at the
   reading's own leaf valuation.

A temporal leaf is evaluated after pin injection, under the visibility the
event schema determines (global, or key-local under a universal symmetric
pin). An implementation that keeps one log per partition key, each stamped on
its own, decides by `PolicySet.authorizePart` instead
(`Dogwood.Spec.Partitioned`), which evaluates each leaf over the decision's own
partition log.

The entity store of a decision is the schema's action entities and the entity
data supplied with the event; the schema's entities take precedence, so
supplied data cannot change the action hierarchy (`decisionEntities`). The
request's principal and resource need not be supplied. In the Cedar part, an
attribute read of an entity the store does not hold is one of the runtime
errors Cedar's validation cannot rule out (`entityDoesNotExist`), and Cedar
skips the rule that reads it. A temporal leaf that reads such an attribute
would compare a value that does not resolve, so a comparison with it would be
false and its negation true. The decision fails closed instead, at step 6,
whenever a rule whose scope holds has a temporal leaf that reads an attribute of
a scope entity the event does not supply (`FailClosed.missingScopeEntity`).

The crate's front end (`api.rs`, `decide_at` and its caller) makes the same
checks in the same order, except step 6: it adds an unsupplied principal or
resource to the store as an entity without attributes and decides. A temporal
leaf that reads a required attribute of it then compares a value that does not
resolve, so a `forbid` on that comparison does not fire where the specification
fails closed.

The decision is defined for every trace. The timestamps of the trace of
accepted events strictly increase (`Trace.StrictlyIncreasing`), because the
authorizer stamps them, and ingestion keeps nonconforming events out of the
log; `Dogwood.Spec.Ingest` specifies both.

A leaf's value is a proposition, `PolicySet.LeafHolds`, so a decision is not
computable; it is the specification an implementation's decisions must agree
with.

Two variants serve the proofs of implementations and the semantics of policy
updates. `PolicySet.authorizeWith` is the decision with the temporal leaf
values supplied by an implementation; `Dogwood.Thm.authorizeWith_eq` states
when it is `authorize`. `PolicySet.authorizeDeployed` lets each rule observe
the trace from a timepoint of its own, which is how a rule deployed while
events flow reads the history under the prospective reading
(`Dogwood.Spec.Log`).
-/

namespace Dogwood.Spec

open Cedar.Spec (Request Entities EntityData EntityUID EntityType Response Decision)
open Cedar.Data (Set Map)
open Temporal

/-- A Dogwood policy set, with the schemas its validation and its decisions
depend on besides the trace. -/
structure PolicySet where
  policies : Policies
  /-- The derived event schema. -/
  schema : EventSchema
  /-- The action schema, as Cedar's validator reads it: the entity types, and
  the actions with their principal and resource types, ancestors, and context
  record types. It includes the enum entity types the provider declarations
  declare. -/
  actionSchema : Cedar.Validation.Schema
  /-- The event schema's `max_window` cap on a window's authored length, in seconds
  (`Window.withinCap`). -/
  maxWindow : Int := Temporal.defaultMaxWindow
  /-- The event schema's `max_horizon` cap on how far back a temporal leaf looks in total, in
  seconds, if it declares one: the leaf's horizon (`Formula.horizon`, at one tick per second), the
  largest sum of the windows along one chain of operators. Validity requires every leaf to keep
  within a declared cap (`PolicySet.Valid.horizon`), so no event older than it matters to a
  decision (`Dogwood.Thm.authorize_drop_maxHorizon`). `none`, the default, is no cap. -/
  maxHorizon : Option Int := none
  /-- The resolution of the authorizer's clock, the unit its timestamps count and its windows
  are compared in: nanoseconds by default. The crate's reference interpreter reads whole seconds
  (`TickRate.seconds`). -/
  tickRate : TickRate := .nanos
  /-- The declarations of the information providers the rules invoke. -/
  providerDecls : Provider.Declarations := []
  /-- The entity types the action schema declares `external` (Cedar 4.14, RFC 116): declared,
  to be defined in another schema fragment. `actionSchema` holds the view Cedar's request and
  entity validation take of one: a standard entity type without attributes or tags. -/
  externalTypes : List EntityType := []
  /-- The actions the action schema declares `external`. `actionSchema` holds the view Cedar's
  request validation takes of one: an action that applies to no principal and no resource, so
  that no request for it conforms. -/
  externalActions : List EntityUID := []

/-- Why a decision failed closed. A failed-closed decision denies. -/
inductive FailClosed where
  | noPrincipal
  | noResource
  /-- The decision event's logged record does not conform to its signature. -/
  | nonconformingEvent
  /-- The request context does not conform to the action schema. -/
  | nonconformingContext
  /-- The entity store does not conform to the action schema. -/
  | nonconformingEntities
  /-- A rule whose scope holds at the request has a temporal leaf that reads an attribute of a
  scope entity the event does not supply (`PolicySet.scopeEntitiesSupplied`). -/
  | missingScopeEntity
  /-- An information-provider invocation of the policy set failed on the
  decision event. -/
  | providerError
  /-- An information provider's output is not a value of its declared type. -/
  | nonconformingProviderOutput
  /-- The response depends on how an out-of-range result is read, under a
  reading that reports an error (`PolicySet.respond`). -/
  | temporalError
deriving Repr, DecidableEq

/-- The outcome of ingesting one event. -/
inductive Outcome where
  /-- The event is history-only: it decides nothing. -/
  | noDecision
  | failClosed (reason : FailClosed)
  | decided (response : Response)

def Outcome.decision? : Outcome → Option Decision
  | .noDecision => none
  | .failClosed _ => some .deny
  | .decided r => some r.decision

/-! ## Leaves -/

/-- The temporal leaves of a policy set's rules, as authored (before pin
injection). -/
def PolicySet.temporalLeaves (P : PolicySet) : List Formula :=
  P.policies.flatMap fun p => p.toExpr.leaves.filterMap fun
    | .inl φ => some φ
    | .inr _ => none

/-- The longest horizon of the policy set's temporal leaves
(`Formula.horizon`): how far back, in ticks of its clock, any of its decisions
can look (`Dogwood.Thm.authorize_horizon`). -/
def PolicySet.horizon (P : PolicySet) : Int :=
  P.temporalLeaves.foldr (fun φ h => max (φ.horizon P.tickRate) h) 0

/-! ## Information providers -/

/-- The information-provider invocations of the rules, in evaluation order. -/
def Policies.providerCalls (ps : Policies) : List Provider.Call :=
  ps.flatMap fun p => p.toExpr.leaves.filterMap fun
    | .inl _ => none
    | .inr c => some c

/-- Some information-provider invocation of the rules fails on the decision
event `e`. -/
def Policies.providersFail (ps : Policies) (ω : Provider.Providers) (e : Event) : Bool :=
  ps.providerCalls.any fun c => (ω (c.resolve e)).isError

/-- Every information-provider invocation of the rules that produced a value on the
decision event produced a value of its declared output type. An invocation without a
declared type has no conforming output. -/
def PolicySet.providerOutputsConform (P : PolicySet) (ps : Policies) (ω : Provider.Providers)
    (e : Event) : Bool :=
  ps.providerCalls.all fun c =>
    match ω (c.resolve e) with
    | .error => true
    | o => match c.outputType? P.providerDecls with
      | some ty => decide (o.Conforms P.actionSchema ty)
      | none => false

/-! ## The decision -/

/-- The temporal leaf `φ` holds at the decision timepoint `n`. -/
def PolicySet.LeafHolds (ι : ImplChoices) (P : PolicySet) (σ : Trace) (n : Nat)
    (φ : Formula) : Prop :=
  ∃ p, σ[n]? = some p ∧
    Sat ι P.tickRate σ p.event (P.schema.Visible σ p.event) Valuation.empty n
      (φ.injectPins P.schema)

/-- Every result the temporal leaves of the policy set compute at the decision timepoint `n`,
after pin injection, is in the `Long` range under the reading `ι` (`Formula.InRange`). -/
def PolicySet.InRange (ι : ImplChoices) (P : PolicySet) (σ : Trace) (n : Nat) : Prop :=
  ∀ p, σ[n]? = some p → ∀ φ ∈ P.temporalLeaves,
    (φ.injectPins P.schema).InRange ι P.tickRate σ p.event (P.schema.Visible σ p.event)
      Valuation.empty n

/-- The leaf valuation of a decision at timepoint `n`, whose event is `e`. -/
noncomputable def PolicySet.leaves (ι : ImplChoices) (P : PolicySet) (ω : Provider.Providers)
    (σ : Trace) (n : Nat) (e : Event) : Leaves where
  temporal φ := @decide (P.LeafHolds ι σ n φ) (Classical.propDecidable _)
  provider c := (ω (c.resolve e)).leafValue

/-- The action entities of the action schema, with their ancestors, so that
`action in [Group]` resolves. -/
def PolicySet.actionEntities (P : PolicySet) : Entities :=
  P.actionSchema.acts.mapOnValues Cedar.Validation.actionSchemaEntryToEntityData

/-- The entity store of a decision: the schema's action entities and the entity
data supplied with the event. The schema's entities take precedence over
supplied data for the same uid (`Map.make` keeps the earlier entry), so supplied
data cannot change the action hierarchy. -/
def PolicySet.decisionEntities (P : PolicySet) (e : Event) : Entities :=
  Map.make (P.actionEntities.toList ++ e.entities.toList)

/-- The Cedar request of a decision event. -/
def Event.request (e : Event) (principal resource : EntityUID) : Request where
  principal := principal
  action := e.action
  resource := resource
  context := e.context

/-! ## Scope entities

A temporal leaf reads the entity data of the request's principal and resource through
`principal.<path>` and `resource.<path>` terms (`Event.entityAttr?`). The data must come with the
decision event: a decision whose rules read the attributes of a scope entity the event does not
supply fails closed (`FailClosed.missingScopeEntity`). The rule is static: it looks at the rules
whose scope holds at the request, and at what their temporal leaves can read, not at what an
evaluation of them reaches. -/

mutual

/-- The scope entities whose attributes a condition reads: the root of every `principal.<path>`
or `resource.<path>` term, in a comparison operand, a predicate argument, or an aggregation body,
whose path is not empty. The bare root needs no entity data. -/
def Temporal.Formula.scopeReads : Formula → List ScopeRoot
  | .and φ ψ | .since φ _ ψ => φ.scopeReads ++ ψ.scopeReads
  | .not φ | .formerly _ φ | .previous _ φ | .exist _ φ => φ.scopeReads
  | .pred _ _ args => Temporal.Formula.argsScopeReads args
  | .cmp _ l r => l.scopeReads ++ r.scopeReads
  | .tp _ => []

/-- The scope entities whose attributes a term reads. -/
def Temporal.Term.scopeReads : Term → List ScopeRoot
  | .scope r p => if p.isEmpty then [] else [r]
  | .agg a => a.scopeReads
  | .arith _ l r => l.scopeReads ++ r.scopeReads
  | _ => []

def Temporal.Aggregate.scopeReads : Aggregate → List ScopeRoot
  | .count _ body | .sum _ _ body => body.scopeReads

/-- The scope entities whose attributes a predicate's arguments read. -/
def Temporal.Formula.argsScopeReads : List (Path × Term) → List ScopeRoot
  | [] => []
  | (_, t) :: args => t.scopeReads ++ Temporal.Formula.argsScopeReads args

end

/-- The event supplies the entity data of its scope entity `r`: its entity data holds the
entity, when the event has one. -/
def Event.supplies (e : Event) (r : ScopeRoot) : Bool :=
  match e.scope r with
  | some uid => (e.entities.find? uid).isSome
  | none => true

/-- A Cedar result is the value `true`. -/
def isTrueResult : Cedar.Spec.Result Cedar.Spec.Value → Bool
  | .ok (.prim (.bool true)) => true
  | _ => false

/-- The rule's scope holds at the request: Cedar evaluates each of its scope constraints to
`true`. A rule whose scope does not hold is not satisfied, and does not err, whatever its
conditions (`Dogwood.Thm.isAuthorized_congr_scope`). -/
def Policy.ScopeHolds (p : Policy) (req : Request) (es : Entities) : Prop :=
  Cedar.Spec.evaluate p.principalScope.toExpr req es = .ok (.prim (.bool true)) ∧
  Cedar.Spec.evaluate p.actionScope.toExpr req es = .ok (.prim (.bool true)) ∧
  Cedar.Spec.evaluate p.resourceScope.toExpr req es = .ok (.prim (.bool true))

/-- `Policy.ScopeHolds`, as a Boolean (`Dogwood.Thm.scopeHolds_iff`). -/
def Policy.scopeHolds (p : Policy) (req : Request) (es : Entities) : Bool :=
  isTrueResult (Cedar.Spec.evaluate p.principalScope.toExpr req es) &&
  isTrueResult (Cedar.Spec.evaluate p.actionScope.toExpr req es) &&
  isTrueResult (Cedar.Spec.evaluate p.resourceScope.toExpr req es)

/-- **The scope entities the rules read are supplied.** For every rule of `rules` whose scope
holds at the request of the decision event `e`, every temporal leaf of the rule, after pin
injection, reads the attributes only of scope entities the event supplies. -/
def PolicySet.scopeEntitiesSupplied (P : PolicySet) (rules : Policies) (e : Event)
    (pr rs : EntityUID) : Bool :=
  rules.all fun q =>
    !q.scopeHolds (e.request pr rs) (P.decisionEntities e) ||
      q.toExpr.leaves.all fun
        | .inl φ => (φ.injectPins P.schema).scopeReads.all e.supplies
        | .inr _ => true

/-! ## The decision skeleton -/

/-- The outcome of ingesting the event at timepoint `n` of `σ`, with the response computed by
`respond` once the event and the data it carries pass every check; `respond` is given the event,
its principal, and its resource, and returns `none` when the decision fails closed for a
temporal error. Every kind of decision is this skeleton with a `respond` of its own. -/
def PolicySet.decideWith (P : PolicySet) (rules : Policies) (ω : Provider.Providers)
    (σ : Trace) (n : Nat) (respond : Event → EntityUID → EntityUID → Option Response) :
    Outcome :=
  match σ[n]? with
  | none => .noDecision
  | some p =>
    let e := p.event
    if !P.schema.isDecisionKind e.kind then .noDecision
    else
      match e.principal, e.resource with
      | none, _ => .failClosed .noPrincipal
      | some _, none => .failClosed .noResource
      | some pr, some rs =>
        if !decide (e.Conforms P.actionSchema P.schema) then .failClosed .nonconformingEvent
        else if !succeeds (Cedar.Validation.validateRequest P.actionSchema (e.request pr rs)) then
          .failClosed .nonconformingContext
        else if !succeeds (Cedar.Validation.validateEntities P.actionSchema (P.decisionEntities e))
        then .failClosed .nonconformingEntities
        else if !P.scopeEntitiesSupplied rules e pr rs then .failClosed .missingScopeEntity
        else if rules.providersFail ω e then .failClosed .providerError
        else if !P.providerOutputsConform rules ω e then .failClosed .nonconformingProviderOutput
        else
          match respond e pr rs with
          | some r => .decided r
          | none => .failClosed .temporalError

/-! ## The decision -/

/-- The response of a decision at event `e` of `σ`'s timepoint `n`, under the reading `ι`: the
per-request authorizer's response at the leaf valuation every completion of `ι` gives, when the
completions all respond alike (`ImplChoices.supervaluate`). Under a total reading it is the
response at the reading's own leaf valuation (`Dogwood.Thm.respond_total`). When two
completions respond differently, the response depends on how a result `ι` reports an error for
would have been read, and the decision fails closed (`FailClosed.temporalError`). -/
noncomputable def PolicySet.respond (ι : ImplChoices) (P : PolicySet) (ω : Provider.Providers)
    (σ : Trace) (n : Nat) (e : Event) (pr rs : EntityUID) : Option Response :=
  ι.supervaluate fun ι' =>
    isAuthorized (P.leaves ι' ω σ n e) (e.request pr rs) (P.decisionEntities e) P.policies

/-- The outcome of ingesting the event at timepoint `n` of `σ`. -/
noncomputable def PolicySet.authorize (ι : ImplChoices) (P : PolicySet)
    (ω : Provider.Providers) (σ : Trace) (n : Nat) : Outcome :=
  P.decideWith P.policies ω σ n (P.respond ι ω σ n)

/-! ## Decisions with supplied leaf values -/

/-- The outcome at timepoint `n` when an implementation supplies the value of each temporal
leaf at a decision event `e` (`temporal e φ`): `PolicySet.authorize` with the leaves computed
the implementation's way. When the leaf values decide `LeafHolds`, the outcome is `authorize`'s
(`Dogwood.Thm.authorizeWith_eq`). -/
def PolicySet.authorizeWith (P : PolicySet) (ω : Provider.Providers) (σ : Trace) (n : Nat)
    (temporal : Event → Formula → Bool) : Outcome :=
  P.decideWith P.policies ω σ n fun e pr rs =>
    some (isAuthorized ⟨temporal e, fun c => (ω (c.resolve e)).leafValue⟩
      (e.request pr rs) (P.decisionEntities e) P.policies)

/-- The outcome at timepoint `n` when an implementation supplies the value of each temporal leaf
rule by rule (`temporal e q φ`, for the leaf `φ` of the rule `q` at the decision event `e`), as
an implementation that keys a leaf by its rule rather than by its condition does: it may compute
`φ` for one rule and not for another. Values are keyed by the rule and the condition, not by the
occurrence: two occurrences of one condition in a rule, and two equal rules, take the same value.
With the same value for every rule, it is `authorizeWith`
(`Dogwood.Thm.authorizeWith_eq_authorizeWithEach`). -/
def PolicySet.authorizeWithEach (P : PolicySet) (ω : Provider.Providers) (σ : Trace) (n : Nat)
    (temporal : Event → Policy → Formula → Bool) : Outcome :=
  P.decideWith P.policies ω σ n fun e pr rs =>
    some (isAuthorizedEach (e.request pr rs) (P.decisionEntities e)
      (P.policies.map fun q => (q, ⟨temporal e q, fun c => (ω (c.resolve e)).leafValue⟩)))

/-! ## Rules that observe the trace from a timepoint of their own -/

/-- The temporal leaf `φ` holds at the decision timepoint `n` when it observes
only the timepoints from `start` on: the timepoints before `start` are
invisible to it. With `start = 0` this is `LeafHolds`
(`Dogwood.Thm.leafHoldsFrom_zero`). -/
def PolicySet.LeafHoldsFrom (ι : ImplChoices) (P : PolicySet) (σ : Trace) (start n : Nat)
    (φ : Formula) : Prop :=
  ∃ p, σ[n]? = some p ∧
    Sat ι P.tickRate σ p.event (fun k => start ≤ k ∧ P.schema.Visible σ p.event k)
      Valuation.empty n (φ.injectPins P.schema)

/-- The leaf valuation of a decision at timepoint `n`, whose event is `e`, for
a rule that observes the trace from `start` on. -/
noncomputable def PolicySet.leavesFrom (ι : ImplChoices) (P : PolicySet)
    (ω : Provider.Providers) (σ : Trace) (start n : Nat) (e : Event) : Leaves where
  temporal φ := @decide (P.LeafHoldsFrom ι σ start n φ) (Classical.propDecidable _)
  provider c := (ω (c.resolve e)).leafValue

/-- The outcome of ingesting the event at timepoint `n` of `σ` when the rules
in force are `rules`, each with the timepoint from which it observes the trace.
The rules take the place of `P.policies`; `P` supplies the schemas and the
provider declarations. With every rule of `P.policies` observing from `0`, this
is `PolicySet.authorize` (`Dogwood.Thm.authorize_eq_authorizeDeployed`). -/
noncomputable def PolicySet.authorizeDeployed (ι : ImplChoices) (P : PolicySet)
    (ω : Provider.Providers) (σ : Trace) (n : Nat) (rules : List (Policy × Nat)) : Outcome :=
  P.decideWith (rules.map (·.1)) ω σ n fun e pr rs =>
    ι.supervaluate fun ι' => isAuthorizedEach (e.request pr rs) (P.decisionEntities e)
      (rules.map fun (r : Policy × Nat) => (r.1, P.leavesFrom ι' ω σ r.2 n e))

end Dogwood.Spec
