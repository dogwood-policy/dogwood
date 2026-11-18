import Dogwood.Spec.Temporal.Semantics
import Cedar.Validation.Types

/-!
# The derived event schema: decision kinds, pins, and key-local semantics

The event-schema DSL (guide chapter 3) is a template that *derivation* binds
to a concrete action schema. Parsing the DSL and deriving it are front-end
work, done by the `dogwood-language` crate; this specification starts from
the **derived** schema — one signature per action and event kind — and gives
meaning to the three things in it that affect authorization:

* the **decision kinds**, whose events trigger an authorization decision;
* the **pins**, correlations conjoined onto every predicate that names the
  event (pin injection);
* the **universal symmetric pins**, which switch temporal conditions to
  key-local semantics: a condition observes only the events that agree with
  the current request on every such pin.

The reference implementation realizes key-local semantics by a lowering-time
rewrite of each leaf (`event_schema/relativize.rs`) whose verdict over the
whole trace equals the authored leaf's verdict over the key's slice. This
specification states the slice reading directly, as the visibility predicate
`EventSchema.Visible` passed to `Temporal.Sat`.
-/

namespace Dogwood.Spec

open Cedar.Spec (EntityUID Value)
open Temporal

/-- The request-side value a pin correlates a field with. -/
inductive PinRef where
  /-- `= principal` / `= resource`, optionally with an attribute path. -/
  | scope (root : ScopeRoot) (path : Path)
  /-- `= context.<path>` -/
  | context (path : Path)
deriving Repr, DecidableEq, Inhabited

/-- `pin <field> : T = <ref>`. -/
structure Pin where
  field : Path
  ref : PinRef
deriving Repr, DecidableEq, Inhabited

/-- The declared type of an event field. A field spliced from the action's
`context.input` or `context.output` record, or named with a concrete type, has
that Cedar type. A field named with `principalType(A)` or `resourceType(A)`, such
as the reserved `callerPrincipal`, holds an entity of one of the action's
principal or resource types. -/
inductive FieldTy where
  | cedar (ty : Cedar.Validation.CedarType)
  | entities (etys : List Cedar.Spec.EntityType)
deriving Repr, DecidableEq, Inhabited

/-- A declared leaf field of an event: its path (`input.user`, `callerPrincipal`,
…), its type, and whether every event of the signature must log it. A field
spliced from the action schema is required when every attribute along its path
is required there; a field named in the event-schema DSL is optional, unless it
is pinned (`EventSignature.Admits`). -/
structure FieldDecl where
  path : Path
  ty : FieldTy
  required : Bool
deriving Repr, DecidableEq, Inhabited

/-- One derived event signature: an action and an event kind, whether the
kind is a decision kind, the pins declared for it, and its declared leaf fields
with their types. -/
structure EventSignature where
  action : EntityUID
  kind : String
  decision : Bool
  pins : List Pin
  fields : List FieldDecl
deriving Repr, DecidableEq, Inhabited

/-- The declared field at `path`, if any. -/
def EventSignature.field? (s : EventSignature) (path : Path) : Option FieldDecl :=
  s.fields.find? (·.path == path)

/-- A derived event schema. -/
abbrev EventSchema := List EventSignature

/-- The temporal term a pin's reference denotes. -/
def PinRef.toTerm : PinRef → Term
  | .scope root path => .scope root path
  | .context path => .context path

namespace EventSchema

/-- Whether events of `kind` are decision points. A kind is a decision kind
when the schema marks it `decision`; the flag belongs to the kind, across all
actions. -/
def isDecisionKind (S : EventSchema) (kind : String) : Bool :=
  S.any fun s => s.decision && s.kind == kind

/-- The signature for `action` and `kind`, if the schema declares one. -/
def signature? (S : EventSchema) (action : EntityUID) (kind : String) : Option EventSignature :=
  S.find? fun s => s.action == action && s.kind == kind

/-- The pins of the signature for `action` and `kind`; none when the schema
has no such signature. -/
def pinsOf (S : EventSchema) (action : EntityUID) (kind : String) : List Pin :=
  match S.signature? action kind with
  | some s => s.pins
  | none => []

/-- A pin is *symmetric* when its request-side value is the request's principal,
its resource, or a context attribute (`pin f = principal`, `pin f = resource`,
`pin f = context.q`), whatever the pinned field is called. Event conformance
rejects an event whose symmetric-pin field differs from its own request's value
(`Mirrored`). A pin to an attribute of the principal or resource
(`pin dept = principal.dept`, `pin uid = principal.id`) is not symmetric, and
its field need only be logged. -/
def Pin.isSymmetric (p : Pin) : Bool :=
  match p.ref with
  | .context _ => true
  | .scope _ [] => true
  | .scope _ (_ :: _) => false

/-- The universal symmetric pins: the symmetric pins declared, identically,
on every signature of the schema. An empty schema has none. -/
def universalPins : EventSchema → List Pin
  | [] => []
  | s :: rest => s.pins.filter fun p => Pin.isSymmetric p && rest.all (·.pins.contains p)

/-- The event `ev` is *mine* for a decision at `e`: it is an event of a
declared signature, and it agrees with the current request on every
universally pinned field. -/
def Mine (S : EventSchema) (e ev : Event) : Prop :=
  (∃ s ∈ S, s.action = ev.action ∧ s.kind = ev.kind) ∧
  ∀ p ∈ S.universalPins, ∃ w,
    recordPath? ev.logged p.field = some w ∧ p.ref.toTerm.eval? e Valuation.empty = some (.val w)

/-- The timepoints a temporal condition decided at `e` observes. Without a
universal symmetric pin, every timepoint (global semantics); with one, the
timepoints whose event is mine (key-local semantics). -/
def Visible (S : EventSchema) (σ : Trace) (e : Event) (k : Nat) : Prop :=
  S.universalPins = [] ∨ ∃ p, σ[k]? = some p ∧ Mine S e p.event

/-! ## Partitions

An implementation can realize key-local semantics by storing each key's events
apart, as the reference interpreter's partitioned mode does
(`AuthorizerBuilder::partition_temporal`). It files
each event under its *partition key*, the logged values of the universally
pinned fields (`partition_value_of`), and evaluates a decision over the
decision event's partition. On a trace that is `Partitionable`, the partition
of a decision event holds exactly the events the specification makes visible to
the decision (`Dogwood.Thm.visible_iff_partitionKey`).

An implementation that keeps one log per partition key also stamps each log on
its own. `Dogwood.Spec.Partitioned` defines that partitioned evaluation
(`PolicySet.PartLeafHolds`, `PolicySet.authorizePart`): each partition's log is
stamped by the stamping rule of `Dogwood.Spec.Ingest`, and a decision's leaves
are evaluated over its own partition's log. -/

/-- The partition key of an event: the logged value of each universally pinned
field, `none` where the event does not log the field. -/
def partitionKey (S : EventSchema) (ev : Event) : List (Option Value) :=
  S.universalPins.map fun pin => recordPath? ev.logged pin.field

/-- What partitioned evaluation needs of a trace: every event is of a declared
signature and logs every universally pinned field, and a decision event's
logged pin fields hold the pins' request-side values (as `Event::from_request`
arranges). -/
structure Partitionable (S : EventSchema) (σ : Trace) : Prop where
  declared : ∀ (k : Nat) (p : TimePoint), σ[k]? = some p →
    ∃ s ∈ S, s.action = p.event.action ∧ s.kind = p.event.kind
  logged : ∀ (k : Nat) (p : TimePoint), σ[k]? = some p → ∀ pin ∈ S.universalPins,
    (recordPath? p.event.logged pin.field).isSome
  symmetric : ∀ (k : Nat) (p : TimePoint), σ[k]? = some p →
    S.isDecisionKind p.event.kind = true → ∀ pin ∈ S.universalPins,
      (recordPath? p.event.logged pin.field).map .val = pin.ref.toTerm.eval? p.event Valuation.empty

end EventSchema

/-! ## Pin injection -/

mutual

/-- Conjoin each event's pins onto every predicate that names it: the pinned
field is appended as an argument whose term is the pin's request-side
reference. The append is unconditional, so an authored argument for the same
field can only narrow the pin, never relax it. Pins reach predicates in
aggregation bodies, including the bodies of aggregates that are leaves of a
compound operand; predicate arguments are not descended into (no aggregate is
well-placed there). -/
def Temporal.Formula.injectPins (S : EventSchema) : Formula → Formula
  | .and φ ψ => .and (φ.injectPins S) (ψ.injectPins S)
  | .not φ => .not (φ.injectPins S)
  | .formerly w φ => .formerly w (φ.injectPins S)
  | .previous w φ => .previous w (φ.injectPins S)
  | .since φ w ψ => .since (φ.injectPins S) w (ψ.injectPins S)
  | .pred a k args => .pred a k (args ++ (S.pinsOf a k).map fun p => (p.field, p.ref.toTerm))
  | .cmp op l r => .cmp op (l.injectPins S) (r.injectPins S)
  | .exist x φ => .exist x (φ.injectPins S)
  | .tp x => .tp x

def Temporal.Term.injectPins (S : EventSchema) : Term → Term
  | .agg a => .agg (a.injectPins S)
  | .arith op l r => .arith op (l.injectPins S) (r.injectPins S)
  | t => t

def Temporal.Aggregate.injectPins (S : EventSchema) : Aggregate → Aggregate
  | .count dom body => .count dom (body.injectPins S)
  | .sum s dom body => .sum s dom (body.injectPins S)

end

end Dogwood.Spec
