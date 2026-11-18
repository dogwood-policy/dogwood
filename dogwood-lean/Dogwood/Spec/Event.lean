import Cedar.Spec

/-!
# Events and traces

Dogwood decides over a **trace**: the sequence of events an authorizer has
ingested, in arrival order. Each event is one occurrence of an action, of a
given *kind* (`request`, `response`, …), carrying

* its **logged** record — the durable fields that temporal predicates match
  against, at any later decision point;
* its **request context** — the record the Cedar request is built from, and
  that temporal `context.*` terms and provider arguments read;
* its **request scope** — the principal and resource, present on events that
  wrap an authorization request;
* the **entity data** supplied with it — attributes and ancestors, read by
  `principal.<attr>` / `resource.<attr>` and by Cedar.

Field values are Cedar values throughout (see `REFERENCE.md`, "Relationship to the reference
implementation", "Values").
-/

namespace Dogwood.Spec

open Cedar.Spec (Attr Value Entities EntityUID)
open Cedar.Data (Map)

/-- A dotted attribute path, e.g. `input.user` is `["input", "user"]`. -/
abbrev Path := List Attr

/-- Descend `path` into the value `v`, following a record at every segment.
The empty path denotes `v` itself; a missing attribute, or a non-record met on
the way down, gives `none`. -/
def valuePath? (v : Value) : Path → Option Value
  | [] => some v
  | a :: p =>
    match v with
    | .record r => (r.find? a).bind (valuePath? · p)
    | _ => none

/-- Look up a non-empty `path` in a record. The empty path denotes no field. -/
def recordPath? (r : Map Attr Value) : Path → Option Value
  | [] => none
  | a :: p => (r.find? a).bind (valuePath? · p)

/-- One ingested event. -/
structure Event where
  /-- The action, e.g. `Drupe::Action::"Login"`. -/
  action : EntityUID
  /-- The event kind, e.g. `request` or `response`. Kinds are author-defined. -/
  kind : String
  /-- The request principal, when the event wraps an authorization request. -/
  principal : Option EntityUID
  /-- The request resource, when the event wraps an authorization request. -/
  resource : Option EntityUID
  /-- The logged temporal record: what predicates match against. -/
  logged : Map Attr Value
  /-- The request context: what the Cedar request is built from. -/
  context : Map Attr Value
  /-- The entity data supplied with the event. Its ancestor sets are assumed
  transitively closed, as in Cedar's `Entities`; the type does not enforce it. -/
  entities : Entities

/-- The resolution of an authorizer's clock: how many ticks make up one second. Timestamps
count ticks. Windows are authored in seconds, minutes, hours, or days, and compared in ticks
(`Temporal.Window.ticks`). A policy set counts in nanoseconds by default (`TickRate.nanos`). The
crate's reference interpreter instead reads the caller's timestamps as whole seconds
(`TickRate.seconds`), and the conformance harness scales its traces to the policy set's rate
(`Dogwood.Conformance.readingsOf`). A proof of an implementation that runs at another rate
relates to the specification through `Dogwood.Thm.sat_scale`. -/
structure TickRate where
  perSecond : Nat
  pos : 0 < perSecond

/-- Nanoseconds: the default rate of a policy set (`PolicySet.tickRate`). -/
def TickRate.nanos : TickRate := ⟨1000000000, by decide⟩

/-- Whole seconds: one tick per second, the unit of the crate's timestamps and of the
reference interpreter's recorded traces. -/
def TickRate.seconds : TickRate := ⟨1, by decide⟩

/-- The rate `c` times finer than `rate`: each of its ticks is a `c`-th of one of `rate`'s. -/
def TickRate.mul (rate : TickRate) (c : Nat) (hc : 0 < c) : TickRate :=
  ⟨rate.perSecond * c, Nat.mul_pos rate.pos hc⟩

/-- An event together with its timestamp, in ticks of the authorizer's clock. -/
structure TimePoint where
  ts : Int
  event : Event

/-- A trace: the ingested events, in arrival order. Position `i` is the
`i`-th event ingested (its *timepoint*). -/
abbrev Trace := List TimePoint

/-- The trace `σ` with its timestamps counted at a rate `c` times finer: every
timestamp multiplied by `c`. A condition means the same over the scaled trace
at the finer rate as over `σ` at its own (`Dogwood.Thm.sat_scale`). -/
def Trace.scale (c : Nat) (σ : Trace) : Trace := σ.map fun p => ⟨p.ts * c, p.event⟩

/-! ## Well-formed traces

The language requires the timestamps of the events an authorizer accepts to
strictly increase in arrival order (guide chapter 4, "Evaluation semantics";
guide chapter 8, "Event timestamps are assumed to be increasing"). The
specification's authorizer assigns them: it stamps each event it accepts with
its clock reading, or one tick after the last event's stamp when the reading is
not later (`Dogwood.Spec.Ingest`). So the trace of accepted events, the trace
every decision is made over, satisfies `Trace.StrictlyIncreasing` by
construction (`Dogwood.Thm.ingest_strictlyIncreasing_nil`). The crate's
reference interpreter does not stamp: it keeps the caller's timestamps and does
not check their order (guide chapter 8), so there the rule is the caller's
obligation. Timestamps are counted in ticks of the authorizer's clock (`TickRate`).

The satisfaction relation (`Temporal.Sat`) and the decision
(`PolicySet.authorize`) are defined for every trace, so that the theorems that
do not need the rule do not state it. The theorems that need it state it as a
hypothesis, or state the weaker `Trace.Nondecreasing` when that suffices. -/

/-- The timestamps of the trace strictly increase in arrival order: the
language's rule for the trace of accepted events. -/
def Trace.StrictlyIncreasing (σ : Trace) : Prop :=
  σ.Pairwise fun p q => p.ts < q.ts

/-- The timestamps of the trace never decrease in arrival order. This is
weaker than the language's rule (`Trace.StrictlyIncreasing`), and some
theorems need only this. -/
def Trace.Nondecreasing (σ : Trace) : Prop :=
  σ.Pairwise fun p q => p.ts ≤ q.ts

/-- The two request-scope roots a policy can name outside a Cedar condition. -/
inductive ScopeRoot where
  | principal
  | resource
deriving Repr, DecidableEq, Inhabited

/-- The scope entity of `e` named by `root`, if present. -/
def Event.scope (e : Event) : ScopeRoot → Option EntityUID
  | .principal => e.principal
  | .resource => e.resource

/-- An attribute path read off a scope entity, against the entity data of the
event: the supplied attribute, descending into records for the rest of the path.
`id` and `type` are attributes like any other, as in Cedar. This is the shared
resolver behind temporal `principal.<attr>` terms and provider arguments
(`EventData::resolve_entity_attr`). -/
def Event.entityAttr? (e : Event) (uid : EntityUID) : Path → Option Value
  | [] => none
  | a :: p => ((e.entities.find? uid).bind (·.attrs.find? a)).bind (valuePath? · p)

/-- A request-scope reference `principal` / `resource`, optionally followed
by an attribute path, resolved against the event `e`. A bare root denotes the
entity itself. -/
def Event.scopePath? (e : Event) (root : ScopeRoot) (path : Path) : Option Value :=
  match e.scope root, path with
  | none, _ => none
  | some uid, [] => some (.prim (.entityUID uid))
  | some uid, path => e.entityAttr? uid path

/-- A `context.<path>` reference resolved against the request context of `e`. -/
def Event.contextPath? (e : Event) (path : Path) : Option Value :=
  recordPath? e.context path

end Dogwood.Spec
